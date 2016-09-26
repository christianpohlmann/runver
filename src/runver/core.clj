;;; Copyright (C) 2012 Christian Pohlmann
;;;
;;; Licensed under The MIT License (see LICENSE)

(ns runver.core
  (:use [runver.ltl]
        [runver.util]
        [clojure.set :only (union difference)]
        [clojure.contrib.pprint :only (pprint)]))

(def RV-ACTIVE true)

(declare trace)

(declare *main-monitor*)

;;; A logic is required to support the values top and bot
;;; (for validation and violation)
(def *logics* {'ltl3 {top :valid
                      bot :invalid
                      ? :inconclusive}
               'ltl4 {top :valid
                      bot :invalid
                      p_top :possibly-valid
                      p_bot :possibly-invalid}})

(defstruct property :logic :mon :handlers)

;;; The following closure comprises the main monitor. It is similar to the
;;; "monitor service" found in the work of Klaus Havelund.
;;; It's basically a closure which holds all observed reference objects
;;; (atoms, refs etc.), all registered events (currently guards and function
;;; calls are supported) and all evaluators for LTL formulae
(defn main-monitor []
  (let [refs-to-guards (atom {})
        traced-functions (atom #{})
        events (atom {:guard {} :funcall {} :funreturn {}})
        ;; Set of correctness properties. Each element consists of a
        ;; LTL evaluator and handlers for violation, validation and
        ;; inconclusive events (which are all optional)
        properties (ref #{})
        current-events (atom #{})]
    (letfn [(evaluate-ltl []
              (let [d-props
                    (loop [props @properties
                           ;; properties that will be deleted because they have
                           ;; been {viol,valid}ated
                           d-props #{}]
                      (if (empty? props)
                        d-props
                        (let [prop (first props)
                              {value :value formula :formula}
                              (apply (:mon prop) @current-events)]
                          (if (or (= value top) (= value bot))
                            (let [handler-type ((*logics* (:logic prop)) value)]
                              (apply (handler-type (:handlers prop)) []) ;; execute handler
                              (recur (rest props) (conj d-props prop)))

                            (let [handler-type ((*logics* (:logic prop)) value)]
                                (apply (handler-type (:handlers prop)) []) ;; execute handler
                                (recur (rest props) d-props))))))]
                (alter properties difference d-props)))

            (events-on [name-set]
              (swap! current-events union name-set)
              (dosync (evaluate-ltl)))

            ;; in case an event is no longer active, the ltl specifications
            ;; are not re-evaluated
            (events-off [name-set]
              (swap! current-events difference name-set))

            (ref-changed
              [key ref old new]
              (let [guards (@refs-to-guards ref)]
                (let [[on-name-set off-name-set]
                      (loop [guards guards
                             acc-on #{}
                             acc-off #{}]
                        (if (empty? guards) [acc-on acc-off]
                            (let [evt-name ((:guard @events) (first guards))]
                              (if ((first guards))
                                (recur (rest guards)
                                       (conj acc-on evt-name)
                                       acc-off)
                                (recur (rest guards)
                                       acc-on
                                       (conj acc-off evt-name))))))]
                  (events-on on-name-set)
                  (events-off off-name-set))))

            (fun-called [name params]
              (let [tmp-events ((:funcall @events) name)]
                (when tmp-events
                  (let [name-set
                        ;; several events could be triggered at the same time
                        ;; in case predicates "overlap"
                        (loop [tmp-events tmp-events
                               acc #{}]
                          (let [{evt-name :name pred :pred} (first tmp-events)]
                            (if (empty? tmp-events) acc
                                (if (pred params)
                                  (recur (rest tmp-events) (conj acc evt-name))
                                  (recur (rest tmp-events) acc)))))]
                    (events-on name-set)
                      ;; unlike condition events (specified by guards),
                      ;; function events are "momentary" events. Therefore, the
                      ;; function event is turned off immediately after the
                      ;; evaluation of corresponding correctness properties has
                      ;; been triggered (cf. fun-returned)
                    (events-off name-set)))))

            (fun-returned [name value]
              (let [tmp-events ((:funreturn @events) name)]
                (when tmp-events
                  (doseq [{evt-name :name pred :pred} tmp-events]
                    (when (pred value)
                      ;; TODO: Several events could be on at the same time
                      ;; (if predicates "overlap"). This is not supported yet.
                      ;; This has already been fixed for fun-called.
                      (events-on evt-name)
                      (events-off evt-name))))))

            (verify [formula logic handlers]
              ;; fns maps monitor results (eg. top, bot, ? for LTL3 and
              ;; top, bot, p_top, p_bot for LTL4) to functions that are
              ;; called when the monitor mon assumes the corresponding
              ;; value. Consistency (with the specified logic) is checked
              ;; upon executing the verify macro.
              (let [mon (ltl-evaluator formula logic)]
                (dosync
                 (alter properties conj (struct property logic mon handlers)))))

            (register-guard
              [evt-name guard refs]
              (doseq [r refs]
                (if-not (@refs-to-guards r)
                  (do
                    (add-watch r nil ref-changed) ; no key argument needed
                    (swap! refs-to-guards assoc r #{guard}))
                  (swap! refs-to-guards assoc r (conj (@refs-to-guards r)
                                                      guard))))
              (swap! events assoc :guard (assoc (:guard @events) guard evt-name)))

            ;; evt-type is one of :funcall or :funreturn
            (register-func [evt-name evt-type function-name pred]
              (let [old-function (var-get (resolve function-name))]
                (when-not (@traced-functions function-name)
                  ;; Thanks to André Thieme who came up with the idea of
                  ;; redefining the function that's supposed to be traced.
                  (intern *ns* function-name
                          (fn [& params]
                            (*main-monitor* 'fun-called function-name params)
                            (let [value (apply old-function params)]
                              (*main-monitor* 'fun-returned function-name
                                              value)
                              value)))
                  (swap! traced-functions conj function-name))
                (let [curr (@events evt-type)]
                  (if-not ((@events evt-type) function-name)
                    (swap! events assoc evt-type (assoc curr function-name
                                                        #{{:name evt-name
                                                           :pred pred}}))
                    (swap! events assoc evt-type (assoc curr function-name
                                                        (conj (curr function-name)
                                                              {:name evt-name
                                                               :pred
                                                               pred})))))))]

      (fn [op & params]
        (cond (= op 'register-guard)
              (apply register-guard params)
              
              (= op 'register-func)
              (apply register-func params)

              (= op 'verify)
              (apply verify params)

              (= op 'fun-called)
              (apply fun-called params)

              (= op 'fun-returned)
              (apply fun-returned params)

              :else
              (throw (Exception.
                      (format "Function not supported or private: %s" op))))))))

(defn init-rv []
  (def *main-monitor* (main-monitor)))

(defmacro is-deref?
  "Checks if the passed sexpr is a dereferencing operation (i.e. something
   like @foobar)"
  [obj]
  `(and (coll? ~obj) (= (first (macroexpand-1 ~obj)) 'clojure.core/deref)))

;;; check if this function can be put in some letfn-form
(defn find-refs
  "Returns a hash set of all ref/atom/agent-references in the given
   s-expression. This function is only used by add-condition to find
   references that must be monitored."
  [sexpr]
  (letfn [(fr-aux [sexpr]
            (cond (is-deref? sexpr) (list (second sexpr))

                  (empty? sexpr) '()

                  (and (coll? (first sexpr)) (is-deref? (first sexpr)))
                  (cons (second (first sexpr)) (fr-aux (rest sexpr)))

                  (coll? (first sexpr))
                  (cons (fr-aux (first sexpr)) (fr-aux (rest sexpr)))

                  :else
                  (fr-aux (rest sexpr))))]
    ;; converts a (deeply) nested list into linear order and then converts
    ;; it into a set to remove duplicates -- not very elegant, but I didn't
    ;; find an idiomatic way to solve this
    (into #{} (flatten (fr-aux sexpr)))))

(defmacro register-event [evt-name evt-type & params]
  (cond (= evt-type :guard)
        ;; (first params) represents the actual code of the guard
        ;; it is wrapped inside a fn (lambda abstraction) to suppress
        ;; evaluation
        `(*main-monitor* '~'register-guard '~evt-name (fn [] ~(first params))
                         ~(find-refs (first params)))

        (or (= evt-type :funcall) (= evt-type :funreturn))
        `(*main-monitor* '~'register-func '~evt-name ~evt-type
                         '~(first params) ; name of the function
                         ~(if (second params) ; predicate on parameter list
                            ;; to make writing predicates as comfortable as
                            ;; possible. The macro abstracts away the fn [x] ..
                            ;; syntax and binds the parameters (return value)
                            ;; of the traced function to the variable *params*
                            `(fn [~'*params*] ; deliberate leak
                               ~(second params))
                            `(fn [x#] true)))

        :else
        `(throw (Exception. (format "Unknown event type: %s" ~evt-type)))))

(defmacro verify [formula & options]
  (let [opts (apply hash-map options)
        handlers (dissoc opts :logic)
        logic (if (:logic opts) (:logic opts) 'ltl3)]
    ;; consistency check of specified logic and handlers
    (doseq [[k v] handlers]
      (when (not (some #{k} (vals (*logics* logic))))
        (throw (Exception.
                (format "Handler type %s not supported by chosen logic %s"
                        k logic)))))

    `(*main-monitor* '~'verify '~formula '~logic
                     ~(into {}
                            (for [[k v] (*logics* logic)]
                              [v
                               `(fn []
                                  ~(if (handlers v)
                                     (handlers v)
                                     k))])))))

;;; Note that no comparison involving RV-ACTIVE is performed when defm is
;;; invoked. RV-ACTIVE is only evaluated once at compile-time.
(defmacro defm [fname & args]
  (let [new `(rv-service :new '~fname)
        def `(defn ~fname ~@args)]
    (if RV-ACTIVE `(do ~new ~def) def)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Event declarations                                                    ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct event :type :value)

(defmacro defevent [evt-type value]
  `(event evt-type ~(if (= evt-type :guard) ; credit to Susan Mielke
                        `(fn [] ~value)
                        value)))
