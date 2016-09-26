;;; Copyright (C) 2012 Christian Pohlmann
;;;
;;; Licensed under The MIT License (see LICENSE)

(ns runver.ltl
  (:use [matchure :only [cond-match]])
  (:gen-class))

(def operators
  ^{:doc "Symbols representing LTL operators are mapped to their respective
          precedence."}
  { '-> 1 'or 1 'and 2 'U 3 'R 3 'WX 3 'X 3 'G 3 'F 3 'not 4})

(def arity
  { '-> 2 'or 2 'and 2 'U 2 'R 2 'WX 1 'X 1 'G 1 'F 1 'not 1})

(defn is-operator? [x]
  (some #{x} (keys operators)))

(def is-operand? (comp not is-operator?))

(def precedence operators)

(defn infix-to-postfix
  "Converts an LTL expression given in usual infix syntax to postfix syntax
   (RPN). This function implements Dijkstra's shunting-yard algorithm."
  [expr]
  (loop [expr expr
         stack []
         out []]
    (cond (not (coll? expr))
          expr

          (empty? expr)
          (concat out (reverse stack))

          (coll? (first expr))
          (recur (rest expr) stack (concat out (infix-to-postfix
                                                (first expr))))

          (is-operand? (first expr))
          (recur (rest expr) stack (conj out (first expr)))

          (empty? stack)
          (recur (rest expr) (conj stack (first expr)) out)

          (> (precedence (peek stack)) (precedence (first expr)))
          (recur expr (pop stack) (conj out (peek stack)))

          :else
          (recur (rest expr) (conj stack (first expr)) out))))

(defn peek-n
  "Returns the first n items from the given stack."
  [stack n]
  (loop [n n
         vals []
         stack stack]
    (if (= n 0) (reverse vals)
        (recur (dec n) (conj vals (peek stack)) (pop stack)))))

(defn pop-n
  "Returns the given stack with the first n items removed."
  [stack n]
  (loop [n n
         stack stack]
    (if (= n 0) stack
        (recur (dec n) (pop stack)))))

(defn postfix-to-prefix
  "Converts an LTL expression given in RPN into prefix notation by performing
   a 'pseudo evaluation'."
  [expr]
  (loop [expr expr
         stack []]
    (cond (not (coll? expr))
          expr

          (empty? expr)
          (peek stack)

          (is-operator? (first expr))
          (recur (rest expr)
                 (conj (pop-n stack (arity (first expr)))
                       (conj (peek-n stack (arity (first expr)))
                             (first expr))))

          :else
          (recur (rest expr) (conj stack (first expr))))))

(def infix-to-prefix (comp postfix-to-prefix infix-to-postfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Defining the LTL truth domain, i.e. constants, order (which is        ;;;;
;;;; linear), meet/join operations and the dual elements                   ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def top 'top)
(def bot 'bot)

(def ? '?) ;; LTL3-specific value

(def p_top 'p_top) ;; LTL4-specific value
(def p_bot 'p_bot) ;; LTL4-specific value

(defn ltl-boolean? [x]
  (some #{x} [bot top ? p_top p_bot]))

(defn final-value?
  "Returns true if the given argument is a final value. A final value
   is either top or bottom."
  [x]
  (or (= x top) (= x bot)))

(let [ltl3-order { top 3 ? 2 bot 1 }
      ltl4-order { top 3 p_top 2 p_bot 2 bot 1 }]
  (defn ltl-meet [arg1 arg2 env]
    (if (= (:logic env) 'ltl3)
      (min-key ltl3-order arg1 arg2) ; ltl3
      (if (or (= [arg1 arg2] [p_top p_bot]) ; ltl4
              (= [arg1 arg2] [p_bot p_top]))
        bot
        (min-key ltl4-order arg1 arg2))))

  (defn ltl-join [arg1 arg2 env]
    (if (= (:logic env) 'ltl3)
      (min-key ltl3-order arg1 arg2)
      (if (or (= [arg1 arg2] [p_top p_bot])
              (= [arg1 arg2] [p_bot p_top]))
        top
        (max-key ltl4-order arg1 arg2)))))

(def ltl-dual {top bot
               bot top
               ? ?
               p_top p_bot
               p_bot p_top})

(defn simplify
  "Simplifies a given LTL formula according to some rules."
  ;;; TODO: Use syntax-quote instead of manual calls to list etc.
  [phi]
  (letfn [(simplify-once [phi]
            (if (not (coll? phi))
              phi
              (let [[fst phi1 phi2] phi]
                (cond (= fst 'and)
                      (cond
                       ;; rule: A1
                       (= phi1 bot) bot
                       ;; rule: A2
                       (= phi2 bot) bot
                       ;; rule: A3
                       (= phi1 top) (recur phi2)
                       ;; rule: A4
                       (= phi2 top) (recur phi1)
                       ;; rule A5
                       :else
                       (list 'and
                             (simplify-once phi1)
                             (simplify-once phi2)))

                      (= fst 'or)
                      (cond
                       ;; rule: O1
                       (= phi1 bot) (recur phi2)
                       ;; rule: O2
                       (= phi2 bot) (recur phi1)
                       ;; rule: O3
                       (= phi1 top) top
                       ;; rule: O4
                       (= phi2 top) top
                       ;; rule O5
                       :else
                       (list 'or
                             (simplify-once phi1)
                             (simplify-once phi2)))

                      (= fst 'not)
                      (cond
                       ;; rule: N1
                       (= phi1 top) bot
                       ;; rule: N2
                       (= phi1 bot) top
                       ;; rules: N3, N4
                       (and (coll? phi1) (or (= (first phi1) 'and)
                                             (= (first phi1) 'or)))
                       (let [[op psi1 psi2] phi1]
                         (simplify-once
                          (list ({'or 'and 'and 'or} op)
                                (list 'not (simplify-once psi1))
                                (list 'not (simplify-once psi2)))))

                       ;; rule: N5
                       (and (coll? phi1) (= (first phi1) 'not))
                       (recur (second phi1))
                       ;; rule: N6
                       :else
                       (list 'not (simplify-once phi1)))

                      ;; rule: U1
                      (= fst 'U)
                      (list 'U
                            (simplify-once phi1)
                            (simplify-once phi2))

                      :else
                      phi))))]
    ;; There are formulae which cannot be fully simplified in a single
    ;; iteration using the above rules (e.g. (and (not bot) phi1) will
    ;; result in (and top phi1)). Therefore simplify-once is applied
    ;; iteratively until the formula doesn't change in one iteration
    ;; (i.e. can't be simplified further)
    (loop [prev-formula phi]
      (let [simp-formula (simplify-once prev-formula)]
        (if (not= prev-formula simp-formula)
          (recur simp-formula)
          simp-formula)))))

(defstruct monitor-result :value :formula)

(defmacro result [value formula]
  `(struct monitor-result ~value ~formula))

(defn simplify-result
  "Simplifies the formula of a result object and returns the updated
   rseult, i.e. leaving the value field unchanged."
  [{value :value formula :formula}]
  (struct monitor-result value (simplify formula)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; LTL evaluation functions                                              ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; All evaluation functions have an env-parameter which is currently only
;;; used to signal whether LTL3 or LTL4 is used, but it could be used for
;;; other options as well.
(declare ltl-eval)

(defn ltl-ap [input ap]
  (if (some #{ap} input) (result top top) (result bot bot)))

(defn ltl-not [input phi env]
  (let [ev-phi (ltl-eval input phi env)]
    (result (ltl-dual (:value ev-phi))
            `(~'not ~(:formula ev-phi)))))

(defn ltl-next [input phi env]
  (if (= (:logic env) 'ltl4)
    (result p_bot phi) ; ltl4
    (result ? phi))) ; ltl3

(defn ltl-weaknext [input phi env]
  (ltl-eval input `(~'not (~'X (~'not ~phi))) env))
;;  (if (= (:logic env) 'ltl4)
;;    (result p_top phi) ; ltl4
;;    (result ? phi))) ; ltl3

(defn ltl-until [input phi1 phi2 env]
  (let [new-formula `(~'or ~phi2 (~'and ~phi1 (~'X (~'U ~phi1 ~phi2))))]
    (ltl-eval input new-formula env)))

(defn ltl-release [input phi1 phi2 env]
  (ltl-eval input `(~'not (~'U (~'not ~phi1) (~'not ~phi2))) env))

(defn ltl-globally [input phi env]
  (ltl-eval input `(~'R ~bot ~phi) env))

(defn ltl-finally [input phi env]
  (ltl-eval input `(~'U ~top ~phi) env))

(defn ltl-and [input phi1 phi2 env]
  (let [ev-phi1 (ltl-eval input phi1 env)]
    (if (= (:value ev-phi1) top)
      (ltl-eval input phi2 env)
      (let [ev-phi2 (ltl-eval input phi2 env)
            meet (ltl-meet (:value ev-phi1) (:value ev-phi2) env)]
        (cond (final-value? meet) (result meet meet)
              :else (result meet (list 'and (:formula ev-phi1)
                                       (:formula ev-phi2))))))))

;; in order to improve performance it might be better to implement
;; ltl-or and ltl-impl independently and not in terms of other functions
(defn ltl-or [input phi1 phi2 env]
  (ltl-eval input `(~'not (~'and (~'not ~phi1) (~'not ~phi2))) env))

(defn ltl-impl [input phi1 phi2 env]
  (ltl-eval input `(~'or (~'not ~phi1) ~phi2) env))

(defn ltl-boolean [input val]
  (result val val))

(defn ltl-evaluator
  "Online-evaluation of infinite traces *without* automata. This function
   returns a closure acting as monitor which can be called with the
   continuation of the trace (which may be non-finite). When the given
   formula can be fully evaluated, either top or bot is returned, otherwise
   ? is returned (i.e. in cases like p and X phi)."
  [formula logic]
  (let [formula (atom (infix-to-prefix formula))]
    (fn [& input]
      (let [res (ltl-eval input @formula {:logic logic})
            s-res (simplify-result res)] ; simplified result
        (compare-and-set! formula @formula (:formula s-res))
        s-res))))

(defn ltl-eval [input phi env]
  (cond (coll? phi)
        (let [[op phi1 phi2] phi]
          (cond (= op 'and) (ltl-and input phi1 phi2 env)
                (= op' or) (ltl-or input phi1 phi2 env)
                (= op '->) (ltl-impl input phi1 phi2 env)
                (= op 'not) (ltl-not input phi1 env)
                (= op 'WX) (ltl-weaknext input phi1 env)
                (= op 'X) (ltl-next input phi1 env)
                (= op 'U) (ltl-until input phi1 phi2 env)
                (= op 'R) (ltl-release input phi1 phi2 env)
                (= op 'G) (ltl-globally input phi1 env)
                (= op 'F) (ltl-finally input phi1 env)
                :else_ (throw (Exception.
                               (format "Unsupported operation: %s"
                                       (first phi))))))

        (ltl-boolean? phi)
        (ltl-boolean input phi)

        :else
        (ltl-ap input phi)))
