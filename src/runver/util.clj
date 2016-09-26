;;; Copyright (C) 2012 Christian Pohlmann
;;;
;;; Licensed under The MIT License (see LICENSE)

(ns runver.util)

(defmacro set-atom! [atom value]
  `(compare-and-set! ~atom (deref ~atom) ~value))

(defn seq-merge [l1 l2 cmp]
  (loop [l1 l1
         l2 l2
         acc '()]
    (cond (empty? l1)
          (concat (reverse acc) l2)

          (empty? l2)
          (concat (reverse acc) l1)

          :else
          (let [a (first l1)
                b (first l2)]
            (if (cmp a b)
              (recur (rest l1) l2 (conj acc a))
              (recur l1 (rest l2) (conj acc b)))))))

(defn invert-map [m]
  (into {} (for [[k v] m] [v k])))
