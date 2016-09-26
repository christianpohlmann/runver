;;; Copyright (C) 2012 Christian Pohlmann
;;;
;;; Licensed under The MIT License (see LICENSE)

(ns runver.test
  (:use [runver.core]
        [runver.ltl]
        [runver.util :only [set-atom!]]))
;;        [clojure.contrib.pprint :only (pprint)]))
        
(init-rv)
    
;; A simple example using LTL3
;; Define two events:
;;   1. any-rest refers to any application of rest
;;   2. safe-rest only refers to those applications of rest for which the seq given to rest is non-empty
;; Define a LTL formula requiring that any-rest implies safe-rest

(register-event any-rest :funcall rest)

(register-event safe-rest :funcall rest
                (not (empty? (first *params*))))

(verify (G (any-rest -> safe-rest))
        :logic ltl3
        :valid (println "LTL verified.")
        :invalid (println "LTL violated."))

