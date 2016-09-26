(defproject runver "1.0.0-SNAPSHOT"
  :description "A Clojure DSL for runtime verification."
  :dependencies [[org.clojure/clojure "1.2.1"]
                 [org.clojure/clojure-contrib "1.2.0"]
                 [matchure "0.10.1"]]
;; in order to build the lander game, uncomment line 10
;; then build with "lein uberjar" and run the jar from the project's root directory: java -jar target/runver-1.0.0-SNAPSHOT-standalone.jar
;;  :main lander.game
  :source-path "src"
)
