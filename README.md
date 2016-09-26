# runver

_runver_ is a DSL for runtime verification implemented in
Clojure. Monitors are represented as formula-rewriting closures. No
transformation of LTL formulae into automata is needed.  LTL3 and LTL4 are
supported.

## Usage
It is sufficient to install [leiningen](http://leiningen.org/) to run the following examples.

### Simple example
In `src/runver/test.clj` the following properties are defined:

```(register-event any-rest :funcall rest)

(register-event safe-rest :funcall rest
                (not (empty? (first *params*))))
```

Now it can be specified that each call to `rest` should be a safe call:

```(verify (G (any-rest -> safe-rest))
        :logic ltl3
        :valid (println "LTL verified.")
        :invalid (println "LTL violated."))
```

In order to try it out yourself, just type `lein repl` from the root
directory of the project followed by these expressions:

```(load-file "src/runver/test.clj")
(in-ns 'runver.test)
(rest [1 2 3])
(rest [])
```

The last call to rest will violate the LTL3 formula defined in `test.clj`


### More complex example
`runver` comes with a lunar lander game. The movements of the lander unit is observed by an LTL formula:

```(register-event p :guard @gear-extended)
   (register-event q :guard (< (second (:position @lander)) 300))
   (verify (G (p -> G q)) :invalid (JOptionPane/showMessageDialog
                                   nil "Formula violated"))))
```

Event `p` is fired when the `y`-position of the lander is
below 300. Event `q` is fired when the landing gear is extended. The
given formula `G (q -> G p)` therefore validates that the landing gear
is never extended before the altitude is below 300.

In order to run this example, uncomment line 10 (`;; :main
lander.game`) and then build a standalone jar by typing the following
command from the project's root directory: `lein uberjar`
The game can then be run via `java -jar target/runver-1.0.0-SNAPSHOT-standalone.jar`
The landing gear is extended by pressing `g`.


## Todo
* Convert to Clojure 1.8
* Load lander images from jar
