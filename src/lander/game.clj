;;; Copyright (C) 2012 Christian Pohlmann
;;;
;;; Licensed under The MIT License (see LICENSE)
;;;
;;; This is a simple moon lander game to illustrate the RV DSL.
;;; Mostly simple Swing code which has been partially inspired by
;;; Stuart Halloway's snake implementation:
;;; https://github.com/stuarthalloway/programming-clojure/blob/master/examples/
;;; snake.clj

(ns lander.game
  (:use [clojure.contrib.java-utils])
  (:use [clojure.contrib.math])
  (:use clojure.contrib.import-static)
  (:use [runver.core])
  (:use [runver.ltl])
  (:gen-class))

(import
 '(java.awt Dimension Color Point GridBagConstraints GridBagLayout Insets
            BorderLayout)
 '(java.awt.event ActionListener KeyListener WindowAdapter)
 '(javax.imageio ImageIO)
 '(javax.swing JPanel JFrame Timer JLabel JOptionPane JButton)
 '(java.util Date))

(import-static java.awt.event.KeyEvent VK_UP VK_G)
(import-static java.awt.GridBagConstraints WEST EAST)

;; constants
(def interval 20)
(def gravity-force 4)
(def boost-force 10)
(def surface-height 20)
(def map-size [600 800])
(def lander-wo-gear (ImageIO/read
                     (as-file "src/lander/img/lander_wo_gear.png")))
(def lander-w-gear (ImageIO/read (as-file "src/lander/img/lander_w_gear.png")))

(defn create-lander [map-size]
  (let [position [0 0]]
    (ref {:position  position
          :direction [0 0]
          :image     lander-wo-gear
          :map-size  map-size})))

;; global variables to allow top-level LTL spec
;; in a real application these variables could be captured in a closure
(def gear-extended (ref false))
(def lander (create-lander map-size))

(defn translate-pos [[x y]]
  [x (- (second map-size) surface-height y (.getHeight (lander :image)))])

(defn add-2d [[x y] [dx dy]]
  [(+ x dx) (+ y dy)])

(defn sub-2d [[x y] [dx dy]]
  [(- x dx) (- y dy)])

(defn panel-painter []
  (let [bg-color (Color. 0 0 0)
        surface-color (Color. 140 140 140)]
    (fn [g lander]
      (let [size (lander :map-size)
            [x y] (translate-pos (lander :position))]
        (.setColor g bg-color)
        (dosync
         (doto g
           (.fillRect 0 0 (first size) (second size))
           (.setColor surface-color)
           (.fillRect  0 (- (second size) surface-height)
                       (first size) surface-height)))
        (.drawImage g (lander :image) x y (.getWidth (lander :image))
                    (.getHeight (lander :image)) nil)))))

(defn on-surface? [lander]
  (<= (second (@lander :position)) 0))

(defn update-velocity [lander boost-time]
  (let [dy (- (/ boost-force (/ 1000 (if (zero? boost-time) 1 boost-time))))]
    (dosync
     (alter lander assoc :direction (add-2d (lander :direction) [0 dy])))))

(defn game-start [lander timer gui]
  (dosync
   (alter lander assoc :direction [0 0])
   (alter lander assoc :position
          [(- (/ (first map-size) 2)
              (/ (.getWidth lander-wo-gear) 2))
           700])
   (alter lander assoc :image lander-wo-gear)
   (ref-set gear-extended false)
   (if (not (.isRunning timer))
     (.start timer))
   (.requestFocus (:lander-panel gui))
   (doto (:status-bar gui)
     (.setForeground (Color. 0 0 0))
     (.setText "Landing..."))

   (init-rv)

   (register-event p :guard @gear-extended)
   (register-event q :guard (< (second (:position @lander)) 300))
   (verify (G (p -> G q)) :invalid (JOptionPane/showMessageDialog
                                   nil "Formula violated"))))

(defn game-ended [lander timer gui]
  (cond (> (* (/ 1000 interval) (second (:direction @lander))) 75)
        (doto (:status-bar gui)
          (.setForeground (Color. 255 0 0))
          (.setText "Lander crashed: Velocity too high."))

        (not @gear-extended)
        (doto (:status-bar gui)
          (.setForeground (Color. 255 0 0))
          (.setText "Lander crashed: Landing gear not extended."))

        :else
        (doto (:status-bar gui)
          (.setForeground (Color. 0 128 0))
          (.setText "Lander successfully landed.")))

  ((:inf-panel gui) 'set-h 0)
   (let [[x y] (lander :position)]
     (dosync
      (alter lander assoc :direction [0 0])
      (alter lander assoc :position [x 0])))
   (.stop timer))

(defn make-lander-panel [size lander timer gui]
  (let [paint-panel (panel-painter)
        dimension (Dimension. (first size) (second size))
        boost-start (ref 0)
        lander-height (.getHeight (:image @lander))]
    (proxy [JPanel ActionListener KeyListener] []
      (paintComponent [g]
        (paint-panel g lander))
      (getPreferredSize []
        dimension)
      (actionPerformed [e]
        (let [dy (/ gravity-force (/ 1000 interval))]
          (dosync
           (alter lander assoc :direction (add-2d (lander :direction) [0 dy]))
           (alter lander assoc :position (sub-2d (lander :position)
                                                 (lander :direction)))
           (when (> @boost-start 0)
             (update-velocity lander interval)))
          ((:inf-panel gui) 'set-v (* (/ 1000 interval)
                                      (second (lander :direction))))
          ((:inf-panel gui) 'set-h (second (lander :position)))
          (when (on-surface? lander)
            (game-ended lander timer gui)))
        (.repaint this))
      (keyPressed [e]
        (cond (= (.getKeyCode e) VK_UP)
              (dosync (ref-set boost-start (.getTime (Date.))))))
      (keyReleased [e]
        (cond (and (= (.getKeyCode e) VK_UP) (> @boost-start 0))
              (dosync (ref-set boost-start 0))

              (= (.getKeyCode e) VK_G)
              (let [h1 (.getHeight lander-wo-gear)
                    h2 (.getHeight lander-w-gear)]
                (if @gear-extended
                  (dosync (alter lander assoc :image lander-wo-gear)
                          (ref-set gear-extended false)
                          (alter lander assoc
                                 :position (add-2d (lander :position)
                                                   [0 (- h2 h1)])))
                  (dosync (alter lander assoc :image lander-w-gear)
                          (ref-set gear-extended true)
                          (alter lander assoc
                                 :position (sub-2d (lander :position)
                                                   [0 (- h2 h1)])))))))
      (keyTyped [e]) ; ignore
      )))

(defn make-info-panel [lander timer status-bar]
  (let [gbc (GridBagConstraints.)
        l-velo (JLabel. (str 0))
        l-height (JLabel. (str 0))
        reset (JButton. "Reset")
        panel (JPanel. (GridBagLayout.))
        lander-panel (atom nil)]
    (.addActionListener reset
                        (proxy [ActionListener] []
                          (actionPerformed [evt]
                            (game-start lander timer {:lander-panel
                                                      @lander-panel
                                                      :status-bar
                                                      status-bar}))))
    (set! (. gbc gridx) 0)
    (set! (. gbc gridy) 0)
    (set! (. gbc gridwidth) 1)
    (set! (. gbc gridheight) 1)
    (set! (. gbc anchor) WEST)
    (set! (. gbc insets) (Insets. 0 0 0 20))
    (.add panel (JLabel. "Velocity") gbc)
    (set! (. gbc gridx) 1)
    (set! (. gbc anchor) EAST)
    (.setPreferredSize l-velo (Dimension. 40 15))
    (.add panel l-velo gbc)
    (set! (. gbc gridx) 0)
    (set! (. gbc gridy) 1)
    (set! (. gbc anchor) WEST)
    (.add panel (JLabel. "Height") gbc)
    (set! (. gbc gridx) 1)
    (set! (. gbc anchor) EAST)
    (.setPreferredSize l-height (Dimension. 40 15))
    (.add panel l-height gbc)
    (set! (. gbc gridx) 0)
    (set! (. gbc gridy) 2)
    (.add panel reset gbc)
    (fn [op & args]
      (cond (= op 'get-panel) panel
            (= op 'set-v) (.setText l-velo (str (round (first args))))
            (= op 'set-h) (.setText l-height (str (round (first args))))
            (= op 'set-lander-panel) (swap! lander-panel
                                            #(identity %2)
                                            (first args))))))

(defn game []
  (let [frame (JFrame. "Moon lander")
        timer (Timer. interval nil)
        status-bar (JLabel. "Landing...")
        info-panel-fn (make-info-panel lander timer status-bar)
        info-panel (info-panel-fn 'get-panel)
        lander-panel (make-lander-panel map-size lander timer
                                        {:inf-panel info-panel-fn
                                         :status-bar status-bar})
        panel (JPanel.)]
    (info-panel-fn 'set-lander-panel lander-panel)
    (.addActionListener timer lander-panel)
    (.. frame (getContentPane) (add status-bar BorderLayout/SOUTH))
    
    ;; (doto frame (.addWindowListener
    ;;              (proxy [WindowAdapter] []
    ;;                (windowClosing [e]
    ;;                  (System/exit 0)))))
    (doto lander-panel
      (.setFocusable true)
      (.addKeyListener lander-panel))
    (doto panel
      (.add lander-panel)
      (.add info-panel))
    (doto frame
      (.add panel)
      (.pack)
      (.setLocationRelativeTo (. frame getRootPane))
      (.setVisible true))
    (game-start lander timer {:lander-panel lander-panel
                              :status-bar status-bar})))

(defn -main [& args]
  (game))
