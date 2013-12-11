(ns metacircular.env
  (:refer-clojure :exclude [extend contains?])
  (:require [clojure.core :as clj]))

(defprotocol IEnv
  (def! [env sym val])
  (set! [env sym val])
  (bind [env sym val])
  (extend [env m])
  (null-locals [env])
  (contains? [env sym])
  (lookup [env sym] [env sym not-found])
  (copy [env]))

(deftype SimpleEnv [vars locals]
  IEnv
  (def! [this sym val]
    (swap! vars assoc sym val)
    this)
  (set! [this sym val]
    (if (clj/contains? @vars sym)
      (do (swap! vars assoc sym val)
          this)
      (throw (Exception. (str "Can't set an unbound global: " sym)))))
  (bind [this sym val]
    (SimpleEnv. vars (assoc locals sym val)))
  (extend [this m]
    (SimpleEnv. vars (merge locals m)))
  (null-locals [this]
    (SimpleEnv. vars {}))
  (contains? [this sym]
    (not= (lookup this sym ::not-found)
          ::not-found))
  (lookup [this sym]
    (lookup this sym ::throw))
  (lookup [this sym not-found]
    (let [x (get locals sym ::not-found)]
      (if (= x ::not-found)
        (let [x (get @vars sym ::not-found)]
          (if (= x ::not-found)
            (if (= not-found ::throw)
              (throw (Exception. (str "Unable to resolve symbol " sym)))
              not-found)
            x))
        x)))
  (copy [this]
    (SimpleEnv. (atom @vars) locals)))

(deftype Env [vars locals]
  IEnv
  (def! [this sym val]
    (swap! vars assoc sym val)
    this)
  (set! [this sym val]
    (if-let [frame (loop [locals locals]
                     (when (seq locals)
                       (let [frame (peek locals)]
                         (if (clj/contains? @frame sym)
                           frame
                           (recur (pop locals))))))]
      (do (swap! frame assoc sym val)
          this)
      (if (clj/contains? @vars sym)
        (do (swap! vars assoc sym val)
            this)
        (throw (Exception. (str "Can't set an unbound variable: " sym))))))
  (bind [this sym val]
    (Env. vars (conj locals (atom {sym val}))))
  (extend [this m]
    (Env. vars (conj locals (atom m))))
  (null-locals [this]
    (Env. vars []))
  (contains? [this sym]
    (not= (lookup this sym ::not-found)
          ::not-found))
  (lookup [this sym]
    (lookup this sym ::throw))
  (lookup [this sym not-found]
    (let [local (loop [locals locals]
                  (if (seq locals)
                    (let [frame (peek locals)
                          x (get @frame sym ::not-found)]
                      (if (= x ::not-found)
                        (recur (pop locals))
                        x))
                    ::not-found))]
      (if (= local ::not-found)
        (let [global (get @vars sym ::not-found)]
          (if (= global ::not-found)
            (if (= not-found ::throw)
              (throw (Exception. (str "Unable to resolve symbol " sym)))
              not-found)
            global))
        local)))
  (copy [this]
    (Env. (atom @vars) (mapv (comp atom deref) locals))))

(defn make-env
  "Create and return a new environment."
  ([] (make-env {}))
  ([vars] (Env. (atom vars) [])))

(defn make-simple-env
  "Create and return a new simple environment."
  ([] (make-simple-env {}))
  ([vars] (SimpleEnv. (atom vars) {})))
