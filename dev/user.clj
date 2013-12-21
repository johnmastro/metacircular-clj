(ns user
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.pprint :refer (pprint)]
            [clojure.walk :as walk]
            [clojure.repl :refer :all]
            [clojure.test :as test]
            [clojure.tools.namespace.repl :refer (refresh refresh-all)]
            [metacircular.core :as c]
            [metacircular.env :as e]
            [metacircular.analyzer :as a]))

(alter-var-root #'*print-length* (constantly 10))
(alter-var-root #'*print-level* (constantly 2))

(defn set-printing!
  ([] (set-printing! 'limit))
  ([msg]
     (case msg
       limit (set-printing! 10 2)
       relax (set-printing! nil nil)
       (throw (Exception. (str "Unknown set-printing! message " msg)))))
  ([length level]
     (set! *print-length* length)
     (set! *print-level* level)
     [length level]))

(defn run-tests
  ([] (run-tests 'metacircular.core-test))
  ([ns-sym] (test/run-tests ns-sym)))
