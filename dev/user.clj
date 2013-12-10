(ns user
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.pprint :refer (pprint)]
            [clojure.repl :refer :all]
            [clojure.test :as test]
            [clojure.tools.namespace.repl :refer (refresh refresh-all)]
            [metacircular.core :as c]
            [metacircular.env :as e]
            [metacircular.analyzer :as a]))

(defn run-tests
  ([] (run-tests 'metacircular.core-test))
  ([ns-sym] (test/run-tests ns-sym)))
