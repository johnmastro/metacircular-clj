(ns metacircular.core-test
  (:refer-clojure :exclude [eval apply load-file extend])
  (:require [clojure.core :as clj]
            [clojure.test :refer :all]
            [metacircular.core :refer :all]))

;; TODO: Look into using simple-check

(deftest test-special-forms
  (testing "if"
    (are [form] (= (eval form) (clj/eval form))
         ;; We require three args to if
         '(if true :then :else)
         '(if false :then :else)))
  (testing "quote"
    (are [form] (= (eval form) (clj/eval form))
         '(quote)
         '(quote 1)
         '(quote one)
         '(quote (one two))
         '(quote [one 2 :three "four"])
         '(quote yes no)))
  (testing "fn"
    (are [form x] (= (eval form) x)
         '((fn []))                            nil
         '((fn [] :foo))                       :foo
         '((fn [n] (inc n)) 1)                 2
         '((fn [n m] (+ n m)) 1 2)             3
         '((fn [n & more] (count more)) 1 2 3) 2
         )
    (is (procedure? (eval '(let [foo nil] ((fn foo [] foo)))))))
  ;; (testing "def"
  ;;   (are [form] (= (eval form) (clj/eval form))
  ;;        '(do (def one 1)
  ;;             one)
  ;;        '(do (def one 1)
  ;;             (def one :one)
  ;;             one)))
  (testing "set!"
    (are [form x] (= (eval form) x)
         '(let [n 1] (set! n 2) n)              2
         '(let [n 1] (let [n 2] (set! n 3)) n)  1
         )))

(deftest test-core-macros
  (testing "do"
    (are [form] (= (eval form) (clj/eval form))
         '(do)
         '(do 1)
         '(do 1 2 :three)
         '(do 1 2 :three (let [four 4] four))))
  (testing "and"
    (are [form] (= (eval form) (clj/eval form))
         '(and)
         '(and nil)
         '(and false)
         '(and true nil)
         '(and false true)
         '(and 1 'one :one "one")
         '(and 1 'one :one "one" false)))
  (testing "or"
    (are [form] (= (eval form) (clj/eval form))
         '(or)
         '(or nil)
         '(or false)
         '(or true)
         '(or true nil)
         '(or false nil [])
         '(or nil false ())))
  (testing "let"
    (are [form] (= (eval form) (clj/eval form))
         '(let [])
         '(let [] :foo)
         '(let [n 1] n)
         '(let [n 1 m 2] (+ n m))
         '(let [add1 (fn [n] (+ n 1))
                sub1 (fn [n] (- n 1))]
            (add1 (sub1 1)))
         '(let [n 1 m 2]
            (let [n 2]
              (+ n m)))
         '(let [n 1 m 2]
            (let [n 2] :noop)
            (+ n m))
         '(let [n 1
                add1 (fn [m] (+ n m))]
            (add1 1))
         '(let [add1
                (let [n 1]
                  (fn [m] (+ n m)))]
            (add1 1))))
  (testing "cond"
    (are [form] (= (eval form) (clj/eval form))
         '(cond)
         '(cond true :then)
         '(cond false :then)
         '(cond nil :nope :else :then)
         '(cond false :nope nil :nope)
         '(cond nil :nope false :nope () :then)))
  (testing "if-let and when-let"
    (are [form] (= (eval form) (clj/eval form))
         '(if-let [x true]
            (str "x is " x)
            :nope)
         '(if-let [x false]
            (str "x is " x)
            :nope)
         '(when-let [n 1]
            (inc n))
         '(when-let [n nil]
            (inc n))))
  (testing "if-not and when-not"
    (are [form] (= (eval form) (clj/eval form))
         '(if-not (+ 1 2)
            :true
            :false)
         '(if-not (or nil nil)
            :true
            :false)
         '(when-not ()
            :foo)
         '(when-not false
            :bar)))
  (testing "condp"
    (are [form] (= (eval form) (clj/eval form))
         '(condp = :obj :default)
         '(condp = (dec 4)
            1 :one
            2 :two
            3 :three)
         '(condp < (inc 41)
            60 :sixty
            50 :fifty
            40 :forty)
         '(condp > 42
            10 :ten
            20 :twenty
            :default))))

(deftest test-destructuring
  (testing "vector destucturing"
    (are [form] (= (eval form) (clj/eval form))
         '(let [[a b] [1 2]] (+ a b))

         '(let [[x y :as z] [1 2 3]]
            {:x x :y y :z z})

         '(let [[[i x] [[n] :as q] & more] [[1 2] [[3]] 4 5]]
            {:i i :x x :n n :q q :more more})

         '(when-let [[i [n m]] (seq [1 [2 3]])]
            (+ i n m))

         '(when-let [[i [n m]] (seq [])]
            (+ i n m))

         '(if-let [[x & xs] [1 2 3]]
            {:x x :xs xs}
            :nope)

         '(if-let [[x & xs :as stuff] ()]
            {:x x :xs xs :as stuff}
            :nope)

         '(if-let [[x & xs :as stuff] nil]
            {:x x :xs xs :stuff stuff}
            :nope)))
  (testing "map destucturing"
    (are [form] (= (eval form) (clj/eval form))
         '(let [{a :a b :b} {:a 1 :b 2}]
            [a b])

         '(let [{:keys [a b]} {:a 1 :b 2}]
            [a b])

         '(let [{:keys [a b] :or {b :two}} {:a 1}]
            [a b])

         '(let [{a :a :as m} {:a 1 :b 2}]
            [a m])

         '(let [[_ & {:keys [a b]}] [:ignored :a 1 :b 2]]
            [a b])

         '(let [{a :a :keys [b]} {}]
            [a b])

         '(let [{:keys [a b]} '(:a 1 :b 2)]
            [a b]))))

(deftest test-recursion
  (testing "mutal recursion"
    (is (= (eval '(letfn [(is-even? [n]
                            (if (zero? n)
                              true
                              (is-odd? (dec n))))
                          (is-odd? [n]
                            (if (zero? n)
                              false
                              (is-even? (dec n))))]
                    [(is-even? 20) (is-odd? 20)]))
           [true false])))
  (testing "tail call optimization"
    (is (true? (eval '(letfn [(is-even? [n]
                                (if (zero? n)
                                  true
                                  (is-odd? (dec n))))
                              (is-odd? [n]
                                (if (zero? n)
                                  false
                                  (is-even? (dec n))))]
                        (is-even? 1e5))))))
  (testing "self recursion"
    (is (= (eval '(let [iota (fn iota [n]
                               ((fn recur [i acc]
                                  (if (= i n)
                                    acc
                                    (recur (inc i) (conj acc i))))
                                0 []))]
                    (iota 10)))
           (vec (range 10))))))

(deftest test-higher-order-functions
  (are [form] (= (eval form) (clj/eval form))
       '(reduce + 0 [1 2 3])
       '(reduce (fn [result n] (conj result (str n)))
                []
                [1 2 3])
       '(map inc [1 2 3])
       '(map (fn [n] (+ n 1)) [1 2 3])
       '(mapcat (fn [n] (list n (str n))) [1 2 3])
       '((comp keyword str) "foo")
       '((juxt even? odd?) 42)))
