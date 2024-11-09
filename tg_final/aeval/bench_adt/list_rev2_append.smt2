(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun rev2 (Lst Lst) Lst)
(assert (forall ((a Lst)) (= (rev2 nil a) a)))
(assert (forall ((x Int) (t Lst) (a Lst)) (= (rev2 (cons x t) a) (rev2 t (cons x a)))))

; extra lemma
(assert (forall ((x Lst) (y Lst) (z Lst)) (= (append (append x y) z) (append x (append y z)))))

(assert (not (forall ((x Lst) (a Lst)) (= (rev2 x a) (append (rev2 x nil) a)))))
(check-sat)
