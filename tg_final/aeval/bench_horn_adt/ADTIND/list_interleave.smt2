(set-logic HORN)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-fun interleave (Lst Lst Lst) Bool)
(declare-fun evens (Lst Lst) Bool)
(declare-fun odds (Lst Lst) Bool)

(assert (evens nil nil))
(assert (odds nil nil))
(assert (forall ((xs Lst) (ys Lst) (x Int) (rs Lst))
  (=> (and (= xs (cons x ys)) (odds ys rs)) (evens xs (cons x rs)))))
(assert (forall ((xs Lst) (ys Lst) (x Int) (rs Lst)) 
  (=> (and (= xs (cons x ys)) (evens ys rs)) (odds xs rs))))
(assert (forall ((ys Lst) (zs Lst)) (=> (= zs nil) (interleave zs ys ys))))
(assert (forall ((xs Lst) (ys Lst) (zs Lst) (z Int) (rs Lst)) 
  (=> (and (= zs (cons z xs)) (interleave ys xs rs)) 
    (interleave zs ys (cons z rs)))))

(assert (forall ((xs Lst) (ys Lst) (zs Lst) (rs Lst))
       (=> (and (evens xs ys) (odds xs zs) (interleave ys zs rs) (not (= xs rs))) false)))
(check-sat)
