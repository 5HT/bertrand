(variables x y)

(postulate
  ─────── 0-def
  (0 nat)

      (x nat)
  ────────────── succ-def
  ((succ x) nat))

(define 1 (succ 0))
(define 2 (succ 1))
(define 3 (succ 2))
(define 4 (succ 3))
(define 5 (succ 4))

(lemma
  ─────── 1-def
  (1 nat)
  (succ-def [x ≔ 0] 0-def)

  ─────── 2-def
  (2 nat)
  (succ-def [x ≔ 1] 1-def))