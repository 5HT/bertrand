(variables φ x y z)

(postulate
  ─────── =-refl
  (x = x)

  (x = y)
  ─────── =-symm
  (y = x)

  (x = y) (y = z)
  ─────────────── =-trans
      (x = z)

      (x = y)
  ─────────────── =-prefix-ind
  ((φ x) = (φ y))

    (x₁ = y₁) (x₂ = y₂)
  ─────────────────────── =-infix-ind
  ((x₁ φ x₂) = (y₁ φ y₂)))

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
  val (succ-def [x ≔ 0] 0-def))

(lemma
  ─────── 2-def
  (2 nat)
  val (succ-def [x ≔ 1] 1-def))

(lemma
         ─────── p
         (x = y)
  ───────────────────── =-succ
  ((succ x) = (succ y))
  val (=-prefix-ind [φ ≔ succ] p))

(postulate
     (x nat)
  ───────────── +-zero
  ((x + 0) = x)

           (x nat) (y nat)
  ───────────────────────────────── +-succ
  ((x + (succ y)) = (succ (x + y))))

(theorem
  ───────────── 1+1
  ((1 + 1) = 2)
  lem-1 (+-succ [x ≔ 1 y ≔ 0] 1-def 0-def)
  lem-2 (+-zero [x ≔ 1] 1-def)
  lem-3 (=-succ [x ≔ (1 + 0) y ≔ 1] lem-2)
  th    (=-trans [x ≔ (1 + 1) y ≔ (succ (1 + 0)) z ≔ 2] lem-1 lem-3))