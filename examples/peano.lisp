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
  ((x₁ φ x₂) = (x₂ φ y₂)))

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
  (succ-def [x ≔ 1] 1-def)

         ─────── p
         (x = y)
  ───────────────────── =-succ
  ((succ x) = (succ y))
  (=-prefix-ind [φ ≔ succ] p))

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
  (=-trans [x ≔ (1 + 1) y ≔ (succ (1 + 0)) z ≔ 2]
    (+-succ [x ≔ (succ 0) y ≔ 0] 1-def 0-def)
    (=-succ [x ≔ (1 + 0) y ≔ 1] (+-zero [x ≔ 1] 1-def))))