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
  succ-def 0-def)

(lemma
  ─────── 2-def
  (2 nat)
  succ-def 1-def)

(lemma
         ─────── p
         (x = y)
  ───────────────────── =-succ
  ((succ x) = (succ y))
  =-prefix-ind p)

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
  =-trans
    +-succ 1-def 0-def
    =-succ +-zero 1-def)