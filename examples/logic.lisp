(infix → 25)

(variables α β γ δ φ x a b c)

(bound (∀ x _))

(define (∃ x φ) (¬ (∀ x (¬ φ))))
(define (α ∧ β) (¬ (α → (¬ β))))
(define (α ∨ β) ((¬ α) → β))
(define (α ↔ β) ((α → β) ∧ (β → α)))

(define (¬¬ α) (¬ (¬ α)))

(postulate
  α (α → β)
  ───────── mp
      β

  ;; (# α → β → γ → δ → ...) ≡ (α → (β → (γ → (δ → ...))))
  ;; NB: (α → β → α) is not definitionally (α → (β → α))
  ───────────── VEQ
  (# α → β → α)

  ───────────────────────────────────── CR
  (# (# α → β → γ) → (α → β) → (α → γ))

  ─────────────── double-negation
  ((¬¬ α) → α)

  ───────────────────────────────────── ∀-over-→-distrib
  ((∀ x (α → β)) → ((∀ x α) → (∀ x β)))

     α
  ─────── generalization
  (∀ x α)

  (∀ x α)
  ─────── instantiation
     α)

(theorem
  ─────── I
  (α → α)

  mp [α ≔ (# α → α → α) β ≔ (α → α)] VEQ
    mp [α ≔ (# α → (α → α) → α)
        β ≔ (# (# α → α → α) → α → α)]
      VEQ CR)

(theorem
    ─── v
     β
  ─────── →-intro
  (α → β)

  mp v VEQ)

(theorem
  ─────────────────────────────── bicond-prop-law
  (((α → β) ∧ (β → α)) → (α ↔ β))
  I)

(theorem
  ─────────── lem
  (α ∨ (¬ α))
  I)

(lemma
  ───────────── h ─────── g
  (# α → β → γ)   (α → β)
  ─────────────────────── CR-rule
          (α → γ)

  mp [α ≔ (α → β) β ≔ (α → γ)] g
    mp [α ≔ (# α → β → γ)
        β ≔ ((α → β) → (α → γ))]
      h CR)

(postulate
  ─────────────────── no-upper-bound
  (∀ a (∃ b (a > b))))

;; fails
(lemma
  ─────────────────── variable-bound-fail
  (∀ b (∃ b (b > b)))
  no-upper-bound)