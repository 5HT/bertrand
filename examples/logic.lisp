(infix → 25)

(variables α β γ δ φ x a b c)

(bound (∀ x _))

(define (∃ x φ) (¬ (∀ x (¬ φ))))
(define (α ∧ β) (¬ (α → (¬ β))))
(define (α ∨ β) ((¬ α) → β))
(define (α ↔ β) ((α → β) ∧ (β → α)))

(define (¬¬ α) (¬ (¬ α)))

(postulate
  ─────────────────── no-upper-bound
  (∀ a (∃ b (a > b))))

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
  lem-1 (VEQ [β ≔ (α → α)])
  lem-2 (CR [β ≔ (α → α) γ ≔ α])
  lem-3 (VEQ [β ≔ α])
  lem-4 (mp [α ≔ (# α → (α → α) → α)
             β ≔ (# (# α → α → α) → α → α)] lem-1 lem-2)
  th (mp [α ≔ (# α → α → α) β ≔ (α → α)] lem-3 lem-4))

(theorem
    ─── v
     β
  ─────── →-intro
  (α → β)
  lem (VEQ [α ≔ β β ≔ α])
  th  (mp [α ≔ β β ≔ (α → β)] v lem))

(theorem
  ─────────────────────────────── bicond-prop-law
  (((α → β) ∧ (β → α)) → (α ↔ β))
  th (I [α ≔ ((α → β) ∧ (β → α))]))

(theorem
  ─────────── lem
  (α ∨ (¬ α))
  th (I [α ≔ (¬ α)]))

(lemma
  ───────────── h ─────── g
  (# α → β → γ)   (α → β)
  ─────────────────────── CR-rule
          (α → γ)
  lem (mp [α ≔ (# α → β → γ)
           β ≔ ((α → β) → (α → γ))] h CR)
  th (mp [α ≔ (α → β) β ≔ (α → γ)] g lem))

;; fails
(lemma
  ─────────────────── variable-bound-fail
  (∀ b (∃ b (b > b)))
  th (no-upper-bound [a ≔ b]))