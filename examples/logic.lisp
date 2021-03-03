(infix → 25)

(variables α β γ δ φ x y a b c)

(bound (∀ x _))

(define (∃ x φ) (¬ (∀ x (¬ φ)))
  Existential quantifier)
(define (α ∧ β) (¬ (α → (¬ β))))
(define (α ∨ β) ((¬ α) → β))
(define (α ↔ β) ((α → β) ∧ (β → α)))

(define (¬¬ α) (¬ (¬ α)))

(theorem
  ─── hyp
   α
  ─── false
   ⊥

  hyp [α ≔ ⊥])

(description
  mp              (Modus ponens, or <i>implicaion elimination</i>)
  VEQ             (This rule corresponds to the type
                   of <code>const</code> function: $ λ x, λ y, x $)
  CR              (Chain rule as proposition)
  CR-rule         (Chain rule as deduction rule)
  double-negation (Law of double negation)
  bicond-prop-law (Material equivalence introduction)
  lem             (Law of excluded middle))

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

(description
  no-upper-bound      (Example of axiom that uses bound variables)
  variable-bound-fail (Example of invalid substitution))

(postulate
  ─────────────────── no-upper-bound
  (∀ a (∃ b (a > b))))

;; fails
(lemma
  ─────────────────── variable-bound-fail
  (∀ b (∃ b (b > b)))
  no-upper-bound)