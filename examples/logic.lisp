;; TODO:
;;; definitions

(infix → 25)

(variables α β γ x a b c)

(bound (∀ x _) (∃ x _))

(postulate
  ───────────── no-upper-bound
  (∀ a (∃ b (a > b))))

;; fails
(lemma
  ───────────── variable-bound-fail
  (∀ b (∃ b (b > b)))
  (no-upper-bound (a b)))

(postulate
  α (α → β)
  ───────── mp
      β

  ;; [α → β → γ → δ → …] ≡ (α → (β → (γ → (δ → …))))
  ;; NB: (α → β → α) is not definitionally (α → (β → α))
  ─────────── VEQ
  [α → β → α]

  ───────────────────────────────── CR
  [[α → β → γ] → (α → β) → (α → γ)]

  ─────────────── double-negation
  ((¬ (¬ α)) → α)

  ───────────────────────────────────── ∀-over-→-distrib
  ((∀ x (α → β)) → ((∀ x α) → (∀ x β)))

  ───────────── generalization
  (α → (∀ x α))

  ───────────── specialization
  ((∀ x α) → α))

(theorem
  ─────── I
  [α → α]
  (mp (VEQ (β α))
      (mp (VEQ (β (α → α)))
          (CR  (β (α → α) γ α))
          (α [α → (α → α) → α]
           β [[α → α → α] → α → α]))
      (α [α → α → α]
       β [α → α])))

(lemma
  ─────────── h ─────── g
  [α → β → γ]   (α → β)
  ─────────────────────── CR-rule
          (α → γ)
  (mp g
      (mp h CR
          (α [α → β → γ]
           β ((α → β) → (α → γ))))
      (α (α → β)
       β (α → γ))))