(infix → 25)

(variables Γ Δ Τ Θ f g α β γ τ μ ρ x y)

(define (α = β) ((Id α) β))
(bound (λ (x : _) _))

;; http://us.metamath.org/holuni/mmtheorems1.html
(postulate
  (Γ ⊢ Δ) (Δ ⊢ Τ)
  ─────────────── ⊢-syll
     (Γ ⊢ Τ)

  (Γ ⊢ Δ) (Γ ⊢ Τ)
  ─────────────── ⊢-join
   (Γ ⊢ (Δ , Τ))

  (τ : Prop) (μ : Prop)
  ───────────────────── ⊢-simpl
      ((τ , μ) ⊢ τ)

  (τ : Prop) (μ : Prop)
  ───────────────────── ⊢-simpr
      ((τ , μ) ⊢ μ)

  (τ : Prop)
  ────────── ⊢-id
   (τ ⊢ τ)

  (τ : Prop)
  ────────── ⊤-intro
   (τ ⊢ ⊤)

   (Γ ⊢ Δ)
  ───────── ctx₁-Prop
  (Γ : Prop)

   (Γ ⊢ Δ)
  ───────── ctx₂-Prop
  (Δ : Prop)

  ((Γ , Δ) : Prop)
  ──────────────── join₁-Prop
     (Γ : Prop)

  ((Γ , Δ) : Prop)
  ──────────────── join₂-Prop
     (Δ : Prop)

  ────────────────────── =-form
  (Id : (# α → α → Prop))

     (μ : α)
  ───────────── =-refl
  (⊤ ⊢ (μ = μ))

  (Γ ⊢ Δ) (Γ ⊢ (Δ = Τ))
  ───────────────────── =-mp
        (Γ ⊢ Τ)

        (f : (α → β)) (g : (α → β))
             (Γ : α) (Δ : α)
  ────────────────────────────────────── =-cong
  (((f = g) , (Γ = Δ)) ⊢ ((f Γ) = (g Δ)))

             (Γ : β)
  ──────────────────────────── β-subst
  (⊤ ⊢ ((λ (x : α) (Γ x)) = Γ)))

(theorem
  ────────── ⊤-form
  (⊤ : Prop)

  ctx₁-Prop =-refl =-form)

(theorem
  ───────── Γ-form ─────── Δ-truth
  (Γ : Prop)       (⊤ ⊢ Δ)
  ──────────────────────── ⊤⇒ctx
           (Γ ⊢ Δ)

  ⊢-syll ⊤-intro Γ-form Δ-truth)

(theorem
  ─────── Δ-truth ─────── Τ-truth ──────────── Θ-truth
  (Γ ⊢ Δ)         (Γ ⊢ Τ)        ((Δ , Τ) ⊢ Θ)
  ──────────────────────────────────────────── ⊢-syll₂
                  (Γ ⊢ Θ)

  ⊢-syll ⊢-join Δ-truth Τ-truth Θ-truth)

(theorem
  ─────── Δ-truth  ──────────── Τ-truth
  (Γ ⊢ Δ)         ((Γ , Δ) ⊢ Τ)
  ───────────────────────────── ⊢-mp
              (Γ ⊢ Τ)

  ⊢-syll₂ [Δ ≔ Γ Τ ≔ Δ Θ ≔ Τ]
    ⊢-id ctx₁-Prop Δ-truth
    Δ-truth Τ-truth)

(theorem
  ───────────── Τ-truth  ───────────── Θ-truth
  ((Γ , Δ) ⊢ Τ)          ((Γ , Τ) ⊢ Θ)
  ──────────────────────────────────── syll-inf
              ((Γ , Δ) ⊢ Θ)

  ⊢-syll₂ [Γ ≔ (Γ , Δ) Δ ≔ Γ]
    ⊢-simpl join₁-Prop ctx₁-Prop Τ-truth
            join₂-Prop ctx₁-Prop Τ-truth
    Τ-truth Θ-truth)

(theorem
   ───────────── hyp
   (Γ ⊢ (Δ , Τ))
   ───────────── join-left
     (Γ ⊢ Δ)

  ⊢-syll hyp
    ⊢-simpl
      join₁-Prop ctx₂-Prop hyp
      join₂-Prop ctx₂-Prop hyp)

(theorem
   ───────────── hyp
   (Γ ⊢ (Δ , Τ))
   ───────────── join-right
     (Γ ⊢ Τ)

  ⊢-syll hyp
    ⊢-simpr
      join₁-Prop ctx₂-Prop hyp
      join₂-Prop ctx₂-Prop hyp)