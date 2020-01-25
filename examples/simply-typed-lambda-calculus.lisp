(variables
  ;; contexts
  Γ Δ Ρ
  ;; types
  τ σ ρ
  ;; variables
  x y z e e₁ e₂)

(axiom ctx-intro
  (Γ ctx) ((x : σ) ∈ Γ)
  (Γ ⊢ (x : σ)))

(axiom λ-intro
  (Γ ctx) ((cons (x : σ) Γ) ⊢ (e : τ))
  (Γ ⊢ ((λ (x : σ) e) : (σ → τ))))

(axiom λ-elim
  (Γ ctx)
  (Γ ⊢ (e₁ : (σ → τ)))
  (Γ ⊢ (e₂ : σ))
  (Γ ⊢ ((e₁ e₂) : τ)))

(axiom ℕ-ctx-def (ℕ-ctx ctx))
(axiom 0-def    ((0 : ℕ) ∈ ℕ-ctx))
(axiom succ-def ((succ : (ℕ → ℕ)) ∈ ℕ-ctx))

(theorem 1-def (ℕ-ctx ⊢ ((succ 0) : ℕ))
  (λ-elim (ℕ-ctx-def ())
          (ctx-intro (ℕ-ctx-def ()) (succ-def ())
                     (Γ ℕ-ctx x succ σ (ℕ → ℕ)))
          (ctx-intro (ℕ-ctx-def ()) (0-def ())
                     (Γ ℕ-ctx x 0 σ ℕ))
          (Γ ℕ-ctx
           e₁ succ e₂ 0
           σ ℕ τ ℕ)))