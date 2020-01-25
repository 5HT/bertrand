(variables
  ;; contexts
  Γ Δ Ρ
  ;; types
  τ σ ρ
  ;; variables
  x y z e e₁ e₂)

(postulate
  (Γ ctx) ((x : σ) ∈ Γ)
  ───────────────────── ctx-intro
      (Γ ⊢ (x : σ)))

(postulate λ-intro
  (Γ ctx) ((cons (x : σ) Γ) ⊢ (e : τ))
  ──────────────────────────────────── λ-intro
  (Γ ⊢ ((λ (x : σ) e) : (σ → τ)))

                (Γ ctx)
  (Γ ⊢ (e₁ : (σ → τ))) (Γ ⊢ (e₂ : σ))
  ─────────────────────────────────── λ-elim
          (Γ ⊢ ((e₁ e₂) : τ)))

(postulate
  ─────────── ℕ-ctx-def
  (ℕ-ctx ctx)

  ────────────────── 0-def
  ((0 : ℕ) ∈ ℕ-ctx)

  ─────────────────────────── succ-def
  ((succ : (ℕ → ℕ)) ∈ ℕ-ctx))

(theorem
  ───────────────────────── 1-def
  (ℕ-ctx ⊢ ((succ 0) : ℕ))
  (λ-elim (ℕ-ctx-def ())
          (ctx-intro (ℕ-ctx-def ()) (succ-def ())
                     (Γ ℕ-ctx x succ σ (ℕ → ℕ)))
          (ctx-intro (ℕ-ctx-def ()) (0-def ())
                     (Γ ℕ-ctx x 0 σ ℕ))
          (Γ ℕ-ctx
           e₁ succ e₂ 0
           σ ℕ τ ℕ)))