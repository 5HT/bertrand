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
      (Γ ⊢ x : σ)

        (Γ ctx)
  ─────────────────── ctx-∪
  ((Γ ∪ (x : σ)) ctx)

            (Γ ctx)
  ───────────────────────── ctx-∈
  ((x : σ) ∈ (Γ ∪ (x : σ)))

    (Γ ctx) ((x : σ) ∈ Γ)
  ───────────────────────── ∪-conservativity
  ((x : σ) ∈ (Γ ∪ (y : τ)))

    (Γ ctx) (Γ ⊢ τ)
  ─────────────────── ⊢-conservativity
  ((Γ ∪ (x : σ)) ⊢ τ))

(postulate
  (Γ ctx) ((Γ ∪ (x : σ)) ⊢ e : τ)
  ───────────────────────────────── λ-intro
  (Γ ⊢ (λ (x : σ) e) : (σ → τ))

               (Γ ctx)
  (Γ ⊢ e₁ : (σ → τ)) (Γ ⊢ e₂ : σ)
  ──────────────────────────────── λ-elim
          (Γ ⊢ (e₁ e₂) : τ))

(postulate
  ─────────── ℕ-ctx-def
  (ℕ-ctx ctx)

  ────────────────── 0-def
  ((0 : ℕ) ∈ ℕ-ctx)

  ─────────────────────────── succ-def
  ((succ : (ℕ → ℕ)) ∈ ℕ-ctx))

(theorem
  ───────────────────────── 1-def
  (ℕ-ctx ⊢ (succ 0) : ℕ)
  (λ-elim ℕ-ctx-def
          (ctx-intro ℕ-ctx-def succ-def
                     (Γ ℕ-ctx x succ σ (ℕ → ℕ)))
          (ctx-intro ℕ-ctx-def 0-def
                     (Γ ℕ-ctx x 0 σ ℕ))
          (Γ ℕ-ctx
           e₁ succ e₂ 0
           σ ℕ τ ℕ)))

(theorem
  ──────────────────────── λ-ctx-def
  ((ℕ-ctx ∪ (x : ℕ)) ctx)
  (ctx-∪ ℕ-ctx-def (Γ ℕ-ctx σ ℕ))

  ──────────────────────────────────────── λ-ctx-contains-succ
  ((ℕ-ctx ∪ (x : ℕ)) ⊢ succ : (ℕ → ℕ))
  (ctx-intro
    λ-ctx-def
    (∪-conservativity
      ℕ-ctx-def succ-def
      (Γ ℕ-ctx x succ y x σ (ℕ → ℕ) τ ℕ))
    (Γ (ℕ-ctx ∪ (x : ℕ)) x succ σ (ℕ → ℕ)))

  ────────────────────────────────────────────────── succ-twice
  (ℕ-ctx ⊢ (λ (x : ℕ) (succ (succ x))) : (ℕ → ℕ))
  (λ-intro ℕ-ctx-def
           (λ-elim λ-ctx-def λ-ctx-contains-succ
                   (λ-elim λ-ctx-def λ-ctx-contains-succ
                           (ctx-intro
                             λ-ctx-def
                             (ctx-∈ ℕ-ctx-def (Γ ℕ-ctx σ ℕ))
                             (Γ (ℕ-ctx ∪ (x : ℕ)) σ ℕ))
                           (Γ (ℕ-ctx ∪ (x : ℕ))
                            e₁ succ e₂ x
                            σ ℕ τ ℕ))
                   (Γ (ℕ-ctx ∪ (x : ℕ))
                    e₁ succ e₂ (succ x)
                    σ ℕ τ ℕ))
           (Γ ℕ-ctx σ ℕ τ ℕ e (succ (succ x)))))