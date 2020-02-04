(variables
  ;; contexts
  Γ Δ Ρ
  ;; types
  τ σ ρ
  ;; variables
  x y z e e₁ e₂)

(bound (λ (x : _) _))

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
  (λ-elim [Γ ≔ ℕ-ctx
           e₁ ≔ succ e₂ ≔ 0
           σ ≔ ℕ τ ≔ ℕ]
          ℕ-ctx-def
          (ctx-intro [Γ ≔ ℕ-ctx x ≔ succ σ ≔ (ℕ → ℕ)]
                     ℕ-ctx-def succ-def)
          (ctx-intro [Γ ≔ ℕ-ctx x ≔ 0 σ ≔ ℕ]
                     ℕ-ctx-def 0-def)))

(theorem
  ──────────────────────── λ-ctx-def
  ((ℕ-ctx ∪ (x : ℕ)) ctx)
  (ctx-∪ [Γ ≔ ℕ-ctx σ ≔ ℕ] ℕ-ctx-def)

  ──────────────────────────────────────── λ-ctx-contains-succ
  ((ℕ-ctx ∪ (x : ℕ)) ⊢ succ : (ℕ → ℕ))
  (ctx-intro
    [Γ ≔ (ℕ-ctx ∪ (x : ℕ))
     x ≔ succ σ ≔ (ℕ → ℕ)]
    λ-ctx-def
    (∪-conservativity
      [Γ ≔ ℕ-ctx x ≔ succ y ≔ x
       σ ≔ (ℕ → ℕ) τ ≔ ℕ]
      ℕ-ctx-def succ-def))

  ────────────────────────────────────────────────── succ-twice
  (ℕ-ctx ⊢ (λ (x : ℕ) (succ (succ x))) : (ℕ → ℕ))
  (λ-intro [Γ ≔ ℕ-ctx σ ≔ ℕ τ ≔ ℕ e ≔ (succ (succ x))]
           ℕ-ctx-def
           (λ-elim [Γ ≔ (ℕ-ctx ∪ (x : ℕ))
                    e₁ ≔ succ e₂ ≔ (succ x)
                    σ ≔ ℕ τ ≔ ℕ]
                   λ-ctx-def λ-ctx-contains-succ
                   (λ-elim [Γ ≔ (ℕ-ctx ∪ (x : ℕ))
                            e₁ ≔ succ e₂ ≔ x
                            σ ≔ ℕ τ ≔ ℕ]
                           λ-ctx-def λ-ctx-contains-succ
                           (ctx-intro
                             [Γ ≔ (ℕ-ctx ∪ (x : ℕ)) σ ≔ ℕ]
                             λ-ctx-def
                             (ctx-∈ [Γ ≔ ℕ-ctx σ ≔ ℕ] ℕ-ctx-def)))))

  ────────────────────────────────────────────────────── fail
  (ℕ-ctx ⊢ (λ (succ : ℕ) (succ (succ succ))) : (ℕ → ℕ))
  (succ-twice [x ≔ succ]))