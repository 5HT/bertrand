(variables
  ;; contexts
  Γ Δ Ρ
  ;; types
  τ σ ρ
  ;; variables
  x y z b e e₁ e₂)

(bound (λ (x : _) _))

(postulate
  (Γ ctx) ((x : σ) ∈ Γ)
  ───────────────────── ctx-intro
      (Γ ⊢ x : σ)

       (Γ ctx)
  ──────────────── ctx-cons
  ((Γ (x : σ)) ctx)

            (Γ ctx)
  ───────────────────────── ctx-∈
  ((x : σ) ∈ (Γ (x : σ)))

   (Γ ctx) ((x : σ) ∈ Γ)
  ──────────────────────── cons-conservativity
  ((x : σ) ∈ (Γ (y : τ)))

   (Γ ctx) (Γ ⊢ τ)
  ────────────────── ⊢-conservativity
  ((Γ (x : σ)) ⊢ τ)
  
  (Γ ctx) (Δ ctx)
  ──────────────── ∪-form
   ((Γ ∪ Δ) ctx)

  (Γ ctx) (Δ ctx) (Γ ⊢ e : τ)
  ─────────────────────────── ∪-intro₁
       ((Γ ∪ Δ) ⊢ e : τ)

  (Γ ctx) (Δ ctx) (Δ ⊢ e : τ)
  ─────────────────────────── ∪-intro₂
      ((Γ ∪ Δ) ⊢ e : τ))

(postulate
  (Γ ctx) ((Γ (x : σ)) ⊢ e : τ)
  ───────────────────────────── λ-intro
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
  ────────────────────── 1-def
  (ℕ-ctx ⊢ (succ 0) : ℕ)
  λ-elim ℕ-ctx-def
    ctx-intro ℕ-ctx-def succ-def
    ctx-intro ℕ-ctx-def 0-def)

(theorem
  ───────────────────── λ-ctx-def
  ((ℕ-ctx (x : ℕ)) ctx)
  ctx-cons ℕ-ctx-def)

(theorem
  ─────────────────────────────────── λ-ctx-contains-succ
  ((ℕ-ctx (x : ℕ)) ⊢ succ : (ℕ → ℕ))
  ctx-intro λ-ctx-def
    cons-conservativity
      ℕ-ctx-def succ-def)

(theorem
  ──────────────────────────────────────────────── succ-twice
  (ℕ-ctx ⊢ (λ (x : ℕ) (succ (succ x))) : (ℕ → ℕ))
  λ-intro ℕ-ctx-def
    λ-elim λ-ctx-def λ-ctx-contains-succ
    λ-elim λ-ctx-def λ-ctx-contains-succ
    ctx-intro λ-ctx-def
      ctx-∈ ℕ-ctx-def)

(theorem
  ────────────────────────────────────────────────────── fail
  (ℕ-ctx ⊢ (λ (succ : ℕ) (succ (succ succ))) : (ℕ → ℕ))
  succ-twice)

(postulate
  ───────────── bool-ctx-def
  (bool-ctx ctx)

  ────────────────────────── false-def
  ((false : bool) ∈ bool-ctx)

  ────────────────────────── true-def
  ((true : bool) ∈ bool-ctx)

   (Γ ctx) ((Γ ∪ bool-ctx) ⊢ b : bool)
       (Γ ⊢ e₁ : σ) (Γ ⊢ e₂ : σ)
  ───────────────────────────────────── ite-def
  ((Γ ∪ bool-ctx) ⊢ (ite b e₁ e₂) : σ))