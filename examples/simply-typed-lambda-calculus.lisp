(variables
  ;; contexts
  Γ Δ Ρ
  ;; types
  τ σ ρ μ η
  ;; variables
  x y z b e e₁ e₂)

(infix → 25) (infix ∈ 30) (infix : 50)
(bound (λ (x : _) _))

(postulate
  ((x : σ) ∈ Γ)
  ───────────── ctx-intro
   (Γ ⊢ x : σ)

  (Γ ⊢ x : σ)
  ─────────── ctx-elim
    (ctx Γ)

      (Γ ctx)
  ──────────────── ctx-cons
  ((Γ (x : σ)) ctx)

  ─────── ø-ctx
  (ø ctx)

  ─────────── ctx-∈
  (μ ∈ (Γ μ))

    (μ ∈ Γ)
  ─────────── ctx-rec
  (μ ∈ (Γ η))

      (Γ ⊢ e : τ)
  ───────────────────── ⊢-rec
  ((Γ (x : σ)) ⊢ e : τ)

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
      ((Γ (x : σ)) ⊢ e : τ)
  ───────────────────────────── λ-intro
  (Γ ⊢ (λ (x : σ) e) : (σ → τ))

  (Γ ⊢ e₁ : (σ → τ)) (Γ ⊢ e₂ : σ)
  ──────────────────────────────── λ-elim
         (Γ ⊢ (e₁ e₂) : τ))

(postulate
  ─────────── 0-def
  (ø ⊢ 0 : ℕ)

  ──────────────────── succ-def
  (ø ⊢ succ : (ℕ → ℕ)))

(theorem
  ────────────────── 1-def
  (ø ⊢ (succ 0) : ℕ)
  λ-elim succ-def 0-def)

(theorem
  ─────────────────────────────── λ-ctx-succ
  ((ø (x : ℕ)) ⊢ succ : (ℕ → ℕ))
  ⊢-rec succ-def)

(theorem
  ──────────────────────────────────────────── succ-twice
  (ø ⊢ (λ (x : ℕ) (succ (succ x))) : (ℕ → ℕ))
  λ-intro λ-elim
    ⊢-rec succ-def
    λ-elim
      ⊢-rec succ-def
      ctx-intro ctx-∈)

(theorem
  ───────────────────────────────────────────────── fail
  (ø ⊢ (λ (succ : ℕ) (succ (succ succ))) : (ℕ → ℕ))
  succ-twice)

(define (if b then e₁ else e₂) (((ite b) e₁) e₂))

(postulate
  ───────────── bool-ctx-def
  (bool-ctx ctx)

  ────────────────── false-def
  (ø ⊢ false : bool)

  ───────────────── true-def
  (ø ⊢ true : bool)

  ─────────────────────────────── ite-def
  (ø ⊢ ite : (# bool → σ → σ → σ)))