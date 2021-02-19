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
  ─────── ·-ctx
  (· ctx)

      (Γ ctx)
  ──────────────── ctx-cons
  ((Γ (x : σ)) ctx)

  ─────────── ctx-∈
  (μ ∈ (Γ μ))

    (μ ∈ Γ)
  ─────────── ctx-rec
  (μ ∈ (Γ η))

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
  ((x : σ) ∈ Γ)
  ───────────── ctx-intro
   (Γ ⊢ x : σ)

  (Γ ⊢ x : σ)
  ─────────── ctx-elim
    (ctx Γ)

       (Γ ⊢ e : τ)
  ───────────────────── ⊢-rec
  ((Γ (x : σ)) ⊢ e : τ))

(postulate
      ((Γ (x : σ)) ⊢ e : τ)
  ───────────────────────────── λ-intro
  (Γ ⊢ (λ (x : σ) e) : (σ → τ))

  (Γ ⊢ e₁ : (σ → τ)) (Γ ⊢ e₂ : σ)
  ──────────────────────────────── λ-elim
         (Γ ⊢ (e₁ e₂) : τ))

(postulate
  ─────────── 0-def
  (· ⊢ 0 : ℕ)

  ──────────────────── succ-def
  (· ⊢ succ : (ℕ → ℕ)))

(theorem
  ────────────────── 1-def
  (· ⊢ (succ 0) : ℕ)
  λ-elim succ-def 0-def)

(theorem
  ─────────────────────────────── λ-ctx-succ
  ((· (x : ℕ)) ⊢ succ : (ℕ → ℕ))
  ⊢-rec succ-def)

(theorem
  ──────────────────────────────────────────── succ-twice
  (· ⊢ (λ (x : ℕ) (succ (succ x))) : (ℕ → ℕ))
  λ-intro λ-elim
    ⊢-rec succ-def
    λ-elim
      ⊢-rec succ-def
      ctx-intro ctx-∈)

(theorem
  ───────────────────────────────────────────────── fail
  (· ⊢ (λ (succ : ℕ) (succ (succ succ))) : (ℕ → ℕ))
  succ-twice)

(define (if b then e₁ else e₂) (((ite b) e₁) e₂))

(postulate
  ────────────────── false-def
  (· ⊢ false : bool)

  ───────────────── true-def
  (· ⊢ true : bool)

  ─────────────────────────────── ite-def
  (· ⊢ ite : (# bool → σ → σ → σ)))