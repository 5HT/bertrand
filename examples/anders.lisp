;; Anders CCHM prover configuration file

;; -- boot
(variables Γ Δ Π Ρ τ σ ρ μ η x y z b e e₁ e₂)
(infix : 50)
(bound (λ (x : _) _))
(bound (x : Π _))
;; -- meta-nat
(postulate           ─ 0-def (0 : nat))
(postulate (x : nat) ─ succ-def ((succ x) : nat))
;; -- cosmos
(postulate (n : nat) ─ Γ-def (Γ-n kan))
(postulate (n : nat) ─ Δ-def (Δ-n pre))
;; -- presheaf-1
(postulate (x : Π e) ─ Π-λ (x : Π (λ (y : σ) e)))
