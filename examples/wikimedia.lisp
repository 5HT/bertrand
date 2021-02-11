(infix → 25) (infix ∧ 50)

(variables α β)

(postulate
  (α true)
  ──────── truth-elim
     α

    α (β true)
  ────────────── →-intro
  ((α → β) true)
  
  (α true) ((α → β) true)
  ─────────────────────── mp
        (β true))

(postulate
    α β
  ─────── ∧-formation
  (α ∧ β)
  
  (α true) (β true)
  ───────────────── ∧-intro
   ((α ∧ β) true)

  ((α ∧ β) true)
  ────────────── ∧-elim-left
     (α true)

  ((α ∧ β) true)
  ────────────── ∧-elim-right
     (β true))

;; https://wikimedia.org/api/rest_v1/media/math/render/svg/3a6c22831067960643c6988d6c9889bfe14bed76
(theorem
  ──────── u  ──────── w
  (α true)    (β true)
  ────────────────────── wikimedia-example
  ((# α → β → α ∧ β) true)

  →-intro
    truth-elim u
    →-intro
      truth-elim w
      ∧-intro u w)

;; https://wikimedia.org/api/rest_v1/media/math/render/svg/87c96716eb4cd6dabc991b253d6d878790f81b6b
(theorem
  ────────────── α,β
  ((α ∧ β) true)
  ────────────── ∧-rev
  ((β ∧ α) true)

  ∧-intro
    ∧-elim-right α,β
    ∧-elim-left  α,β)