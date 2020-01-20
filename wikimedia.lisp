(infix → 25) (infix ∧ 50)

(variables α β)

(axiom truth-elim (α true) α)

(axiom →-intro α (β true) ([α → β] true))
(axiom mp α [α → β] β)

(axiom ∧-intro (α true) (β true) ([α ∧ β] true))

;; https://wikimedia.org/api/rest_v1/media/math/render/svg/3a6c22831067960643c6988d6c9889bfe14bed76
(theorem wikimedia-example
  u (α true) w (β true)
  ([α → β → α ∧ β] true)
  (→-intro
    (truth-elim (u ()) ())
    (→-intro
      (truth-elim (w ()) (α β))
      (∧-intro (u ()) (w ()) ())
      (α β
       β [α ∧ β]))
    (β [β → α ∧ β])))