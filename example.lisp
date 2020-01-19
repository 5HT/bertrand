;; TODO:
;;; definitions

(infix → 25)

(variables α β γ)

(axiom mp α [α → β] β)
(axiom VEQ [α → β → α])
(axiom CR  [[α → β → γ] → [α → β] → α → γ])

(theorem I [α → α]
  (mp (VEQ (β α))
      (mp (VEQ (β [α → α]))
          (CR  (β [α → α] γ α))
          (α [α → [α → α] → α]
           β [[α → α → α] → α → α]))
      (α [α → α → α]
       β [α → α])))

(lemma CR-rule h [α → β → γ] g [α → β] [α → γ]
  (mp (g ())
      (mp (h ()) (CR ())
          (α [α → β → γ]
           β [[α → β] → [α → γ]]))
      (α [α → β]
       β [α → γ])))
