variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false := begin
intros,
have hsbb := (h barber),
have no := λ sbb, hsbb.mp sbb sbb,
have yes := hsbb.mpr no,
contradiction
end
