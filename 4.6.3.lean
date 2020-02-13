variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false := 
have hc: shaves barber barber ↔ ¬ shaves barber barber, from h barber,
have h1: shaves barber barber -> false, from λ l, hc.mp l l,
have h2: shaves barber barber, from hc.mpr h1,
h1 h2