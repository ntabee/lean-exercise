variables a b c d e : Prop
variable p : Prop → Prop

theorem thm₁ (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
propext h ▸ iff.refl _

theorem thm₂ (h : a ↔ b) (h₁ : p a) : p b :=
propext h ▸ h₁

-- BEGIN
#print axioms thm₁  -- propext
#print axioms thm₂  -- propext
-- END

#check propext
#check thm₂

theorem pe_from_thm₂ {a b: Prop}: (a ↔ b) -> a = b := begin
intro h,
let P: Prop -> Prop := λ x, a = x,
have: implies (a = a)  (a = b), from @thm₂ a b P h,
from this rfl,
end
