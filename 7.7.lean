namespace hidden
universe u

inductive eq {α : Type u} (a : α) : α → Prop
| refl : eq a

@[elab_as_eliminator]
theorem subst {α : Type u} {a b : α} {P : α → Prop}
  (h₁ : eq a b) (h₂ : P a) : P b :=
eq.rec h₂ h₁


-- BEGIN
theorem symm {α : Type u} {a b : α} (h : eq a b) : eq b a :=
subst h (eq.refl a)

theorem trans {α : Type u} {a b c : α}
  (h₁ : eq a b) (h₂ : eq b c) : eq a c :=
subst h₂ h₁

theorem congr {α β : Type u} {a b : α} (f : α → β)
  (h : eq a b) : eq (f a) (f b) :=
subst h (eq.refl $ f a)

-- END
end hidden