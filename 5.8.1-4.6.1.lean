variables (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := begin
apply iff.intro, {
  intro h,
  constructor, {
    intro x, exact (h x).1
  }, {
    intro x, exact (h x).2
  }
}, {
  intro h, intro x,
  constructor, exact (h.1 x), exact (h.2 x)
}
end

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := begin
intros, exact a x (a_1 x)
end

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := begin
intros,
apply or.elim a, {
  intro hp, left, exact (hp x)
}, {
  intro hq, right, exact (hq x)
}
end
