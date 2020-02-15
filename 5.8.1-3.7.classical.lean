open classical

variables p q r s : Prop

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := begin
intro h, apply by_cases, {
  assume hp: p,
  cases (h hp),
    left, intro, assumption,
    right, intro, assumption,
}, {
  assume hnp: ¬ p,
  exact (or.inl $ λ hp:p, absurd hp hnp)
}
end

example : ¬(p ∧ q) → ¬p ∨ ¬q := begin
intro h, apply by_cases, {
  assume hp: p,
  right, intro hq, exact (h ⟨hp, hq⟩)
}, {
  assume hnp: ¬ p, left, assumption
}
end

lemma dne {p: Prop} (h: ¬ ¬ p) : p := 
or.elim (em p)
  (assume hp: p, hp)
  (assume hnp: ¬ p, absurd hnp h)

example : ¬(p → q) → p ∧ ¬q := begin
intro h, apply by_contradiction, {
  intro hc,
  have hcc: p -> ¬ q -> false, from λ x y, hc ⟨x, y⟩,
  have: p -> q, {
    intro hp,
    have: ¬ ¬ q, from hcc hp, apply dne this
  }, contradiction
}
end

example : (p → q) → (¬p ∨ q) := begin
intro h, apply by_cases, {
  assume: p, right, exact (h this)
}, {
  assume: ¬ p, left, assumption
}
end

example : (¬q → ¬p) → (p → q) := begin
intro h, intro hp, apply by_cases, {
  assume: q, assumption
}, {
  assume:  ¬ q, have: ¬ p, from h this, contradiction
}
end

example : p ∨ ¬p := begin
apply em p
end

example : (((p → q) → p) → p) := begin
intro h, apply by_contradiction, {
  intro hnp,
  have: p -> q, from λ hp, absurd hp hnp,
  have: p, from h this, contradiction
}
end
