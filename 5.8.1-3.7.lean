variables p q r : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := begin
apply iff.intro, all_goals {intro h, exact ⟨h.2, h.1⟩ }
end
example : p ∨ q ↔ q ∨ p := begin
apply iff.intro, all_goals {intro h, cases h, {right, assumption}, {left, assumption} }
end

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := begin
apply iff.intro, {
  intro h, rw [and_assoc] at h, exact h
}, {
  intro h,
  rw [and_assoc], exact h
}
end
  
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := begin
apply iff.intro, {
  intro h, rw [or_assoc] at h, exact h
}, {
  intro h, rw [or_assoc], exact h
}
end

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := begin
apply iff.intro, {
  intro h,
  have hp: p := h.1,
  cases h.2,
  all_goals {
    {left, constructor, repeat {assumption}} <|> {right, constructor, repeat {assumption}}
  }
}, {
  intro h,
  cases h,
  all_goals { exact ⟨h.1, or.inl h.2⟩ <|> exact ⟨h.1, or.inr h.2⟩}
}
end

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := begin
apply iff.intro, {
  intro h,
  cases h with hp hqr,
    exact ⟨or.inl hp, or.inl hp⟩,
    exact ⟨or.inr hqr.1, or.inr hqr.2⟩,
}, {
  intro h,
  apply or.elim h.1,
    intro, left, assumption,
    intro, cases h.2 with hp hr,
      left, assumption,
      right, constructor, repeat{assumption}
}
end

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := begin
apply iff.intro, {
  intros, exact a a_1.1 a_1.2
}, {
  intros, exact a ⟨a_1, a_2⟩
}
end

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := begin
apply iff.intro, {
  intro h,
  exact ⟨λ hp, h $ or.inl hp, λ hq, h $ or.inr hq⟩
}, {
  intro h,
  intro hpq, cases hpq,
    exact h.1 hpq,
    exact h.2 hpq,
}
end

example : ¬p ∨ ¬q → ¬(p ∧ q) := begin
intro h,
intro hpq,
cases h,
  exact h hpq.1,
  exact h hpq.2,
end

example : ¬(p ∧ ¬p) := begin
intro h, exact h.2 h.1
end

example : p ∧ ¬q → ¬(p → q) := begin
  intro h1, intro h2, exact (h1.2 $ h2 h1.1)
end

example : ¬p → (p → q) := begin
intros, contradiction
end

example : (¬p ∨ q) → (p → q) := begin
intros, cases a,
  contradiction,
  assumption
end

example : p ∨ false ↔ p := begin
apply iff.intro, {
  intro h, cases h,
    assumption,
    contradiction,
}, {
  intro h, left, assumption
}
end

example : p ∧ false ↔ false := begin
apply iff.intro, {
  intro h, exact h.2
}, {
  intro, contradiction
}
end

example : ¬(p ↔ ¬p) := begin
intro hc, simp at hc, assumption
end

example : (p → q) → (¬q → ¬p) := begin
intro h, intro hnq, exact (λ hp, hnq $ h hp)
end

