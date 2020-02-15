variables (α : Type) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := begin
intro,
apply iff.intro, {
  intro f, exact f a
}, {
  intros, assumption
}
end

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := begin
apply iff.intro, {
  intro h,
  apply classical.by_cases, {
    assume hr: r, right, assumption
  }, {
    assume hnr: ¬ r, left,
    intro,
    apply or.elim (h x), {
      intro, assumption,
    }, {
      intro, contradiction,
    }
  }
}, {
  intro h,
  intro,
  apply or.elim h, {
    intro h1, left, exact h1 x
  }, {
    intro, right, assumption
  }
}
end

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := begin
apply iff.intro, {
  intros h hr x, exact h x hr
}, {
  intros h x hr, exact h hr x
}
end
