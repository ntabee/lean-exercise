open classical

lemma imp_or : ∀ p q: Prop, (p → q) → (¬p ∨ q) := begin
intros p q h, apply by_cases, {
  assume: p, right, exact (h this)
}, {
  assume: ¬ p, left, assumption
}
end
#check imp_or

lemma nall_en: ∀ α: Type, ∀ p: α -> Prop, (¬ ∀ x, p x) -> (∃ x, ¬ p x) := begin
intros,
apply by_contradiction, {
  intro hc,
  have: ∀ x, p x, {
    intro, apply by_contradiction, {
      intro hnpx,
      have: ∃ x, ¬ p x, from ⟨x, hnpx⟩, contradiction
    }
  }, contradiction
}
end
#check nall_en

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

example : (∃ x : α, r) → r := begin
intro h, cases h, assumption
end

include a
example : r → (∃ x : α, r) := begin
intro hr, exact ⟨a, hr⟩
end

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := begin
apply iff.intro, {
  intro h, cases h, constructor,
    exact ⟨h_w, h_h.1⟩,
    exact h_h.2
}, {
  intro h, cases h.1, existsi w, constructor, exact h_1, exact h.2
}
end

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := begin
apply iff.intro, {
  intro h, cases h, cases h_h,
    left, exact ⟨h_w, h_h⟩,
    right, exact ⟨h_w, h_h⟩
}, {
  intro h, cases h, 
    cases h, existsi h_w, left, assumption,
    cases h, existsi h_w, right, assumption,
}
end

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := begin
apply iff.intro, {
  intro h, intro h1,
  cases h1 with w hnpw, exact hnpw (h w)
}, {
  intro h, intro x,
  apply by_contradiction, {
    intro hnpx,
    have h2: (∃ x, ¬ p x), from ⟨x, hnpx⟩,
    contradiction
  }
}
end

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := begin
apply iff.intro, {
  intro h, cases h,
  intro hnpx, exact hnpx h_w h_h
}, {
  intro h, apply by_contradiction, {
    intro hc,
    have: ∀ x, ¬ p x, {
      intro x,
      intro hpx,
      have: ∃ x, p x, from ⟨x, hpx⟩,
      contradiction
    }, contradiction
  }
}
end

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := begin
apply iff.intro, {
  intros h x,
  assume: p x, exact h ⟨x, this⟩
}, {
  intros h hnxp, cases hnxp with w pw,
  have: ¬ p w, from h w, contradiction
}
end

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := begin
apply iff.intro, {
  intro h,
  exact nall_en α p h,
}, {
  intro h, cases h,
  intro hpx,
  have: p h_w, from hpx h_w, contradiction
}
end

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := begin
apply iff.intro, {
  intros h he, cases he,
  exact h he_w he_h
}, {
  intro h, intros x hpx,
  exact h ⟨x, hpx⟩
}
end

example : (∃ x, p x → r) ↔ (∀ x, p x) → r := begin
apply iff.intro, {
  intros h hpx, cases h,
  have: p h_w, from hpx h_w,
  exact h_h this
}, {
  intro h,
  have: (¬ ∀ x, p x) ∨ r, from imp_or (∀ x, p x) r h,
  cases this, {
    have: ∃ x, ¬ p x, from nall_en α p this,
    cases this with w hnpw,
    existsi w, intro, contradiction
  }, {
    existsi a, intro, assumption
  }
}
end

example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := begin
apply iff.intro, {
  intros h hr,
  cases h,
  exact ⟨h_w, h_h hr⟩ 
}, {
  intro h, apply by_cases, {
    assume hr: r,
    cases (h hr) with w pw,
    existsi w, intro, assumption
  }, {
    assume: ¬ r,
    existsi a, intro hr, contradiction
  }
}
end
