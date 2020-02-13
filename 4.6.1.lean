variables (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := ⟨
  assume h: (∀ x, p x ∧ q x),
  show (∀ x, p x) ∧ (∀ x, q x), from (
    have h1: ∀ x, p x, from λ x, (h x).left,
    have h2: ∀ x, q x, from λ x, (h x).right,
    ⟨h1, h2⟩
  ),

  assume h: (∀ x, p x) ∧ (∀ x, q x),
  λ x, ⟨(h.left x), (h.right x)⟩
⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := (
  assume (h1: ∀ x, p x → q x) (h2: ∀ x, p x),
  λ x, (h1 x) (h2 x)  
)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := (
  assume h: (∀ x, p x) ∨ (∀ x, q x),
  or.elim h (
    assume hp: ∀ x, p x,
    λ x, or.inl (hp x)
  ) (
    assume hq: ∀ x, q x,
    λ x, or.inr (hq x)
  )
)