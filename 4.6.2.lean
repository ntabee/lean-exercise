variables (α : Type) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := 
assume y: α,
⟨
  assume h: ∀ x: α, r,
  h y,

  λ hr: r, λ _, hr
⟩

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := ⟨
  assume h: (∀ x, p x ∨ r),
  show (∀ x, p x) ∨ r, from classical.by_contradiction (
    assume hc: ¬ ((∀ x, p x) ∨ r),
    classical.by_cases (
      assume hr: r,
      hc $ or.inr hr
    ) (
      assume hnr: ¬ r,
      have hpx: ∀ x, p x, from 
      λ x, or.elim (h x) (
        λ px: p x, px
      ) (
        λ hr: r, 
        absurd hr hnr
      ),
      hc $ or.inl hpx
    )
  ),

  assume h: (∀ x, p x) ∨ r,
  or.elim h (
    λ hpx, λ x, or.inl $ hpx x
  ) (
    λ hr, λ x, or.inr hr
  )
⟩

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := ⟨
  assume h: ∀ x, r → p x,
  λ hr, λ x, h x hr,

  assume h: r → ∀ x, p x,
  λ x, λ hr, h hr x
⟩