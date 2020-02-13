open classical

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

example : (∃ x : α, r) → r := 
  assume h: (∃ x: α, r),
  match h with ⟨w, hr⟩ := hr end

example : r → (∃ x : α, r) := 
  assume hr: r,
  ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := ⟨
  assume h: (∃ x, p x ∧ r),
  let ⟨w, c⟩ := h in ⟨
    ⟨w, c.left⟩,
    c.right
  ⟩,

  assume h: (∃ x, p x) ∧ r,
  let ⟨w, pw⟩ := h.left in ⟨w, pw, h.right⟩
⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := ⟨
  assume h: (∃ x, p x ∨ q x),
  let ⟨w, dw⟩ := h in 
  show (∃ x, p x) ∨ (∃ x, q x), from or.elim dw (
    λ hpw: p w, or.inl ⟨w, hpw⟩
  ) (
    λ hqw: q w, or.inr ⟨w, hqw⟩
  ),

  assume h: (∃ x, p x) ∨ (∃ x, q x),
  show (∃ x, p x ∨ q x), from or.elim h (
    λ hpx, let ⟨w, pw⟩ := hpx in ⟨w, or.inl pw⟩
  ) (
    λ hqx, let ⟨w, qw⟩ := hqx in ⟨w, or.inr qw⟩
  )
⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := ⟨
  assume h: (∀ x, p x),
  show ¬ (∃ x, ¬ p x), from (
    assume hnpx: ∃ x, (p x -> false),
    let ⟨w, hnpw⟩ := hnpx in
    have pw: p w, from h w,
    show false, from hnpw pw
  ),

  assume h: ¬ (∃ x, ¬ p x),
  show ∀ x, p x, from 
  assume y: α,
  show p y, from by_contradiction (
    assume h1: ¬ p y,
    have h2: (∃ x, ¬ p x), from ⟨y, h1⟩,
    h h2
  )
⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := ⟨
  assume h: ∃ x, p x,
  show ¬ (∀ x, ¬ p x), from (
    let ⟨w, hpw⟩ := h in
    λ hnpx: ∀ x, ¬ p x, hnpx w hpw
  ),

  assume h: ¬ (∀ x, ¬ p x),
  show ∃ x, p x, from by_contradiction (
    assume h1: ¬ (∃ x, p x),
    have h2: ∀ x, ¬ p x, from (
      assume y: α,
      show p y -> false, from
      assume hpy: p y,
      have hpx: ∃ x, p x, from ⟨y, hpy⟩,
      h1 hpx
    ),
    h h2
  )
⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := ⟨
  assume h: ¬ ∃ x, p x,
  show ∀ x, ¬ p x, from (
    assume y: α,
    show p y -> false, from 
    assume hpy: p y,
    h ⟨y, hpy⟩
  ),

  assume h: ∀ x, ¬ p x,
  show ¬ ∃ x, p x, from (
    assume hpx: ∃ x, p x,
    let ⟨w, hpw⟩ := hpx in
    h w hpw
  ),
⟩

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := ⟨
  assume h: ¬ ∀ x, p x,
  show ∃ x, ¬ p x, from by_contradiction (
    assume h1: ¬ ∃ x, ¬ p x,
    have hpx: ∀ x, p x, from (
      assume y: α,
      show p y, from by_contradiction (
        assume hnpy: ¬ p y,
        h1 ⟨y, hnpy⟩        
      )
    ),
    h hpx
  ),

  assume h: ∃ x, ¬ p x,
  show ¬ ∀ x, p x, from (
    let ⟨w, hnpw⟩ := h in
    assume h1: ∀ x, p x,
    have hpw: p w, from h1 w,
    show false, from hnpw hpw
  ), 
⟩

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := ⟨
  assume h: ∀ x, p x → r,
  show (∃ x, p x) → r, from (
    assume h1: ∃ x, p x,
    let ⟨y, hpy⟩ := h1 in
    have h2: p y -> r, from h y,
    show r, from h2 hpy
  ),

  assume h: (∃ x, p x) → r,
  show ∀ x, p x -> r, from (
    assume y: α,
    show p y -> r, from (
      assume hpy: p y,
      have hpx: ∃ x, p x, from ⟨y, hpy⟩,
      show r, from h hpx
    )
  ),
⟩

example : (∃ x, p x → r) ↔ (∀ x, p x) → r := ⟨
  assume h: ∃ x, p x → r,
  show (∀ x, p x) → r, from (
    assume hpx: ∀ x, p x,
    let ⟨w, hw⟩ := h in
    have hpw: p w, from hpx w,
    hw hpw
  ),

  assume h: (∀ x, p x) → r,
  show ∃ x, p x → r, from by_cases (
    assume hp: ∀ x, p x,
    have hr: r, from h hp,
    have himp: p a -> r, from λ _, hr,
    ⟨a, himp⟩
  ) (
    assume hnp: ¬ ∀ x, p x, 
    have hnp': ∃ x, ¬ p x, from by_contradiction (
      assume h1: ¬ ∃ x, ¬ p x,
      have hpx: ∀ x, p x, from (
        assume y: α,
        show p y, from by_contradiction (
          assume hnpy: ¬ p y,
          h1 ⟨y, hnpy⟩        
        )
      ),
      hnp hpx
    ),
    let ⟨w, hnpw⟩ := hnp' in
    ⟨w, λ hpx, absurd hpx hnpw⟩
  ),
⟩

example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := ⟨
  assume h: ∃ x, r → p x,
  show r → ∃ x, p x, from (
    assume hr: r,
    let ⟨w, himp⟩ := h in
    have hpw: p w, from himp hr,
    ⟨w, hpw⟩
  ),

  assume h: r → ∃ x, p x,
  show ∃ x, r → p x, from by_cases (
    assume hr: r,
    let ⟨w, hpw⟩ := h hr in
    ⟨w, λ _, hpw⟩
  ) (
    assume hnr: ¬ r,
    ⟨a, λ hr: r, absurd hr hnr⟩
  ),
⟩
