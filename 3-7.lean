-- https://leanprover.github.io/theorem_proving_in_lean/propositions_and_proofs.html#exercises

variables p q r : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  ⟨ assume h: p ∧ q, ⟨h.right, h.left⟩, assume h: q ∧ p, ⟨h.right, h.left⟩ ⟩

example : p ∨ q ↔ q ∨ p := 
  ⟨
    assume h: p ∨ q,
    show q ∨ p, from h.elim (λ hp: p, or.inr hp) (λ hq: q, or.inl hq),

    assume h: q ∨ p,
    show p ∨ q, from h.elim (λ hq: q, or.inr hq) (λ hp: p, or.inl hp),
  ⟩
    
-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  ⟨
    assume h: (p ∧ q) ∧ r,
    show p ∧ (q ∧ r), from ⟨h.left.left, ⟨h.left.right, h.right⟩⟩,

    assume h: p ∧ (q ∧ r),
    show (p ∧ q) ∧ r, from ⟨⟨h.left, h.right.left⟩, h.right.right⟩,
  ⟩
  
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := ⟨
  let goal := p ∨ (q ∨ r) in
  assume h: (p ∨ q) ∨ r,
  show goal, from h.elim (
    assume hpq: p ∨ q, show goal, from hpq.elim 
      (assume hp: p, show goal, from or.inl hp)
      (assume hq: q, show goal, from or.inr (or.inl hq))
  ) (
    assume hr: r, show goal, from or.inr (or.inr hr)
  ),

  let goal := (p ∨ q) ∨ r in
  assume h: p ∨ (q ∨ r),
  show goal, from h.elim (
    assume hp: p, show goal, from or.inl (or.inl hp)
  ) (
    assume hqr: q ∨ r, show goal, from hqr.elim 
      (assume hq: q, show goal, from or.inl (or.inr hq))
      (assume hr: r, show goal, from or.inr hr)
  )
⟩

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := ⟨
  assume h: p ∧ (q ∨ r),
  show (p ∧ q) ∨ (p ∧ r), from (
    have hp: p, from h.left,
    have hqr: q ∨ r, from h.right,
    or.elim hqr (
      assume hq: q, or.inl ⟨hp, hq⟩
    ) (
      assume hr: r, or.inr ⟨hp, hr⟩
    )
  ),

  assume h: (p ∧ q) ∨ (p ∧ r),
  show p ∧ (q ∨ r), from (
    or.elim h (
      assume hpq: p ∧ q,
      ⟨hpq.left, or.inl hpq.right⟩
    ) (
      assume hpr: p ∧ r,
      ⟨hpr.left, or.inr hpr.right⟩
    )
  ),
⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
let left := p ∨ (q ∧ r) in
let right := (p ∨ q) ∧ (p ∨ r) in ⟨
  assume h: left,
  show right, from or.elim h
    (λ hp: p, show right, from ⟨or.inl hp, or.inl hp⟩)
    (λ hqr: q ∧ r, show right, from ⟨or.inr hqr.left, or.inr hqr.right⟩),
  
  assume h: right,
  have hpq: p ∨ q, from h.left,
  show left, from or.elim hpq (
    λ hp: p, or.inl hp
  ) (
    λ hq: q,
      have hqr: p ∨ r, from h.right,
      show left, from or.elim hqr (
        λ hp: p, or.inl hp
      ) (
        λ hr: r, or.inr ⟨hq, hr⟩
      )
  )
⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
let left := p → (q → r) in
let right := (p ∧ q → r) in
⟨
  assume h: left,
  show right, from 
    (λ hpq: p ∧ q, h hpq.left hpq.right),

  assume h: right,
  show left, from (λ (hp: p) (hq: q), h ⟨hp, hq⟩)
⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
let left := (p ∨ q) → r, right := (p → r) ∧ (q → r) in
⟨
  assume h: left,
  show right, from ⟨λ hp: p, h $ or.inl hp,  λ hq: q, h $ or.inr hq⟩,

  assume h: right,
  show left, from λ hpq: p ∨ q, hpq.elim
    (λ hp: p, h.left hp) 
    (λ hq: q, h.right hq)
⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
let left := ¬(p ∨ q), right := ¬ p ∧ ¬ q in ⟨
  assume h: left, show right, from
  let hnp := 
    show ¬ p, from 
    assume hp: p,
    have hpq: (p ∨ q), from or.inl hp,
    show false, from h hpq in
  let hnq :=
    show ¬ q, from
    assume hq: q,
    have hpq: (p ∨ q), from or.inr hq,
    show false, from h hpq in
  ⟨hnp, hnq⟩,

  assume h: right, show left, from
  let hnp := h.left, hnq := h.right in
  assume hpq: p ∨ q,
  show false, from hpq.elim (λ hp: p, hnp hp) (λ hq: q, hnq hq)
⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) := 
assume h: ¬ p ∨ ¬ q, assume hpq: p ∧ q, show false, from
  h.elim (λ hnp: ¬ p, hnp hpq.left) (λ hnq: ¬ q, hnq hpq.right)

example : ¬(p ∧ ¬p) := 
assume h: p ∧ ¬ p, show false, from h.right h.left

example : p ∧ ¬q → ¬(p → q) := 
assume h: p ∧ ¬q,
have hp: p, from h.left, have hnq: q -> false, from h.right,
assume hpq: p -> q, show false, from hnq $ hpq hp

example : ¬p → (p → q) := 
assume hnp: ¬ p, assume hp: p, show q, from absurd hp hnp

example : (¬p ∨ q) → (p → q) := 
assume h: ¬ p ∨ q, h.elim 
  (λ hnp: ¬ p, λ hp: p, absurd hp hnp) 
  (λ hq: q, λ hp: p, hq)

example : p ∨ false ↔ p := ⟨
  assume h: p ∨ false,
  show p, from h.elim (λ x, x) false.elim,

  λ h: p, or.inl h
⟩

example : p ∧ false ↔ false := ⟨
  λ h: p ∧ false, h.right,
  λ h: false, ⟨h.elim, h⟩
⟩

example : ¬(p ↔ ¬p) := 
  assume h: (p ↔ ¬p),
  have hl: p -> p -> false, from h.mp,
  have hnp: p -> false, from λ hp, hl hp hp,
  have hr: (p -> false) -> p, from h.mpr,
  have hp: p, from hr hnp,
  absurd hp hnp

example : (p → q) → (¬q → ¬p) := 
assume (h: p -> q) (hnq: ¬ q),
show ¬ p, from
  assume hp: p,
  absurd (h hp) hnq

