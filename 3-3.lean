variables p q: Prop

#check p -> ¬ p
#check p -> q -> p ∧ q

example (hp: p) (hq: q): p ∧ q := and.intro hp hq
example (h: p ∧ q): p := and.elim_left h
example (h: p ∧ q): q := and.elim_right h
#check assume (h: p ∧ q), and.elim_left h

example (h: p ∧ q): q ∧ p := and.intro (and.right h) (and.left h)

#check assume (hp: p) (hq: q), (⟨hp, hq⟩: p ∧ q)

example (h: p ∧ q): q ∧ p := ⟨h.right, h.left⟩

example (h: p ∧ q): q ∧ p ∧ q := ⟨h.right, h.left, h.right⟩

example (hp: p): p ∨ q := or.intro_left q hp

#print or.elim

example (h: p ∨ q) : q ∨ p := 
  or.elim h
    (assume hp: p, or.inr hp)
    (assume hq: q, or.inl hq)

example (hpq: p -> q) (hnq: ¬ q) : ¬ p :=
  assume hp: p,
  show false, from hnq (hpq hp)

#print absurd
example (hp: p) (hnp: ¬ p) : q := absurd hp hnp

theorem and_swap: p ∧ q ↔ q ∧ p := ⟨ λ h, ⟨h.right, h.left⟩, λ h, ⟨h.right, h.left⟩ ⟩ 

example (h: p ∧ q) : q ∧ p := (and_swap p q).mp h

example (h: p ∧ q): q ∧ p :=
  have hp: p, from h.left,
  have hq: q, from h.right,
  ⟨hq, hp⟩
 
example (h: p ∧ q): q ∧ p :=
  have hp: p, from h.left,
  suffices hq: q, from ⟨hq, hp⟩,
  show q, from h.right
