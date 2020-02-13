-- https://leanprover.github.io/theorem_proving_in_lean/propositions_and_proofs.html#exercises
open classical

variables p q r s : Prop

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
assume (h: p -> r ∨ s),
by_cases (
  assume hp: p,
  have hrs: r ∨ s, from h hp,
  hrs.elim (λ hr: r, or.inl (λ hp: p, hr)) (λ hs: s, or.inr (λ hp:p, hs))
) (
  assume hnp: ¬ p,
  have hpr: p -> r, from (λ hp: p, absurd hp hnp),
  or.inl hpr
)

example : ¬(p ∧ q) → ¬p ∨ ¬q := 
assume (h: ¬ (p ∧ q)),
by_cases (
  assume hp: p,
  have hnq: ¬ q, from 
    assume hq: q, h ⟨hp, hq⟩,
  or.inr hnq
) (
  assume hnp: ¬ p,
  or.inl hnp
)

lemma dne {p: Prop} (h: ¬ ¬ p) : p := 
or.elim (em p)
  (assume hp: p, hp)
  (assume hnp: ¬ p, absurd hnp h)

lemma L : ¬(p → q) → p ∧ ¬q := 
assume h: ¬ (p -> q),
by_contradiction (
  assume h': ¬ (p ∧ ¬ q),
  have h'': p -> (¬ q) -> false, from λ (hp) (hnq), h' ⟨hp, hnq⟩,
  show false, from h (
    show p -> q, from 
    assume hp: p,
    dne (h'' hp)
  )
)
example : ¬(p → q) → p ∧ ¬q := L p q

example : (p → q) → (¬p ∨ q) := 
assume h: p -> q,
by_cases (λ hp, or.inr (h hp)) (λ hnp, or.inl hnp)

example : (¬q → ¬p) → (p → q) := 
assume h: ¬ q -> ¬ p,
by_cases (
  assume hnq: ¬ q,
  have hnp: ¬ p, from h hnq,
  λ hp, absurd hp hnp
) (
  assume hnnq: ¬ ¬ q,
  have hq: q, from dne hnnq,
  λ hp, hq
)

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) := 
assume h: (p -> q) -> p,
show p, from
by_cases (
  assume hpq: p -> q, h hpq
) (
  assume hnpq: ¬ (p -> q),
  have hpnq: p ∧ ¬ q, from L p q hnpq,
  hpnq.left
)
