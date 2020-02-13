namespace hidden

constant and: Prop -> Prop -> Prop
constant or: Prop -> Prop -> Prop
constant not: Prop -> Prop
constant implies: Prop -> Prop -> Prop 

constant Proof: Prop -> Type

variables p q r: Prop

constant and_comm: ∀ p q: Prop,
  Proof (implies (and p q) (and q p))
#check and_comm p q

constant modus_ponens: ∀ p q: Prop, Proof (implies p q) -> Proof p -> Proof q
constant implies_intro: ∀ p q: Prop, (Proof p -> Proof q) -> Proof (implies p q)

end hidden

namespace hidden
constants p q: Prop 

theorem t1: p -> q -> p := λ (hp: p) (hq: q), hp

theorem t1': p -> q -> p :=
  assume hp: p,
  assume hq: q,
  hp

theorem t1'': p -> q -> p :=
  assume hp: p,
  assume hq: q,
  show p, from hp

axiom ap : p 

theorem t2: q -> p := t1 ap

theorem t1''': ∀ {p q: Prop}, p -> q -> p :=
  assume p q,
  assume hp: p,
  assume hq: q,
  hp
end hidden

theorem t1: ∀ (p q: Prop), p -> q -> p :=
  assume p q,
  assume hp: p,
  assume hq: q,
  hp

variables p q r s: Prop 
#check t1
#check t1 p q
#check t1 r s
#check t1 (r -> s) (s -> r)

theorem t2 (h₁: q -> r) (h₂: p -> q): p -> r :=
  assume h₃: p,
  show r, from h₁ (h₂ h₃)

#check t2
