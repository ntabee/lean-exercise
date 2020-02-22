inductive parity: Type | E | O.

inductive even_or_odd: ℕ -> parity -> Prop
| even_zero : even_or_odd 0 parity.E
| even_succ : ∀ n, (even_or_odd n parity.O) -> even_or_odd (n+1) parity.E
| odd_succ : ∀ n, (even_or_odd n parity.E) -> even_or_odd (n+1) parity.O
