universe u

inductive vector (α : Type u) : nat → Type u
| nil {} : vector 0
| cons   : Π {n}, α → vector n → vector (n+1)

namespace vector
local notation h :: t := cons h t

#check @vector.cases_on
-- Π {α : Type}
--   {C : Π (a : ℕ), vector α a → Type}
--   {a : ℕ}
--   (n : vector α a),
--   (e1 : C 0 nil)
--   (e2 : Π {n : ℕ} (a : α) (a_1 : vector α n),
--           C (n + 1) (cons a a_1)),
--   C a n

def vap_cons {α: Type}: Π {n: nat}, α → vector α n → vector α (n+1)
| 0 h nil := cons h nil
| (n+1) h (h2::t) := h::(vap_cons h2 t)

def to_l {α : Type} {n: nat} (v: vector α n): { l : list α // l.length = n} := begin
induction n, exact ⟨[], rfl⟩,
case nat.succ: n ih {
  cases v with α h t,
  let l1 := (ih t),
  let l2 := list.cons h l1.val,
  have: list.length l2 = n + 1, by {
    simp [list.length_cons l2],
    rw [l1.2, nat.add_comm],
  },
  exact ⟨l2, this⟩ 
}
end

lemma nat_add_eq_eq (a b c: nat) (h: a + c = b + c): a = b := begin
induction c, exact h,
case nat.succ: c ih {
  simp [nat.add_succ] at h,
  exact (ih h)
}
end

def from_l {α : Type}: Π {n: nat}, { l: list α // l.length = n} -> vector α n
| 0 ⟨[], _⟩ := nil
| (n+1) ⟨list.cons h t, p⟩ := begin
  have: list.length t = n, by {
    rw [list.length_cons h t] at p,
    rw [nat_add_eq_eq (list.length t) n 1],
    assumption,
  },
  exact (h::(from_l ⟨t, this⟩))
end

theorem triv (m n: nat): m + n + 1 = m + 1 + n := by simp[add_comm]

def vappend {α : Type} : Π {m n}, vector α m -> vector α n -> vector α (m+n)
| 0 0 nil nil := nil
| m 0 v nil := v
| 0 (n+1) nil (h::v) := h::(vappend nil v)
| (m+1) n (h::u) v := 
  let l := to_l (h::(vappend u v)) in
  let l': { l : list α // list.length l = (m+1+n) } := ⟨l.1, (triv m n) ▸ l.2⟩ in
  from_l l'
.
end vector