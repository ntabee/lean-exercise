universe u
namespace hidden

inductive list (α : Type u)
| nil {} : list
| cons : α → list → list

namespace list

notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

variable {α : Type}

notation h :: t  := cons h t

def append: list α -> list α -> list α
| nil t := t
| (h::s) t := h::(append s t)
.

notation s ++ t := append s t

theorem nil_append (t : list α) : nil ++ t = t := rfl

theorem cons_append (x : α) (s t : list α) : x::s ++ t = x::(s ++ t) := rfl

theorem append_nil : ∀ (t : list α), t ++ nil = t
| nil := rfl
| (h::t) := by simp[append_nil t, cons_append]
.

theorem append_assoc (s t: list α): ∀(r: list α), r ++ s ++ t = r ++ (s ++ t)
| nil := rfl
| (h::r) := by simp[cons_append, append_assoc r]
.

def length: list α -> nat
| nil := 0
| (h::t) := 1 + (length t)
.
#reduce length nil
#reduce length [5]
#reduce length [1, 3, 5, 7, 9]

def reverse: list α -> list α
| nil := nil
| (h::t) := (reverse t) ++ [h]
.
#reduce reverse nil
#reduce reverse [5]
#reduce reverse [1, 3, 5, 7, 9]

lemma len_nil: length (nil: list α) = 0 := rfl.
lemma len_cons (h: α) (t: list α): length(h::t) = 1 + (length t) := by rsimp.
lemma len_cons_append (h: α) (t: list α): ∀(s: list α), (length ((h::s) ++ t)) = length (h::(s++t))
| nil := rfl
| (h2::s) := rfl
.

theorem len_append (t: list α): ∀ (s: list α), length(s++t) = (length s) + (length t)
| nil := by simp [nil_append, len_nil]
| (h::s) := begin
  simp [len_cons],
  rw [add_comm (length t), <-len_append s],
  simp [len_cons_append, len_cons]
end

lemma rev_cons (h: α) (t: list α): reverse (h::t) = (reverse t)++[h] := rfl
theorem len_rev: ∀(t: list α), length t = length (reverse t)
| nil := rfl
| (h::t) := begin
  simp [len_cons, rev_cons],
  simp [len_append],
  simp [len_rev t, len_cons, len_nil],
end

lemma rev_nil_s (s: list α): reverse(nil ++ s) = reverse s := rfl.
lemma rev_s_nil: ∀ (s: list α), reverse(s++nil) = reverse s
| nil := rfl
| (h::s) := by rw [rev_cons, <-rev_s_nil s]; reflexivity.
lemma rev_nil: reverse (nil: list α) = nil := rfl.

lemma rev_append (t: list α): ∀ (s: list α), reverse (s++t) = (reverse t) ++ (reverse s)
| nil := by simp[rev_nil, rev_nil_s, append_nil]
| (h::s) := begin
  simp [rev_cons],
  rw [<-append_assoc, <-rev_append s],
  rw [<-rev_cons],
  reflexivity
end

theorem rev_rev: ∀ (t: list α), reverse (reverse t) = t
| nil := rfl
| (h::t) := begin
  simp [rev_cons, rev_append, rev_rev t], reflexivity
end

end list

end hidden