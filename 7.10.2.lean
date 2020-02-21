universe u
namespace hidden

inductive list (α : Type u)
| nil {} : list
| cons : α → list → list

namespace list

notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

variable {α : Type}

notation h :: t  := cons h t

def append (s t : list α) : list α :=
list.rec_on s t (λ x l u, x::u)

notation s ++ t := append s t

theorem nil_append (t : list α) : nil ++ t = t := rfl

theorem cons_append (x : α) (s t : list α) : x::s ++ t = x::(s ++ t) := rfl

-- BEGIN
theorem append_nil (t : list α) : t ++ nil = t := 
list.rec_on t (
  nil_append nil
) (
  λ h l,
  assume ih: (append l nil = l),
  calc append (h::l) nil = h::(append l nil): cons_append h l nil
    ... = h::l: by rw ih
)

theorem append_assoc (r s t : list α) :
  r ++ s ++ t = r ++ (s ++ t) := 
list.rec_on r (
    by simp [nil_append (s++t), nil_append s]
) (
  λ h r,
  assume ih: r ++ s ++ t = r ++ (s ++ t),
  calc (h::r) ++ s ++ t = h::(r ++ s ++ t): cons_append h (r++s) t
    ... = h::(r ++ (s++t)): by rw ih
)
-- END

def length (l: list α): nat := list.rec_on l 0 (λ _ _ a, 1+a)
#reduce length nil
#reduce length [5]
#reduce length [1, 3, 5, 7, 9]

def reverse (l: list α): list α := list.rec_on l nil (λ h _ a, a ++ [h])
#reduce reverse nil
#reduce reverse [5]
#reduce reverse [1, 3, 5, 7, 9]

lemma len_nil: length (nil: list α) = 0 := rfl.
lemma len_cons (h: α) (t: list α): length(h::t) = 1 + (length t) := by rsimp.
lemma len_cons_append (h: α) (s t: list α): (length ((h::s) ++ t)) = length (h::(s++t)) := begin
induction s, rsimp,
case list.cons: x s ih {
  rw cons_append,
}
end

theorem len_append (s: list α) (t: list α): length(s++t) = (length s) + (length t) := begin
induction s, 
case list.nil: {
  rw [nil_append, len_nil, nat.add_comm, nat.add_zero]
},
case list.cons: h s ih {
  rw [len_cons, nat.add_assoc],
  rw <-ih,
  rw [len_cons_append, len_cons]
}
end

lemma rev_cons (h: α) (t: list α): reverse (h::t) = (reverse t)++[h] := begin
induction t, reflexivity,
case list.cons: x t ih {
  repeat {rw reverse},
}
end
theorem len_rev (t: list α): length t = length (reverse t) := begin
induction t, reflexivity,
case list.cons: h t ih {
  rw [rev_cons, len_append, len_cons, len_cons, ih],
  rw len_nil,
  simp [nat.add_assoc, nat.add_comm], 
}
end

lemma rev_nil_s (s: list α): reverse(nil ++ s) = reverse s := rfl.
lemma rev_s_nil (s: list α): reverse(s++nil) = reverse s := begin
induction s, reflexivity,
case list.cons: h s ih {
  rw rev_cons, rw <- ih, reflexivity,
}
end
lemma rev_nil: reverse (nil: list α) = nil := rfl.

lemma rev_append (s t: list α): reverse (s++t) = (reverse t) ++ (reverse s) := begin
induction s, { rw [rev_nil_s, rev_nil, append_nil] },
case list.cons: h s ih {
  rw rev_cons,
  rw <-append_assoc,
  rw <-ih,
  rw <-rev_cons,
  reflexivity,
}
end

theorem rev_rev (t: list α): reverse (reverse t) = t := begin
induction t, reflexivity,
case list.cons: h t ih {
  rw rev_cons,
  rw [rev_append, ih],
  rw [rev_cons, rev_nil, nil_append],
  reflexivity,
}
end

end list

end hidden