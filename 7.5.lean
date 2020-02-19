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

end list

end hidden