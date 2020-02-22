inductive t: Type
| const : bool -> t
| var : ℕ -> t
| and : t -> t -> t
| or : t -> t -> t
| not : t -> t

def bn := ℕ × t.
def env := list bn.

def lookup: env -> nat -> t
| [] x := t.var x
| ((y,v)::ys) x := if x = y then v else lookup ys x

def t_and: t -> t -> t
| (t.const a) (t.const b) := t.const (a ∧ b)
| u v := t.and u v

def t_or: t -> t -> t
| (t.const a) (t.const b) := t.const (a ∨ b)
| u v := t.or u v

def t_not: t -> t
| (t.const a) := t.const (¬ a)
| u := t.not u

infix `<|>`:50 := t_or
infix `<&>`:70 := t_and

def subst : env -> t -> t
| _ (t.const v) := t.const v
| e (t.var x) := lookup e x
| e (t.and u v) := t.and (subst e u) (subst e v)
| e (t.or u v) := t.or (subst e u) (subst e v)
| e (t.not u) := t_not (subst e u)
.

def atomic : t -> t
| (t.const v) := t.const v
| (t.not v) := t_not v
| u := u

def reduce : env -> t -> t
| _ (t.const v) := t.const v
| e (t.var x) := atomic (lookup e x)
| e (t.and u v) := (reduce e u) <&> (reduce e v)
| e (t.or u v) := (reduce e u) <|> (reduce e v)
| e (t.not u) := t_not (reduce e u)
.

def T := t.const tt
def F := t.const ff
def x₁ := t.var 1
def x₂ := t.var 2
def x₃ := t.var 3
def x₄ := t.var 4

#reduce reduce [] (t.const tt)
#reduce reduce [] (t.var 1)

#reduce reduce [(1, T)] (t.var 1)
#reduce subst  [(1, T)] (t.var 1)

#reduce reduce [(1, T), (2, T)] (x₁ <&> x₂)
#reduce reduce [(1, F), (2, T)] (x₁ <&> x₂)
#reduce reduce [(1, F), (2, T)] (x₁ <|> x₂)
#reduce reduce [(1, F), (2, F)] (x₁ <|> x₂)

#reduce reduce [(1, x₃ <|> x₄), (2, T)] (x₁ <&> x₂)
#reduce subst  [(1, x₃ <|> x₄), (2, T)] (x₁ <&> x₂)
#reduce reduce [(3, F), (4, F)] (subst  [(1, x₃ <|> x₄), (2, T)] (x₁ <&> x₂))
#reduce reduce [(3, F), (4, t.not F)] (subst  [(1, x₃ <|> x₄), (2, T)] (x₁ <&> x₂))