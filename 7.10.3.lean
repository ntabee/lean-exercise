inductive t: Type
| const : ℕ -> t
| var : ℕ -> t
| plus : t -> t -> t
| times : t -> t -> t

def bn := ℕ × ℕ.
def env := list bn.
def val := option ℕ

def lookup: env -> nat -> val
| [] _ := none
| ((y,v)::ys) x := if x = y then some v else lookup ys x

def bin: (ℕ -> ℕ -> ℕ) -> val -> val -> val
| _ none _ := none
| _ _ none := none
| op (some x) (some y) := some (op x y)

def add := bin nat.add
def mul := bin nat.mul

infix `<+>`:50 := add
infix `<*>`:70 := mul

def eval : env -> t -> val
| _ (t.const v) := some v
| e (t.var x) := lookup e x
| e (t.plus u v) := (eval e u) <+> (eval e v)
| e (t.times u v) := (eval e u) <*> (eval e v).

def tplus (u: t) (v: t): t := t.plus u v
def ttimes (u: t) (v: t): t := t.times u v
infix `[+]`:50 := tplus
infix `[*]`:70 := ttimes

def x₁ := t.var 1
def x₂ := t.var 2
def x₃ := t.var 3
def x₄ := t.var 4

#reduce eval [] (t.const 1)
#reduce eval [] (t.var 1)
#reduce eval [(1, 100)] (t.var 1)
#reduce eval [(1, 1), (2, 12)] ((x₁[*]x₁[*]x₁) [+] (x₂[*]x₂[*]x₂))
#reduce eval [(1, 9), (2, 10)] ((x₁[*]x₁[*]x₁) [+] (x₂[*]x₂[*]x₂))
#reduce eval [(3, 0), (2, 9), (1, 10)] ((x₁[*]x₁[*]x₁) [+] (x₂[*]x₂[*]x₂))
#reduce eval [(3, 0), (1, 10)] ((x₁[*]x₁[*]x₁) [+] (x₂[*]x₂[*]x₂))
