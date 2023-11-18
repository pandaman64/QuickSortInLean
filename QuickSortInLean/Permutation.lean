class Interp (n : Nat) (α : Type) where
  interp (self : α) : Fin n → Fin n

structure Transposition (n : Nat) where
  i : Fin n
  j : Fin n

def Transposition.interp (t : Transposition n) : Fin n → Fin n
  | k =>
    if k = t.i then t.j
    else if k = t.j then t.i
    else k

instance : Interp n (Transposition n) where
  interp := Transposition.interp

abbrev Permutation (n : Nat) := List (Transposition n)

def Permutation.interp (p : Permutation n) : Fin n → Fin n :=
  match p with
  | [] => id
  | t :: ts => t.interp ∘ Permutation.interp ts

instance : Interp n (Permutation n) where
  interp := Permutation.interp

notation:max " 〚 " x " 〛 " => Interp.interp x
infix:60 " ↔ " => Transposition.mk

-- #check 〚[0 ↔ 1, 3 ↔ 5]〛

theorem Permutation.interp_id : (〚([] : Permutation n)〛 : Fin n → Fin n)= id :=
  rfl

theorem Permutation.interp_cons
  (t : Transposition n) (ts : Permutation n)
  : 〚(t :: ts)〛 = 〚t〛 ∘ (〚ts〛 : Fin n → Fin n) := rfl

theorem Permutation.homomorphism :
  ∀ (p q : Permutation n), (〚p ++ q〛 : Fin n → Fin n) = 〚p〛 ∘ 〚q〛 := by
  intro p
  induction p with
  | nil =>
    intro q
    simp [Permutation.interp_id]
    rfl
  | cons t ts ih =>
    intro q
    simp [Permutation.interp, Permutation.interp_cons, ih]
    rfl
