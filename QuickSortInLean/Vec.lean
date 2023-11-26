import Std.Data.Option.Basic
import Std.Data.Fin.Basic
import Std.Data.Array.Lemmas

/--
When proving termination and the safety of array operation, it's crucial to show
that each operation preserves the size of the array. Therefore, we encode the
size into the type using the Vec type.
-/
abbrev Vec (α : Type) (n : Nat) := { arr : Array α // arr.size = n }

instance : CoeDep (Array α) arr (Vec α arr.size) where
  coe := ⟨arr, by rfl⟩

def Vec.get (self : Vec α n) (i : Fin n) : α :=
  self.val.get ⟨i, by simp [self.property, i.isLt]⟩

instance : GetElem (Vec α n) (Fin n) α (fun _ _ => True) where
  getElem v i _ := v.get i

instance {α : Type} {n : Nat} : GetElem (Vec α n) Nat α (fun _ i => i < n) where
  getElem v i isLt := v.get ⟨i, isLt⟩

def Vec.set (self : Vec α n) (i : Fin n) (v : α) : Vec α n :=
  ⟨self.val.set ⟨i, by simp [self.property, i.isLt]⟩ v, by simp [self.property]⟩

def Vec.swap (self : Vec α n) (i j : Fin n) : Vec α n :=
  ⟨self.val.swap (i.cast self.property.symm) (j.cast self.property.symm), by simp [self.property]⟩

theorem Vec.get_set_eq (a : Vec α n) (i : Fin n) (v : α) :
  (a.set i v)[i] = v := by
  show (a.set i v).get i = v
  simp [Vec.get, Vec.set]

theorem Vec.get_set_ne (a : Vec α n) (i j : Fin n) (v : α) (h : i ≠ j) :
  (a.set i v)[j] = a[j] := by
  show (a.set i v).get j = a.get j
  simp [Vec.get, Vec.set]
  exact Array.get_set_ne (j := j.val) a.val ⟨i, by simp [a.property, i.isLt]⟩ v
    (by simp [a.property, j.isLt]) (Fin.val_ne_of_ne h)

theorem Vec.get_set (a : Vec α n) (i j : Fin n) (v : α) :
  (a.set i v)[j] = if i = j then v else a[j] := by
  if h : i = j then
    simp [h]
    exact Vec.get_set_eq a j v
  else
    simp [h]
    exact Vec.get_set_ne a i j v h

theorem Vec.swap_def (a : Vec α n) (i j : Fin n) :
  a.swap i j = (a.set i (a.get j)).set j (a.get i) := by
  simp [Vec.swap]
  apply Subtype.eq
  simp [Vec.get, Vec.set, Array.swap_def]
  rfl

theorem Vec.get_swap_left {α : Type} {n : Nat} (a : Vec α n) (i j : Fin n) :
  (a.swap i j)[i] = a[j] := by
  simp [Vec.swap_def, Vec.get_set, Vec.get_set_eq]
  cases decEq j i <;> simp [*] <;> rfl

theorem Vec.get_swap_right {α : Type} {n : Nat} (a : Vec α n) (i j : Fin n) :
  (a.swap i j)[j] = a[i] := by
  simp [Vec.swap_def, Vec.get_set_eq]
  rfl

theorem Vec.get_swap_neq {α : Type} {n : Nat} (a : Vec α n) (i j k : Fin n)
  (ki : k ≠ i) (kj : k ≠ j) :
  (a.swap i j)[k] = a[k] := by
  simp [Vec.swap_def]
  rw [Vec.get_set_ne (h := kj.symm), Vec.get_set_ne (h := ki.symm)]

theorem Vec.getElem_eq_getElem {α : Type} {n : Nat} (a : Vec α n) (i : Fin n) :
  a[i] = a.val[i.val]'(a.property.symm ▸ i.isLt) := by rfl
