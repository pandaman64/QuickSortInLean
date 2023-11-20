import QuickSortInLean.Vec

def isInv (f : α → β) (g : β → α) :=
  (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y)

def invertible (f : α → β) := ∃g, isInv f g

theorem invertible_id : invertible (id : α → α) := by
  have : isInv (id : α → α) id := by
    apply And.intro
    . intro x
      simp
    . intro y
      simp
  exact ⟨id, this⟩

-- Reflexive and transitive closure of arr ⇒ arr.swap i j
inductive permuted {α : Type} (n : Nat) : Vec α n → Vec α n → Type where
  | refl : permuted n arr arr
  | step {arr arr'} (i j : Fin n) : permuted n (arr.swap i j) arr' → permuted n arr arr'

theorem permuted.trans : permuted n arr arr' → permuted n arr' arr'' → permuted n arr arr'' := by
  intro h
  induction h with
  | refl => intro; assumption
  | step i j _ ih =>
    intro h'
    exact permuted.step i j (ih h')

def permuted.to_map (p : permuted n arr arr') : Fin n → Fin n :=
  match p with
  | .refl => id
  | .step i j p' => fun k =>
    let k' :=
      if k = i then j
      else if k = j then i
      else k
    p'.to_map k'

theorem permuted_map_invertible (p : permuted n arr1 arr2) : invertible p.to_map := by
  induction p with
  | refl => simp [permuted.to_map, invertible_id]
  | @step arr3 arr4 i j p ih =>
    let ⟨f', ⟨h1, h2⟩⟩ := ih
    let f := permuted.to_map (permuted.step i j p)
    show invertible f
    let g := fun (k : Fin n) =>
      let k' := f' k
      if k' = i then j
      else if k' = j then i
      else k'
    have gf : ∀x, g (f x) = x := by
      intro x
      simp (config := {zeta := false}) [f, permuted.to_map]
      cases decEq x i with
      | isFalse nxi =>
        cases decEq x j with
        | isFalse nxj => simp [nxi, nxj, g, h1]
        | isTrue xj => simp [nxi, xj, g, h1]
      | isTrue xi => simp [xi, g, h1]
    have fg : ∀y, f (g y) = y := by
      intro y
      simp (config := {zeta := false}) [g]
      show f (if f' y = i then j else if f' y = j then i else f' y) = y
      cases decEq (f' y) i with
      | isFalse nfyi =>
        cases decEq (f' y) j with
        | isFalse nfyj => simp [nfyi, nfyj, permuted.to_map, h2]
        | isTrue fyj =>
          simp [nfyi, fyj, permuted.to_map]
          rw [←(congrArg p.to_map fyj), h2]
      | isTrue fyi =>
        simp [fyi, permuted.to_map]
        have : (if j = i then j else i) = i := by simp
        rw [this, ←(congrArg p.to_map fyi), h2]
    exact ⟨g, ⟨gf, fg⟩⟩

theorem permuted_map_index (p : permuted n arr1 arr2) (k : Fin n) :
  arr1[k] = arr2[p.to_map k] := by
  induction p generalizing k with
  | refl => simp [permuted.to_map]
  | @step arr3 arr4 i j p ih =>
    simp [permuted.to_map]
    rw [←ih]
    split
    case step.inl ki => simp [ki, Vec.get_swap_right]
    case step.inr nki =>
      split
      case inl kj => simp [kj, Vec.get_swap_left]
      case inr nkj => rw [Vec.get_swap_neq arr3 i j k nki nkj]

theorem permuted_map_index_invertible {arr arr' : Vec α n} (p : permuted n arr arr') :
  ∃(f : Fin n → Fin n),
    invertible f ∧ (∀(i : Fin n), arr[i] = arr'[f i]) := by
  exists p.to_map
  apply And.intro
  . exact permuted_map_invertible p
  . intro i
    exact permuted_map_index p i
