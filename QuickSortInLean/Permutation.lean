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
inductive permuted {α : Type} (n first last : Nat) : Vec α n → Vec α n → Type where
  | refl : permuted n first last arr arr
  | step {arr arr'} (i j : Fin n) (fi : first ≤ i) (ij : i ≤ j) (jl : j ≤ last) :
    permuted n first last (arr.swap i j) arr' → permuted n first last arr arr'

def permuted.cast_first {α : Type} {n first last first' : Nat} {arr arr' : Vec α n}
  (self : permuted n first last arr arr') (h : first' ≤ first) :
  permuted n first' last arr arr' :=
  match self with
  | .refl => .refl
  | .step i j fi ij jl p => .step i j (Nat.le_trans h fi) ij jl (p.cast_first h)

def permuted.cast_last {α : Type} {n first last last' : Nat} {arr arr' : Vec α n}
  (self : permuted n first last arr arr') (h : last ≤ last') :
  permuted n first last' arr arr' :=
  match self with
  | .refl => .refl
  | .step i j fi ij jl p => .step i j fi ij (Nat.le_trans jl h) (p.cast_last h)

theorem permuted.trans : permuted n first last arr arr' → permuted n first last arr' arr'' → permuted n first last arr arr'' := by
  intro h
  induction h with
  | refl => intro; assumption
  | step i j fi ij jl _ ih =>
    intro h'
    exact permuted.step i j fi ij jl (ih h')

def permuted.to_map (p : permuted n first last arr arr') : Fin n → Fin n :=
  match p with
  | .refl => id
  | .step i j _ _ _ p' => fun k =>
    let k' :=
      if k = i then j
      else if k = j then i
      else k
    p'.to_map k'

theorem permuted_map_invertible (p : permuted n first last arr1 arr2) : invertible p.to_map := by
  induction p with
  | refl => simp [permuted.to_map, invertible_id]
  | step i j fi ij jl p ih =>
    let ⟨f', ⟨h1, h2⟩⟩ := ih
    let f := permuted.to_map (permuted.step i j fi ij jl p)
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

theorem permuted_map_index (p : permuted n first last arr1 arr2) (k : Fin n) :
  arr1[k] = arr2[p.to_map k] := by
  induction p generalizing k with
  | refl => simp [permuted.to_map]
  | step i j fi ij jl p ih =>
    simp [permuted.to_map]
    rw [←ih]
    split
    case step.inl ki => simp [ki, Vec.get_swap_right]
    case step.inr nki =>
      split
      case inl kj => simp [kj, Vec.get_swap_left]
      case inr nkj => rw [Vec.get_swap_neq _ i j k nki nkj]

theorem permuted_map_index_invertible {arr arr' : Vec α n} (p : permuted n first last arr arr') :
  ∃(f : Fin n → Fin n),
    invertible f ∧ (∀(i : Fin n), arr[i] = arr'[f i]) := by
  exists p.to_map
  apply And.intro
  . exact permuted_map_invertible p
  . intro i
    exact permuted_map_index p i

theorem permuted_map_index_in_range (p : permuted n first last arr1 arr2) (k : Fin n)
  (fk : first ≤ k) (kl : k ≤ last) :
  first ≤ p.to_map k ∧ p.to_map k ≤ last := by
  induction p generalizing k with
  | refl => simp [permuted.to_map, fk, kl]
  | step i j fi ij jl p ih =>
    simp [permuted.to_map]
    let k' := if k = i then j else if k = j then i else k
    have : first ≤ k'.val ∧ k'.val ≤ last := by
      match decEq k i, decEq k j with
      | isTrue ki, _ =>
        simp [ki]
        exact ⟨Nat.le_trans fi ij, jl⟩
      | isFalse ki, isTrue kj =>
        simp [ki]
        simp [kj]
        exact ⟨fi, Nat.le_trans ij jl⟩
      | isFalse ki, isFalse kj =>
        simp [ki, kj]
        exact ⟨fk, kl⟩
    exact ih k' this.1 this.2

theorem permuted_map_index_in_range_inv (p : permuted n first last arr1 arr2) (k : Fin n)
  (fk : first ≤ k) (kl : k ≤ last) :
  ∃k' : Fin n, p.to_map k' = k ∧ first ≤ k' ∧ k' ≤ last := by
  induction p generalizing k with
  | refl => simp [permuted.to_map, fk, kl]
  | step i j fi ij jl p ih =>
    simp [permuted.to_map]
    let ⟨k', ⟨index, fk', kl'⟩⟩ := ih k fk kl
    let k'' := if k' = i then j else if k' = j then i else k'
    exists k''

    have : (if k'' = i then j else if k'' = j then i else k'') = k' := by
      match decEq k' i, decEq k' j with
      | isTrue ki, _ => simp [ki]
      | _, isTrue kj => simp [kj]
      | isFalse ki, isFalse kj => simp [ki, kj]
    rw [this]

    have : first ≤ k''.val ∧ k''.val ≤ last := by
      match decEq k' i, decEq k' j with
      | isTrue ki, _ =>
        simp [ki]
        exact ⟨Nat.le_trans fi ij, jl⟩
      | isFalse ki, isTrue kj =>
        simp [ki]
        simp [kj]
        exact ⟨fi, Nat.le_trans ij jl⟩
      | isFalse ki, isFalse kj =>
        simp [ki, kj]
        exact ⟨fk', kl'⟩

    exact ⟨index, this.1, this.2⟩

theorem permuted.get_lt (p : permuted n first last arr1 arr2) {k : Fin n} (lt : k < first) :
  arr2[k] = arr1[k] := by
  induction p with
  | refl => rfl
  | step i j fi ij jl p ih =>
    rw [ih]
    rw [Vec.get_swap_neq _ i j k]
    . apply Fin.ne_of_val_ne
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le lt fi)
    . apply Fin.ne_of_val_ne
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le lt (Nat.le_trans fi ij))

theorem permuted.get_gt (p : permuted n first last arr1 arr2) {k : Fin n} (gt : last < k) :
  arr2[k] = arr1[k] := by
  induction p with
  | refl => rfl
  | step i j fi ij jl p ih =>
    rw [ih]
    rw [Vec.get_swap_neq _ i j k]
    . apply Fin.ne_of_val_ne
      exact Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.le_trans ij jl) gt)
    . apply Fin.ne_of_val_ne
      exact Nat.ne_of_gt (Nat.lt_of_le_of_lt jl gt)
