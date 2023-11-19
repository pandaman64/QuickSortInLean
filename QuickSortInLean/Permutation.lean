import QuickSortInLean.QuickSort
import Std.Data.Option.Basic
import Std.Data.Fin.Basic
import Std.Data.Array.Lemmas

-- Reflexive and transitive closure of arr ⇒ arr.swap i j
inductive permuted : Array α → Array α → Type where
  | refl : permuted arr arr
  | step {arr arr'} (i j : Fin arr.size) : permuted (arr.swap i j) arr' → permuted arr arr'

-- theorem permuted_trans : permuted arr arr' → permuted arr' arr'' → permuted arr arr'' := by
--   intro p
--   induction p with
--   | refl => intro; assumption
--   | step _ ih =>
--     intro q
--     exact .step (ih q)

-- NOTE: somehow we need to write ∃_ : permuted arr arr', True instead of permuted arr arr'.
-- Otherwise, split tactic will not work.
theorem partition'_permutation [Ord α] :
  (partition' (arr : Array α) i j last ij jl la).2 = arr' → ∃_ : permuted arr arr', True := by
  unfold partition'
  split <;> simp [dbgTraceIfShared]
  case inl jl =>
    split
    -- | .lt | .eq
    case h_1 | h_2 =>
      intro eq
      let ⟨ih, _⟩ := partition'_permutation eq
      exact ⟨.step _ _ ih, trivial⟩
    -- | .gt
    case h_3 =>
      intro eq
      exact partition'_permutation eq
  case inr _ =>
    intro eq
    rw [←eq]
    exact ⟨.step _ _ .refl, trivial⟩
termination_by partition'_permutation α arr i j last ij jl la result ord => last - j

theorem partition_permutation [Ord α] :
  (partition (arr : Array α) first last jl la).2 = arr' → ∃_ : permuted arr arr', True := by
    simp [partition]
    exact partition'_permutation

-- TODO: It's really hard to see through the definition of quickSort'.
theorem quickSort'_permutation [Ord α] :
  (quickSort' (arr : Array α) first last la).val = arr' → ∃_ : permuted arr arr', True := by
  sorry

theorem quickSort_permutation [Ord α] :
  (quickSort (arr : Array α)) = arr' → ∃_ : permuted arr arr', True := by
  simp [quickSort]
  split
  case inl => exact quickSort'_permutation
  case inr =>
    intro eq
    rw [eq]
    exact ⟨.refl, trivial⟩

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

def permuted.to_map (p : permuted arr arr') : Fin arr.size → Fin arr'.size :=
  match p with
  | .refl => id
  | .step i j p' => fun k =>
    have h : arr.size = (arr.swap i j).size := by simp
    let k' :=
      if k.val = i.val then j
      else if k.val = j.val then i
      else k
    p'.to_map (k'.cast h)

theorem permuted_size (p : permuted arr arr') : arr'.size = arr.size := by
  induction p with
  | refl => rfl
  | step _ _ _ ih =>
    simp at ih
    exact ih

theorem Fin.cast_eq_val {n m : Nat} (h : n = m) (i : Fin n) : (i.cast h).val = i.val := by
  simp [Fin.cast]

theorem Fin.eq_ite {n : Nat} (i j : Fin n) :
  (if j.val = i.val then j else i) = i := by
  cases Nat.decEq j.val i.val with
  | isFalse h => simp [*]
  | isTrue h => simp [*, Fin.eq_of_val_eq h]

theorem permuted_map_invertible (p : permuted arr1 arr2) : invertible p.to_map := by
  induction p with
  | refl => simp [permuted.to_map, invertible_id]
  | @step arr3 arr4 i j p ih =>
    have size_s3 : (arr3.swap i j).size = arr3.size := by simp
    let ⟨f', ⟨h1, h2⟩⟩ := ih
    let f := permuted.to_map (permuted.step i j p)
    show invertible f
    let g := fun (k : Fin arr4.size) =>
      let k := (f' k).cast size_s3
      -- let k := (f' (f (k.cast size_43))).cast size_s3
      if k.val = i.val then j
      else if k.val = j.val then i
      else k
    have gf : ∀x, g (f x) = x := by
      intro x
      simp (config := {zeta := false}) [f, permuted.to_map]
      cases Nat.decEq x.val i.val with
      | isFalse nxi =>
        cases Nat.decEq x.val j.val with
        | isFalse nxj =>
          simp (config := {zeta := false}) [nxi, nxj, g]
          rw [h1]
          simp [Fin.cast, nxi, nxj]
        | isTrue xj =>
          simp (config := {zeta := false}) [nxi, xj, Fin.eq_ite, g]
          rw [h1]
          simp [Fin.cast]
          exact Fin.eq_of_val_eq xj.symm
      | isTrue xi =>
        simp (config := {zeta := false}) [xi, g]
        rw [h1]
        simp [Fin.cast, Fin.eq_ite]
        exact Fin.eq_of_val_eq xi.symm
    have fg : ∀y, f (g y) = y := by
      intro y
      simp (config := {zeta := false}) [g]
      let k : Fin arr3.size := (f' y).cast size_s3
      show f (if k.val = i.val then j else if k.val = j.val then i else k) = y
      cases Nat.decEq k.val i.val with
      | isFalse nki =>
        cases Nat.decEq k.val j.val with
        | isFalse nkj =>
          simp [nki, nkj, permuted.to_map]
          -- Consective Fin.cast cancel each other
          show p.to_map (f' y) = y
          apply h2
        | isTrue kj =>
          simp [nki, kj, permuted.to_map,Fin.eq_ite]
          have : j = k := Fin.eq_of_val_eq kj.symm
          simp [this]
          show permuted.to_map p (f' y) = y
          apply h2
      | isTrue ki =>
        simp [ki, permuted.to_map, Fin.eq_ite]
        have : i = k := Fin.eq_of_val_eq ki.symm
        simp [this]
        show permuted.to_map p (f' y) = y
        apply h2
    exact ⟨g, ⟨gf, fg⟩⟩

theorem Option.sum_inj {a b : α} : some a = some b → a = b := by simp

theorem getElem?_some_getElem (arr : Array α) (i : Nat) (eq : arr[i]? = some v) :
  ∃h : i < arr.size, arr[i] = v := by
  simp [getElem?] at eq
  cases Nat.decLt i arr.size with
  | isFalse h => simp [h] at eq
  | isTrue h =>
    simp [h] at eq
    exact ⟨h, eq⟩

theorem Array.eq_get_swap_left (arr : Array α) (i j : Fin arr.size) (h : arr.size = (arr.swap i j).size) :
  arr[i] = (arr.swap i j)[j.cast h] := by
  show arr[i] = (arr.swap i j)[(j.cast h).val]
  have : (arr.swap i j)[(j.cast h).val]? = some arr[i.val] := by
    rw [Array.get?_swap arr i j (j.cast h).val, Fin.cast_eq_val]
    simp
  let ⟨_, eq⟩ := getElem?_some_getElem _ _ this
  simp [*]

theorem Array.eq_get_swap_right (arr : Array α) (i j : Fin arr.size) (h : arr.size = (arr.swap i j).size) :
  arr[j] = (arr.swap i j)[i.cast h] := by
  show arr[j] = (arr.swap i j)[(i.cast h).val]
  have : (arr.swap i j)[(i.cast h).val]? = some arr[j.val] := by
    rw [Array.get?_swap arr i j (i.cast h).val, Fin.cast_eq_val]
    simp
    intro eq
    have : j = i := Fin.eq_of_val_eq eq
    rw [this]
  let ⟨_, eq⟩ := getElem?_some_getElem _ _ this
  simp [*]

theorem Array.eq_get_swap_neq (arr : Array α) (i j k : Fin arr.size) (h : arr.size = (arr.swap i j).size) :
  i ≠ k → j ≠ k → arr[k] = (arr.swap i j)[k.cast h] := by
  intro ik jk
  have ikv : i.val ≠ k.val := by
    intro eq
    exact ik <| Fin.eq_of_val_eq eq
  have jkv : j.val ≠ k.val := by
    intro eq
    exact jk <| Fin.eq_of_val_eq eq
  show arr[k] = (arr.swap i j)[(k.cast h).val]
  have : (arr.swap i j)[(k.cast h).val]? = some arr[k.val] := by
    rw [Array.get?_swap arr i j (k.cast h).val, Fin.cast_eq_val]
    simp [ikv, jkv, getElem?, k.isLt]
  let ⟨_, eq⟩ := getElem?_some_getElem _ _ this
  simp [*]

theorem permuted_map_index (p : permuted arr1 arr2) (k : Fin arr1.size) :
  arr1[k] = arr2[p.to_map k] := by
  induction p with
  | refl => simp [permuted.to_map]
  | @step arr3 arr4 i j p ih =>
    simp [permuted.to_map]
    simp at ih
    split
    case step.inl eq =>
      have : arr3[k.val] = arr3[i.val] := by simp [eq]
      rw [this]
      have : arr3.size = (arr3.swap i j).size := by simp
      rw [←ih]
      exact Array.eq_get_swap_left arr3 i j this
    case step.inr neq =>
      split
      case inl eq =>
        have : arr3[k.val] = arr3[j.val] := by simp [eq]
        rw [this]
        have : arr3.size = (arr3.swap i j).size := by simp
        rw [←ih]
        exact Array.eq_get_swap_right arr3 i j this
      case inr neq' =>
        have : arr3.size = (arr3.swap i j).size := by simp
        rw [←ih]
        have neq : i ≠ k := by
          intro eq
          apply neq
          simp [eq]
        have neq' : j ≠ k := by
          intro eq
          apply neq'
          simp [eq]
        exact Array.eq_get_swap_neq arr3 i j k this neq neq'

theorem permuted_map_index_invertible {arr arr' : Array α} (p : permuted arr arr') :
  ∃(f : Fin arr.size → Fin arr'.size),
    invertible f ∧ (∀(i : Fin arr.size), arr[i] = arr'[f i]) := by
  exists p.to_map
  apply And.intro
  . exact permuted_map_invertible p
  . intro i
    exact permuted_map_index p i

theorem quickSort_map_index_invertible {arr arr' : Array α} [Ord α] :
  quickSort arr = arr' →
  ∃f : Fin arr.size → Fin arr'.size,
    invertible f ∧ (∀i : Fin arr.size, arr[i] = arr'[f i]) := by
  intro eq
  let ⟨p, _⟩ := quickSort_permutation eq
  exact permuted_map_index_invertible p
