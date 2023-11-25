import QuickSortInLean.Permutation
import QuickSortInLean.QuickSort
import QuickSortInLean.Induction

theorem partitionImpl_permuted {α : Type} [Ord α]
  {n : Nat} (arr : Vec α n) (first i j : Nat)
  (fi : first ≤ i) (ij : i ≤ j) (jn : j < n) :
  permuted n arr (partitionImpl arr first i j fi ij jn).2 := by
  induction arr, first, i, j, fi, ij, jn using partitionImpl.induct with
  | base arr first i j fi ij jn =>
    simp [*]
    exact .refl
  | step_lt arr first i j fi ij jn _ _ _ _ _ _ ih =>
    simp [*]
    exact ih
  | step_ge arr first i j fi ij jn _ _ _ _ _ _ _ ih =>
    simp [*]
    apply permuted.step ⟨i, by assumption⟩ ⟨j, jn⟩ ih

theorem partition_permuted {α : Type} [Ord α]
  {n : Nat} (arr : Vec α n) (first last : Nat)
  (fl : first ≤ last) (ln : last < n) :
  permuted n arr (partition arr first last fl ln).2 := by
  let result := partition arr first last fl ln
  let mid := result.1
  simp [partition, dbgTraceIfShared]
  let p := partitionImpl_permuted arr first last last fl (Nat.le_refl _) ln
  exact permuted.trans p (.step ⟨first, Nat.lt_of_le_of_lt fl ln⟩ ⟨mid, Nat.lt_of_le_of_lt mid.property.2 ln⟩ .refl)

theorem quickSortImpl_permuted {α : Type} [Ord α]
  {n : Nat} (arr : Vec α n) (first last : Nat) (ln : last < n) :
  permuted n arr (quickSortImpl arr first last ln) := by
  induction arr, first, last, ln using quickSortImpl.induct with
  | base arr first last ln h =>
    simp [*]
    exact .refl
  | step arr first last ln lt parted eq ih₁ ih₂ =>
    simp [*]
    let p := partition_permuted arr first last (Nat.le_of_lt lt) ln
    rw [eq] at p
    exact permuted.trans (permuted.trans p ih₁) ih₂

theorem quickSort'_permuted  {α : Type} [Ord α] {n : Nat} (arr : Vec α n) :
  permuted n arr (quickSort' arr) := by
  simp [quickSort']
  match Nat.decLt 0 n with
  | isTrue h =>
    simp [h]
    apply quickSortImpl_permuted arr
  | isFalse h =>
    simp [h]
    exact .refl

theorem quickSort'_map_index_invertible  {α : Type} [Ord α] {n : Nat} (arr : Vec α n):
  ∃f : Fin n → Fin n,
    invertible f ∧ (∀i : Fin n, arr[i] = (quickSort' arr)[f i]) := by
  let p := quickSort'_permuted arr
  exists p.to_map
  apply And.intro
  . exact permuted_map_invertible p
  . exact permuted_map_index p
