import QuickSortInLean.Permutation
import QuickSortInLean.QuickSort
import QuickSortInLean.Induction

theorem partitionImpl_permuted {α : Type} [Ord α]
  {n : Nat} (arr : Vec α n) (first i j : Fin n)
  (fi : first ≤ i) (ij : i ≤ j) :
  permuted n first j arr (partitionImpl arr first i j fi ij).2 := by
  induction arr, first, i, j, fi, ij using partitionImpl.induct with
  | base arr first i j fi ij jn =>
    simp [*]
    exact .refl
  | step_lt arr first i j fi ij _ _ _ _ ih =>
    simp [*]
    exact ih
  | step_ge arr first i j fi ij _ _ _ _ ih =>
    simp [*]
    apply permuted.step i j fi ij (Nat.le_refl _) (ih.cast_last (Nat.sub_le ..))

theorem partition_permuted {α : Type} [Ord α]
  {n : Nat} (arr : Vec α n) (first last : Fin n) (fl : first ≤ last) :
  permuted n first last arr (partition arr first last fl).2 := by
  let result := partition arr first last fl
  let mid := result.1
  simp [partition, dbgTraceIfShared]
  let p := partitionImpl_permuted arr first last last fl (Nat.le_refl _)
  exact permuted.trans p
    (.step first ⟨mid, Nat.lt_of_le_of_lt mid.property.2 last.isLt⟩ (Nat.le_refl _) mid.property.1 mid.property.2 .refl)

theorem quickSortImpl_permuted {α : Type} [Ord α]
  {n : Nat} (arr : Vec α n) (first : Nat) (last : Fin n) :
  permuted n first last arr (quickSortImpl arr first last) := by
  induction arr, first, last using quickSortImpl.induct with
  | base arr first last h =>
    simp [*]
    exact .refl
  | step arr first last lt parted eq ih₁ ih₂ =>
    simp [*]
    let p := partition_permuted arr ⟨first, Nat.lt_trans lt last.isLt⟩ last (Nat.le_of_lt lt)
    rw [eq] at p
    exact permuted.trans
      (permuted.trans p (ih₁.cast_last (Nat.le_trans (Nat.sub_le ..) parted.1.property.2)))
      (ih₂.cast_first (Nat.le_trans parted.1.property.1 (Nat.le_succ _)))

theorem quickSort'_permuted  {α : Type} [Ord α] {n : Nat} (arr : Vec α n) :
  permuted n 0 (n - 1) arr (quickSort' arr) := by
  simp [quickSort']
  match Nat.decLt 0 n with
  | isTrue h =>
    simp [h]
    apply quickSortImpl_permuted arr 0 ⟨n - 1, Nat.sub_lt_self (by decide) (Nat.zero_lt_of_lt h)⟩
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
