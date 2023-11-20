import QuickSortInLean.Permutation
import QuickSortInLean.QuickSort

theorem partitionImpl_permuted {α : Type} [Ord α]
  {n : Nat} (arr : Vec α n) (first i j : Nat)
  (fi : first ≤ i) (ij : i ≤ j) (jn : j < n) :
  permuted n arr (partitionImpl arr first i j fi ij jn).2 := by
  -- Constants
  have : first < n := Nat.lt_of_le_of_lt (Nat.le_trans fi ij) jn
  have : i < n := Nat.lt_of_le_of_lt ij jn
  have : i - 1 ≤ j - 1 := Nat.sub_le_sub_right ij 1
  have : j - 1 < n := Nat.lt_of_le_of_lt (Nat.sub_le ..) jn
  let i' : Fin n := ⟨i, by assumption⟩
  let j' : Fin n := ⟨j, jn⟩

  -- Proof
  unfold partitionImpl
  match Nat.decLt first i with
  | isTrue h =>
    have : first ≤ i - 1 := Nat.le_sub_of_lt h
    simp [h, dbgTraceIfShared]
    match hm : compare arr[i] arr[first] with
    | .lt =>
      simp [hm]
      apply partitionImpl_permuted
    | .eq | .gt =>
      simp [hm]
      show permuted n arr (partitionImpl (arr.swap i' j') first (i - 1) (j - 1) _ _ _).2
      let ih := partitionImpl_permuted (arr.swap i' j') first (i - 1) (j - 1) (by assumption) (by assumption) (by assumption)
      apply permuted.step i' j' ih
  | isFalse h =>
    simp [h, dbgTraceIfShared]
    exact .step ⟨first, by assumption⟩ j' .refl

theorem partition_permuted {α : Type} [Ord α]
  {n : Nat} (arr : Vec α n) (first last : Nat)
  (fl : first ≤ last) (ln : last < n) :
  permuted n arr (partition arr first last fl ln).2 := by
  apply partitionImpl_permuted

theorem quickSortImpl_permuted {α : Type} [Ord α]
  {n : Nat} (arr : Vec α n) (first last : Nat) (ln : last < n) :
  permuted n arr (quickSortImpl arr first last ln) := by
  unfold quickSortImpl
  match Nat.decLt first last with
  | isTrue h =>
    have : first ≤ last := Nat.le_of_lt h

    simp [h]
    sorry -- RAGE QUIT
  | isFalse h =>
    simp [h]
    exact .refl
termination_by _ => last - first

theorem quickSort'_permuted {α : Type} [Ord α] {n : Nat} (arr : Vec α n) :
  permuted n arr (quickSort' arr) := by
  simp [quickSort']
  match Nat.decLt 0 n with
  | isTrue h =>
    simp [h]
    apply quickSortImpl_permuted arr
  | isFalse h =>
    simp [h]
    exact .refl

theorem quickSort'_map_index_invertible {α : Type} [Ord α] {n : Nat} (arr : Vec α n):
  ∃f : Fin n → Fin n,
    invertible f ∧ (∀i : Fin n, arr[i] = (quickSort' arr)[f i]) := by
  let p := quickSort'_permuted arr
  exists p.to_map
  apply And.intro
  . exact permuted_map_invertible p
  . exact permuted_map_index p
