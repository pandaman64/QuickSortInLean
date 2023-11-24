import QuickSortInLean.QuickSort
import QuickSortInLean.Permutation

theorem partitionImpl.induct {α : Type} [inst : LT α] [DecidableRel inst.lt] {n : Nat}
  (motive : (arr : Vec α n) → (first i j : Nat) → (fi : first ≤ i) → (ij : i ≤ j) → (jn : j < n) → Sort u)
  (arr : Vec α n) (first i j : Nat)
  (fi : first ≤ i) (ij : i ≤ j) (jn : j < n)
  (base : ∀arr first i j fi ij jn (_ : i < n) (_ : first < n) (_ : ¬first < i), motive arr first i j fi ij jn)
  (step_lt : ∀arr first i j fi ij jn
    (_ : i < n) (_ : first < n) (_ : first < i) (_ : first ≤ i - 1) (_ : arr[i] < arr[first]) (_ : i - 1 ≤ j)
    (_ : motive arr first (i - 1) j (by assumption) (by assumption) jn),
    motive arr first i j fi ij jn)
  (step_ge : ∀arr first i j fi ij jn
    (_ : i < n) (_ : first < n) (_ : first < i) (_ : first ≤ i - 1) (_ : ¬arr[i] < arr[first]) (_ : i - 1 ≤ j - 1) (_ : j - 1 < n)
    (_ : motive (arr.swap ⟨i, by assumption⟩ ⟨j, jn⟩) first (i - 1) (j - 1) (by assumption) (by assumption) (by assumption)),
    motive arr first i j fi ij jn)
  : motive arr first i j fi ij jn := by
  have : i < n := Nat.lt_of_le_of_lt ij jn
  have : first < n := Nat.lt_of_le_of_lt fi this
  if h : first < i then
    have : first ≤ i - 1 := Nat.le_sub_of_lt h
    if _ : arr[i] < arr[first] then
      have : i - 1 ≤ j := Nat.le_trans (Nat.sub_le ..) ij
      apply step_lt arr first i j fi ij jn
        (by assumption) (by assumption) h (by assumption) (by assumption)
      apply partitionImpl.induct motive
        arr first (i - 1) j
        (by assumption) (by assumption) jn
        base step_lt step_ge
    else
      have : i - 1 ≤ j - 1 := Nat.sub_le_sub_right ij 1
      have : j - 1 < n := Nat.lt_of_le_of_lt (Nat.sub_le ..) jn
      let arr' := arr.swap ⟨i, by assumption⟩ ⟨j, jn⟩
      apply step_ge arr first i j fi ij jn
        (by assumption) (by assumption) h (by assumption) (by assumption) (by assumption) (by assumption)
      apply partitionImpl.induct motive
        arr' first (i - 1) (j - 1)
        (by assumption) (by assumption) (by assumption)
        base step_lt step_ge
  else
    apply base arr first i j fi ij jn (by assumption) (by assumption) h

@[simp]
theorem partitionImpl.simp_base {α : Type} [inst : LT α] [DecidableRel inst.lt]
  {n : Nat} {arr : Vec α n} {first i j : Nat}
  {fi : first ≤ i} {ij : i ≤ j} {jn : j < n}
  (h : ¬first < i) :
  partitionImpl arr first i j fi ij jn =
  (⟨j, ⟨Nat.le_trans (by assumption) ij, by simp⟩⟩, arr.swap ⟨first, Nat.lt_of_le_of_lt fi (Nat.lt_of_le_of_lt ij jn)⟩ ⟨j, jn⟩) := by
  unfold partitionImpl
  simp [*, dbgTraceIfShared]

@[simp]
theorem partitionImpl.simp_step_lt {α : Type} [inst : LT α] [DecidableRel inst.lt]
  {n : Nat} {arr : Vec α n} {first i j : Nat}
  {fi : first ≤ i} {ij : i ≤ j} {jn : j < n}
  (h : first < i) (_ : arr[i]'(Nat.lt_of_le_of_lt ij jn) < arr[first]'(Nat.lt_of_le_of_lt fi (Nat.lt_of_le_of_lt ij jn))) :
  partitionImpl arr first i j fi ij jn = partitionImpl arr first (i - 1) j (Nat.le_sub_of_lt h) (Nat.le_trans (Nat.sub_le ..) ij) jn := by
  rw [partitionImpl]
  simp [*]

@[simp]
theorem partitionImpl.simp_step_ge {α : Type} [inst : LT α] [DecidableRel inst.lt]
  {n : Nat} {arr : Vec α n} {first i j : Nat}
  {fi : first ≤ i} {ij : i ≤ j} {jn : j < n}(h : first < i) (_ : ¬arr[i]'(Nat.lt_of_le_of_lt ij jn) < arr[first]'(Nat.lt_of_le_of_lt fi (Nat.lt_of_le_of_lt ij jn))) :
  partitionImpl arr first i j fi ij jn =
  match partitionImpl (arr.swap ⟨i, Nat.lt_of_le_of_lt ij jn⟩ ⟨j, jn⟩) first (i - 1) (j - 1)
    (Nat.le_sub_of_lt h) (Nat.sub_le_sub_right ij 1) (Nat.lt_of_le_of_lt (Nat.sub_le ..) jn) with
  | (⟨mid, hm⟩, arr) => (⟨mid, ⟨hm.1, Nat.le_trans hm.2 (Nat.sub_le ..)⟩⟩, arr) := by
  rw [partitionImpl]
  simp [*, dbgTraceIfShared]

theorem partitionImpl_permuted' {α : Type} [inst : LT α] [DecidableRel inst.lt]
  {n : Nat} (arr : Vec α n) (first i j : Nat)
  (fi : first ≤ i) (ij : i ≤ j) (jn : j < n) :
  permuted n arr (partitionImpl arr first i j fi ij jn).2 := by
  induction arr, first, i, j, fi, ij, jn using partitionImpl.induct with
  | base arr first i j fi ij jn =>
    simp [*]
    exact .step ⟨first, by assumption⟩ ⟨j, by assumption⟩ .refl
  | step_lt arr first i j fi ij jn _ _ _ _ _ _ ih =>
    simp [*]
    exact ih
  | step_ge arr first i j fi ij jn _ _ _ _ _ _ _ ih =>
    simp [*]
    apply permuted.step ⟨i, by assumption⟩ ⟨j, jn⟩ ih
