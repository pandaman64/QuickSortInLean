import QuickSortInLean.Order
import QuickSortInLean.Vec
import Std.Data.Nat.Lemmas

theorem Fin.sub_isLt {n k : Nat} {i : Fin n} : i.val - k < n := Nat.lt_of_le_of_lt (Nat.sub_le ..) i.isLt

def partitionImpl {α : Type} [Ord α]
  {n : Nat} (arr : Vec α n) (first i j : Fin n)
  (fi : first ≤ i) (ij : i ≤ j) :
  { mid : Nat // first ≤ mid ∧ mid ≤ j } × Vec α n :=
  if h : first < i then
    have : first ≤ i.val - 1 := Nat.le_sub_one_of_lt h
    if arr[i] <o arr[first] then
      have : i.val - 1 ≤ j := Nat.le_trans (Nat.sub_le ..) ij
      partitionImpl arr first ⟨i - 1, Fin.sub_isLt⟩ j (by assumption) (by assumption)
    else
      let arr := (dbgTraceIfShared "swap1" arr).swap i j
      match partitionImpl arr first ⟨i - 1, Fin.sub_isLt⟩ ⟨j - 1, Fin.sub_isLt⟩ (by assumption) (Nat.sub_le_sub_right ij 1) with
      | (⟨mid, hm⟩, arr) => (⟨mid, ⟨hm.1, Nat.le_trans hm.2 (Nat.sub_le ..)⟩⟩, arr)
  else
    (⟨j, ⟨Nat.le_trans fi ij, by simp⟩⟩, arr)
termination_by _ => i.val

def partition {α : Type} [Ord α]
  {n : Nat} (arr : Vec α n) (first last : Fin n) (fl : first ≤ last) :
  { mid : Nat // first ≤ mid ∧ mid ≤ last } × Vec α n :=
  let result := partitionImpl arr first last last fl (Nat.le_refl _)
  let mid := result.1
  let arr := result.2
  ⟨mid, (dbgTraceIfShared "swap2" arr).swap first ⟨mid, Nat.lt_of_le_of_lt mid.property.2 last.isLt⟩⟩

theorem Nat.sub_add_eq_add_sub {m n k : Nat} (km : k ≤ m) : m - k + n = m + n - k := by
  induction km with
  | refl => simp [Nat.add_sub_cancel_left]
  | @step m km ih =>
    have : k ≤ m + n := Nat.le_trans km (Nat.le_add_right ..)
    simp [Nat.succ_sub km, Nat.succ_add, ih, Nat.succ_sub this]

theorem Nat.lt_sub_right {m n k : Nat} (mk : k ≤ m) (mn : m < n) : m - k < n - k := by
  show m - k + 1 ≤ n - k
  have : m - k + 1 = m + 1 - k := Nat.sub_add_eq_add_sub mk
  rw [this]
  apply Nat.sub_le_sub_right mn

def quickSortImpl {α : Type} [Ord α]
  {n : Nat} (arr : Vec α n) (first : Nat) (last : Fin n) :
  Vec α n :=
  if lt : first < last then
    let parted := partition arr ⟨first, Nat.lt_trans lt last.isLt⟩ last (Nat.le_of_lt lt)
    let mid := parted.1.val
    let hm := parted.1.property
    let arr := parted.2

    -- Lemmas
    have : mid - 1 - first < last - first := termination_lemma lt hm.1 hm.2
    have : last - (mid + 1) < last - first := Nat.sub_lt_sub_left lt (Nat.lt_of_le_of_lt hm.1 (Nat.lt_succ_self ..))
    have : mid - 1 < n := Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.lt_of_le_of_lt hm.2 last.isLt)

    -- Recursion
    let arr := quickSortImpl arr first ⟨mid - 1, by assumption⟩
    quickSortImpl arr (mid + 1) last
  else
    arr
where
  termination_lemma {mid : Nat} (lt : first < last) (hmid₁ : first ≤ mid) (hmid₂ : mid ≤ last) : mid - 1 - first < last - first := by
    cases Nat.decLt first mid with
    | isFalse h =>
      rw [Nat.not_lt] at h
      have : (1 + first) = (1 + mid) := congrArg (1 + ·) (Nat.le_antisymm hmid₁ h)
      rw [Nat.sub_sub, this, Nat.add_comm, Nat.sub_self_add]
      exact Nat.zero_lt_sub_of_lt lt
    | isTrue h =>
      have : first ≤ mid - 1 := Nat.le_sub_one_of_lt h
      have : mid - 1 < mid := Nat.pred_lt' h
      exact Nat.lt_sub_right (by assumption) (Nat.lt_of_lt_of_le (by assumption) hmid₂)
termination_by _ => last.val - first

def quickSort' {α : Type} [Ord α] {n : Nat} (arr : Vec α n) : Vec α n :=
  if _ : n > 0 then
    quickSortImpl arr 0 ⟨n - 1, Nat.sub_lt (by assumption) (by decide)⟩
  else
    arr

def quickSort {α : Type} [Ord α] (arr : Array α) : Array α :=
  (quickSort' (n := arr.size) arr).val

-- #eval quickSort #[7, 5, 6, 2, 8, 1, 9, 4, 10, 3]
-- #eval quickSort #[3, 4, 5, 2, 1, 5, 3, 2, 1, 4]
