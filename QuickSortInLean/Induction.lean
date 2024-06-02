import QuickSortInLean.QuickSort

def partitionImpl.induct' {α : Type} [Ord α] {n : Nat}
  (motive : (arr : Vec α n) → (first i j : Fin n) → (fi : first ≤ i) → (ij : i ≤ j) → Sort u)
  (arr : Vec α n) (first i j : Fin n)
  (fi : first ≤ i) (ij : i ≤ j)
  (base : ∀arr first i j fi ij (_ : ¬first < i), motive arr first i j fi ij)
  (step_lt : ∀arr (first i j : Fin n) fi ij
    (_ : first < i) (_ : first ≤ i.val - 1) (_ : arr[i] <o arr[first]) (_ : i.val - 1 ≤ j)
    (ih : motive arr first i.prev j (by assumption) (by assumption)),
    motive arr first i j fi ij)
  (step_ge : ∀arr (first i j : Fin n) fi ij
    (_ : first < i) (_ : first ≤ i.val - 1) (_ : ¬arr[i] <o arr[first]) (_ : i.val - 1 ≤ j.val - 1)
    (ih : motive (arr.swap i j) first i.prev j.prev (by assumption) (by assumption)),
    motive arr first i j fi ij)
  : motive arr first i j fi ij := by
  if h : first < i then
    have : first ≤ i.val - 1 := Nat.le_sub_one_of_lt h
    if _ : arr[i] <o arr[first] then
      have : i.val - 1 ≤ j := Nat.le_trans (Nat.sub_le ..) ij
      apply step_lt arr first i j fi ij h (by assumption) (by assumption)
      apply partitionImpl.induct' motive
        arr first i.prev j
        (by assumption) (by assumption)
        base step_lt step_ge
    else
      have : i.val - 1 ≤ j.val - 1 := Nat.sub_le_sub_right ij 1
      let arr' := arr.swap i j
      apply step_ge arr first i j fi ij h (by assumption) (by assumption) (by assumption)
      apply partitionImpl.induct' motive
        arr' first i.prev j.prev
        (by assumption) (by assumption)
        base step_lt step_ge
  else
    apply base arr first i j fi ij h
termination_by i.val

@[simp]
theorem partitionImpl.simp_base {α : Type} [Ord α]
  {n : Nat} {arr : Vec α n} {first i j : Fin n}
  {fi : first ≤ i} {ij : i ≤ j}
  (h : ¬first < i) :
  partitionImpl arr first i j fi ij =
  (⟨j, ⟨Nat.le_trans (by assumption) ij, Nat.le_refl _⟩⟩, arr) := by
  unfold partitionImpl
  simp [*, dbgTraceIfShared]

@[simp]
theorem partitionImpl.simp_step_lt {α : Type} [Ord α]
  {n : Nat} {arr : Vec α n} {first i j : Fin n}
  {fi : first ≤ i} {ij : i ≤ j}
  (h : first < i) (_ : arr[i] <o arr[first]) :
  partitionImpl arr first i j fi ij = partitionImpl arr first i.prev j (Nat.le_sub_one_of_lt h) (Nat.le_trans (Nat.sub_le ..) ij) := by
  rw [partitionImpl]
  simp [*]

@[simp]
theorem partitionImpl.simp_step_ge {α : Type} [Ord α]
  {n : Nat} {arr : Vec α n} {first i j : Fin n}
  {fi : first ≤ i} {ij : i ≤ j}
  (h : first < i) (_ : ¬arr[i] <o arr[first]) :
  partitionImpl arr first i j fi ij =
  match partitionImpl (arr.swap i j) first i.prev j.prev
    (Nat.le_sub_one_of_lt h) (Nat.sub_le_sub_right ij 1) with
  | (⟨mid, hm⟩, arr) => (⟨mid, ⟨hm.1, Nat.le_trans hm.2 (Nat.sub_le ..)⟩⟩, arr) := by
  rw [partitionImpl]
  simp [*, dbgTraceIfShared]

def quickSortImpl.induct' {α : Type} [Ord α] {n : Nat}
  (motive : (arr : Vec α n) → (first : Nat) → (last : Fin n) → Sort u)
  (arr : Vec α n) (first : Nat) (last : Fin n)
  (base : ∀arr (first : Nat) (last : Fin n) (_ : ¬first < last), motive arr first last)
  (step : ∀arr (first : Nat) (last : Fin n) (lt : first < last)
    (parted : { mid : Fin n // first ≤ mid ∧ mid ≤ last } × Vec α n) (_ : partition arr ⟨first, Nat.lt_trans lt last.isLt⟩ last (Nat.le_of_lt lt) = parted)
    (ih₁ : motive parted.2 first parted.1.val.prev)
    (ih₂ : motive (quickSortImpl parted.2 first parted.1.val.prev) (parted.1 + 1) last),
    motive arr first last
  )
  : motive arr first last := by
  if lt : first < last then
    let parted := partition arr ⟨first, Nat.lt_trans lt last.isLt⟩ last (Nat.le_of_lt lt)
    let mid := parted.1.val
    let hm := parted.1.property
    -- Termination lemmas
    have : mid.val - 1 < last :=
      match Nat.eq_zero_or_pos mid with
      | .inl eq => by simp[eq]; exact Nat.zero_lt_of_lt lt
      | .inr pos => Nat.lt_of_lt_of_le (Nat.sub_lt pos (by decide)) hm.2
    have : last - (mid + 1) < last - first := Nat.sub_lt_sub_left lt (Nat.lt_of_le_of_lt hm.1 (Nat.lt_succ_self ..))

    apply step arr first last lt parted (Eq.refl parted)
    case ih₁ =>
      apply quickSortImpl.induct' motive parted.2 first mid.prev base step
    case ih₂ =>
      apply quickSortImpl.induct' motive (quickSortImpl parted.2 first mid.prev) (mid + 1) last
        base step
  else
    apply base arr first last lt
termination_by (last.val, last - first)

@[simp]
theorem quickSortImpl.simp_base {α : Type} [Ord α]
  {n : Nat} {arr : Vec α n} {first : Nat} {last : Fin n}
  (h : ¬first < last) :
  quickSortImpl arr first last = arr := by
  unfold quickSortImpl
  simp [*]

@[simp]
theorem quickSortImpl.simp_step {α : Type} [Ord α]
  {n : Nat} {arr : Vec α n} {first : Nat} {last : Fin n}
  (lt : first < last) :
  let parted := partition arr ⟨first, Nat.lt_trans lt last.isLt⟩ last (Nat.le_of_lt lt)
  let mid := parted.1.val
  quickSortImpl arr first last = quickSortImpl (quickSortImpl parted.2 first mid.prev) (mid + 1) last := by
  rw [quickSortImpl]
  simp [*]
