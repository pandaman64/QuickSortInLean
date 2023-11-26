import QuickSortInLean.QuickSort

theorem partitionImpl.induct {α : Type} [Ord α] {n : Nat}
  (motive : (arr : Vec α n) → (first i j : Nat) → (fi : first ≤ i) → (ij : i ≤ j) → (jn : j < n) → Sort u)
  (arr : Vec α n) (first i j : Nat)
  (fi : first ≤ i) (ij : i ≤ j) (jn : j < n)
  (base : ∀arr first i j fi ij jn (_ : i < n) (_ : first < n) (_ : ¬first < i), motive arr first i j fi ij jn)
  (step_lt : ∀arr first i j fi ij jn
    (_ : i < n) (_ : first < n) (_ : first < i) (_ : first ≤ i - 1) (_ : arr[i] <o arr[first]) (_ : i - 1 ≤ j)
    (ih : motive arr first (i - 1) j (by assumption) (by assumption) jn),
    motive arr first i j fi ij jn)
  (step_ge : ∀arr first i j fi ij jn
    (_ : i < n) (_ : first < n) (_ : first < i) (_ : first ≤ i - 1) (_ : ¬arr[i] <o arr[first]) (_ : i - 1 ≤ j - 1) (_ : j - 1 < n)
    (ih : motive (arr.swap ⟨i, by assumption⟩ ⟨j, jn⟩) first (i - 1) (j - 1) (by assumption) (by assumption) (by assumption)),
    motive arr first i j fi ij jn)
  : motive arr first i j fi ij jn := by
  have : i < n := Nat.lt_of_le_of_lt ij jn
  have : first < n := Nat.lt_of_le_of_lt fi this
  if h : first < i then
    have : first ≤ i - 1 := Nat.le_sub_of_lt h
    if _ : arr[i] <o arr[first] then
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
theorem partitionImpl.simp_base {α : Type} [Ord α]
  {n : Nat} {arr : Vec α n} {first i j : Nat}
  {fi : first ≤ i} {ij : i ≤ j} {jn : j < n}
  (h : ¬first < i) :
  partitionImpl arr first i j fi ij jn =
  (⟨j, ⟨Nat.le_trans (by assumption) ij, by simp⟩⟩, arr) := by
  unfold partitionImpl
  simp [*, dbgTraceIfShared]

@[simp]
theorem partitionImpl.simp_step_lt {α : Type} [Ord α]
  {n : Nat} {arr : Vec α n} {first i j : Nat}
  {fi : first ≤ i} {ij : i ≤ j} {jn : j < n}
  (h : first < i) (_ : ltOfOrd.lt (arr[i]'(Nat.lt_of_le_of_lt ij jn)) (arr[first]'(Nat.lt_of_le_of_lt fi (Nat.lt_of_le_of_lt ij jn)))) :
  partitionImpl arr first i j fi ij jn = partitionImpl arr first (i - 1) j (Nat.le_sub_of_lt h) (Nat.le_trans (Nat.sub_le ..) ij) jn := by
  rw [partitionImpl]
  simp [*]

@[simp]
theorem partitionImpl.simp_step_ge {α : Type} [Ord α]
  {n : Nat} {arr : Vec α n} {first i j : Nat}
  {fi : first ≤ i} {ij : i ≤ j} {jn : j < n} (h : first < i) (_ : ¬arr[i]'(Nat.lt_of_le_of_lt ij jn) <o arr[first]'(Nat.lt_of_le_of_lt fi (Nat.lt_of_le_of_lt ij jn))) :
  partitionImpl arr first i j fi ij jn =
  match partitionImpl (arr.swap ⟨i, Nat.lt_of_le_of_lt ij jn⟩ ⟨j, jn⟩) first (i - 1) (j - 1)
    (Nat.le_sub_of_lt h) (Nat.sub_le_sub_right ij 1) (Nat.lt_of_le_of_lt (Nat.sub_le ..) jn) with
  | (⟨mid, hm⟩, arr) => (⟨mid, ⟨hm.1, Nat.le_trans hm.2 (Nat.sub_le ..)⟩⟩, arr) := by
  rw [partitionImpl]
  simp [*, dbgTraceIfShared]

theorem quickSortImpl.induct {α : Type} [Ord α] {n : Nat}
  (motive : (arr : Vec α n) → (first last : Nat) → (ln : last < n) → Sort u)
  (arr : Vec α n) (first last : Nat) (ln : last < n)
  (base : ∀arr first last ln (_ : ¬first < last), motive arr first last ln)
  (step : ∀arr first last ln (lt : first < last)
    (parted : { mid : Nat // first ≤ mid ∧ mid ≤ last } × Vec α n) (_ : partition arr first last (Nat.le_of_lt lt) ln = parted),
    have : parted.1 - 1 < n := Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.lt_of_le_of_lt parted.1.property.2 ln)
    ∀(ih₁ : motive parted.2 first (parted.1 - 1) (by assumption))
      (ih₂ : motive (quickSortImpl parted.2 first (parted.1 - 1) (by assumption)) (parted.1 + 1) last ln),
    motive arr first last ln
  )
  : motive arr first last ln := by
  if lt : first < last then
    let parted := partition arr first last (Nat.le_of_lt lt) ln
    let mid := parted.1.val
    let hm := parted.1.property
    have : mid - 1 < n := Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.lt_of_le_of_lt hm.2 ln)
    -- Termination lemmas
    have : mid - 1 - first < last - first := quickSortImpl.termination_lemma first last lt hm.1 hm.2
    have : last - (mid + 1) < last - first := Nat.sub_lt_sub_left lt (Nat.lt_of_le_of_lt hm.1 (Nat.lt_succ_self ..))

    apply step arr first last ln lt parted (Eq.refl parted)
    case ih₁ =>
      show motive parted.2 first (mid - 1) (by assumption)
      apply quickSortImpl.induct motive parted.2 first (mid - 1) (by assumption)
        base step
    case ih₂ =>
      show motive (quickSortImpl parted.2 first (mid - 1) (by assumption)) (mid + 1) last ln
      apply quickSortImpl.induct motive (quickSortImpl parted.2 first (mid - 1) (by assumption)) (mid + 1) last ln
        base step
  else
    apply base arr first last ln lt
termination_by _ => last - first

@[simp]
theorem quickSortImpl.simp_base {α : Type} [Ord α]
  {n : Nat} {arr : Vec α n} {first last : Nat} {ln : last < n}
  (h : ¬first < last) :
  quickSortImpl arr first last ln = arr := by
  unfold quickSortImpl
  simp [*]

@[simp]
theorem quickSortImpl.simp_step {α : Type} [Ord α]
  {n : Nat} {arr : Vec α n} {first last : Nat} {ln : last < n}
  (lt : first < last) :
  let parted := partition arr first last (Nat.le_of_lt lt) ln
  let mid := parted.1.val
  let hm := parted.1.property
  have : mid - 1 < n := Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.lt_of_le_of_lt hm.2 ln)
  quickSortImpl arr first last ln = quickSortImpl (quickSortImpl parted.2 first (mid - 1) (by assumption)) (mid + 1) last ln := by
  rw [quickSortImpl]
  simp [*]
