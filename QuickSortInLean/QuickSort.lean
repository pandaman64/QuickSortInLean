def partition' [Ord α] [Inhabited α]
  (arr : Array α) (i j last : Nat) (h1 : i ≤ last) (h2 : last < arr.size): (Nat × Array α) :=
  if _ : j < last then
    have : j < arr.size := sorry
    match compare arr[j] arr[last] with
    | .lt | .eq =>
      have _ : i < arr.size := sorry
      have _ : j < arr.size := sorry
      let arr := (dbgTraceIfShared "arr2" arr).swap ⟨i, by assumption⟩ ⟨j, by assumption⟩
      partition' (dbgTraceIfShared "arr3" arr) (i + 1) (j + 1) last (by sorry) (by simp [dbgTraceIfShared, h2])
    | .gt => partition' (dbgTraceIfShared "arr4" arr) i (j + 1) last h1 h2
  else
    have : i < arr.size := sorry
    have : last < arr.size := sorry
    let arr := (dbgTraceIfShared "arr5" arr).swap ⟨i, by assumption⟩ ⟨last, by assumption⟩
    (i, arr)
termination_by partition' _ _ j last h1 h2 => last - j

theorem partition'_size {α : Type} {result : (Nat × Array α)} [Ord α] [Inhabited α]
   (arr : Array α) (i j last : Nat) (h1 : i ≤ last) (h2 : last < arr.size) :
   partition' arr i j last h1 h2 = result →
   result.2.size = arr.size := by
   unfold partition'
   split <;> simp
   case inl _ =>
    split
    -- | .lt | .eq
    case h_1 | h_2 => sorry
    -- | .gt
    case h_3 => sorry
   case inr _ =>
    simp [dbgTraceIfShared]
    intro eq
    rw [←eq]
    simp

theorem partition'_mid {α : Type} {result : (Nat × Array α)} [Ord α] [Inhabited α]
  (arr : Array α) (i j last : Nat) (h1 : i ≤ last) (h2 : last < arr.size) :
  i ≤ j →
  j ≤ last →
  partition' arr i j last h1 h2 = result →
  i ≤ result.1 ∧ result.1 ≤ last := by
  intro ij jl
  unfold partition'
  split <;> simp
  case inl jl =>
    split
    -- | .lt | .eq
    case h_1 | h_2 =>
      intro eq
      have ij : i + 1 ≤ j + 1 := Nat.add_le_add_right ij 1
      have jl : j + 1 ≤ last := Nat.succ_le_of_lt jl
      let ⟨i_result, result_last⟩ := partition'_mid _ (i + 1) (j + 1) last _ _ ij jl eq
      have : i ≤ result.1 := by
        apply Nat.le_trans (by simp_arith) i_result
      exact ⟨by assumption, by assumption⟩
    -- | .gt
    case h_3 =>
      intro eq
      have ij : i ≤ j + 1 := Nat.le_trans ij (by simp_arith)
      have jl : j + 1 ≤ last := Nat.succ_le_of_lt jl
      exact partition'_mid _ i (j + 1) last _ _ ij jl eq
  case inr njl =>
    intro eq
    have : result.1 = i := by
      rw [←eq]
    simp [this]
    exact Nat.le_trans ij jl
termination_by partition'_mid α result ord inhabited arr i j last h1 h2 ij jl => last - j

-- #eval partition' 5 #[7, 9, 5, 2, 8, 2, 5, 4, 10, 5] 0 0 9

def partition [Ord α] [Inhabited α]
  (arr : Array α) (first last : Nat) (_ : first ≤ last) (_ : last < arr.size) :
  ({ mid : Nat // first ≤ mid ∧ mid ≤ last } × Array α) :=
  let result := partition' arr first first last (by assumption) (by assumption)
  let property := partition'_mid (result := result) arr first first last (by assumption) (by assumption) (by simp) (by assumption) (by rfl)
  (⟨result.1, property⟩, result.2)

theorem Nat.le_or_gt : {m n : Nat} → m ≤ n ∨ m > n
  | m, n =>
    match Nat.decLe m n with
    | isTrue h => Or.inl h
    | isFalse h => Or.inr (Nat.gt_of_not_le h)

theorem quickSort'_termination {first mid last : Nat} :
  first < last →
  first ≤ mid →
  mid ≤ last →
  mid - 1 - first < last - first ∧ last - (mid + 1) < last - first := by
  intro lt first_mid mid_last

  -- LHS
  have : mid - (1 + first) < last - first := by
    have : mid ≤ 1 + first ∨ mid > 1 + first := Nat.le_or_gt
    cases this with
    | inl le =>
      have : mid - (1 + first) = 0 := by
        exact Nat.sub_eq_zero_of_le le
      simp [this, Nat.zero_lt_sub_of_lt, lt]
    | inr gt =>
      have : mid - (1 + first) + (1 + first) = mid := by
        apply Nat.sub_add_cancel
        exact Nat.le_of_lt gt
      have : mid - (1 + first) + (1 + first) ≤ last := by
        rw [this]
        exact mid_last
      have : mid - (1 + first) + first + 1 ≤ last := by
        rw [Nat.add_assoc]
        rw [Nat.add_comm first 1]
        exact this
      have : mid - (1 + first) + first < last := by
        simp_arith [this]
      exact Nat.lt_sub_of_add_lt this
  have : mid - 1 - first < last - first := by
    rw [Nat.sub_sub]
    exact this

  -- RHS
  have : last - (mid + 1) < last - first := by
    apply Nat.sub_lt_sub_left
    . assumption
    . simp_arith [first_mid]
  exact And.intro (by assumption) (by assumption)

def quickSort' [Ord α] [Inhabited α] (arr : Array α) (first last : Nat) (_ : last < arr.size) : Array α :=
  if lt : first < last then
    have : first ≤ last := by
      apply Nat.le_of_lt
      assumption
    let (⟨mid, ⟨first_mid, mid_last⟩⟩, arr) := partition (dbgTraceIfShared "arr6" arr) first last this (by assumption)
    have ⟨_, _⟩ := quickSort'_termination lt first_mid mid_last
    have : mid - 1 < arr.size := by
      -- mid - 1 ≤ mid ≤ last < arr.size
      sorry
    let arr := quickSort' (dbgTraceIfShared "arr7" arr) first (mid - 1) (by simp[dbgTraceIfShared, *])
    quickSort' (dbgTraceIfShared "arr8" arr) (mid + 1) last (by sorry)
  else
    arr
termination_by quickSort' _ _ first last _ => last - first

def quickSort [Ord α] [Inhabited α] (arr : Array α) : Array α :=
  if _ : arr.size > 0 then
    quickSort' arr 0 (arr.size - 1) (by simp [Nat.sub_lt, *])
  else
    arr

-- #eval quickSort #[7, 5, 6, 2, 8, 1, 9, 4, 10, 3]
-- #eval quickSort #[3, 4, 5, 2, 1, 5, 3, 2, 1, 4]
