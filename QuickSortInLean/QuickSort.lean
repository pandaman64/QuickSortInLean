import Std.Data.Fin.Basic

/--
When proving termination and the safety of array operation, it's crucial to show
that each operation preserves the size of the array. Therefore, we encode the
size into the type using the Vec type.
-/
abbrev Vec (α : Type) (n : Nat) := { arr : Array α // arr.size = n }

def Vec.swap (self : Vec α n) (i j : Fin n) : Vec α n :=
  ⟨self.val.swap (i.cast self.property.symm) (j.cast self.property.symm), by simp [self.property]⟩

def Vec.getElem (self : Vec α n) (i : Nat) (isLt : i < n) : α :=
  self.val.get ⟨i, by simp [self.property, isLt]⟩

instance : GetElem (Vec α n) (Fin n) α (fun _ _ => True) where
  getElem v i _ := v.getElem i.val i.isLt

instance {α : Type} {n : Nat} : GetElem (Vec α n) Nat α (fun _ i => i < n) where
  getElem := Vec.getElem

theorem Nat.le_sub_of_lt {m n : Nat} (h : m < n) : m ≤ n - 1 := by
  induction h with
  | refl => show m ≤ m; simp
  | step _ ih =>
    apply Nat.le_trans ih
    apply Nat.sub_le_succ_sub

def partitionImpl {α : Type} [Ord α]
  {n : Nat} (arr : Vec α n) (first i j : Nat)
  (fi : first ≤ i) (ij : i ≤ j) (jn : j < n) :
  { mid : Nat // first ≤ mid ∧ mid ≤ j } × Vec α n :=
  have : i < n := Nat.lt_of_le_of_lt ij jn
  have : first < n := Nat.lt_of_le_of_lt fi this
  if fi : first < i then
    have : first ≤ i - 1 := Nat.le_sub_of_lt fi
    match compare arr[i] arr[first] with
    | .lt =>
      have : i - 1 ≤ j := Nat.le_trans (Nat.sub_le ..) ij
      partitionImpl arr first (i - 1) j (by assumption) (by assumption) jn
    | .eq | .gt =>
      have : i - 1 ≤ j - 1 := Nat.sub_le_sub_right ij 1
      have : j - 1 < n := Nat.lt_of_le_of_lt (Nat.sub_le ..) jn
      let arr := (dbgTraceIfShared "swap1" arr).swap ⟨i, by assumption⟩ ⟨j, jn⟩
      match partitionImpl arr first (i - 1) (j - 1) (by assumption) (by assumption) (by assumption) with
      | (⟨mid, ⟨hmid₁, hmid₂⟩⟩, arr) => (⟨mid, ⟨hmid₁, Nat.le_trans hmid₂ (Nat.sub_le ..)⟩⟩, arr)
  else
    let arr := (dbgTraceIfShared "swap2" arr).swap ⟨first, by assumption⟩ ⟨i, by assumption⟩
    (⟨i, And.intro (by assumption) (by assumption)⟩, arr)

def partition {α : Type} [Ord α]
  {n : Nat} (arr : Vec α n) (first last : Nat)
  (fl : first ≤ last) (ln : last < n) :
  { mid : Nat // first ≤ mid ∧ mid ≤ last } × Vec α n :=
  partitionImpl arr first last last fl (by simp) ln

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

def quickSort' [Ord α] (arr : Array α) (first last : Nat) (la : last < arr.size) :
  ({ arr' : Array α  // arr'.size = arr.size }) :=
  let size := arr.size
  if lt : first < last then
    have fl : first ≤ last := by
      apply Nat.le_of_lt
      assumption
    -- Need to use match to put the equality in the context
    match hp : partition arr first last fl la with
    | (mid, arr) =>
      have ⟨first_mid, mid_last⟩ := partition_mid _ first last fl la hp
      have ⟨_, _⟩ := quickSort'_termination lt first_mid mid_last
      have eq1 : size = arr.size := by
        have : arr.size = (partition _ first last fl la).snd.size := by simp[hp]
        rw [this]
        have : (partition _ first last fl la).snd.size = size := by
          apply partition_size
          rfl
        simp [this]
      have : mid - 1 < arr.size := by
        -- mid - 1 ≤ mid ≤ last < size
        have : mid - 1 ≤ last := Nat.le_trans (Nat.sub_le mid 1) mid_last
        have : mid - 1 < size := Nat.lt_of_le_of_lt this (by assumption)
        rw [←eq1]
        exact this
      let ⟨arr, eq2⟩ := quickSort' arr first (mid - 1) this
      have eq3 : arr.size = size := by rw [eq2, eq1]
      have : last < arr.size := by rw [eq3]; assumption
      let ⟨arr, eq4⟩ := quickSort' arr (mid + 1) last this
      ⟨arr, Eq.trans eq4 eq3⟩
  else
    ⟨arr, by rfl⟩
termination_by quickSort' _ _ first last _ => last - first

def quickSort [Ord α] (arr : Array α) : Array α :=
  if _ : arr.size > 0 then
    quickSort' arr 0 (arr.size - 1) (Nat.sub_lt (by assumption) (by decide))
  else
    arr

-- #eval quickSort #[7, 5, 6, 2, 8, 1, 9, 4, 10, 3]
-- #eval quickSort #[3, 4, 5, 2, 1, 5, 3, 2, 1, 4]
