import QuickSortInLean.Order
import QuickSortInLean.Vec
import QuickSortInLean.QuickSort
import QuickSortInLean.Induction
import QuickSortInLean.QuickSortPermutation
import Std.Data.Fin.Basic

def sortedRange [Ord α] (arr : Vec α n) (first last : Nat) : Prop :=
  ∀i j : Fin n, first ≤ i → i ≤ j → j ≤ last → (compare arr[i] arr[j]).isLE

def sorted [Ord α] (arr : Array α) : Prop :=
  ∀i j : Fin arr.size, i ≤ j → (compare arr[i] arr[j]).isLE

structure partitionImpl.LoopInvariant {α : Type} [Ord α] {n : Nat}
  (arr : Vec α n) (first i j last : Fin n) : Prop where
  intro ::
  inv₁ : ∀k, i < k → (kj : k < j) → arr[k] <o arr[first]
  inv₂ : ∀k, j < k → (kl : k ≤ last) → ¬arr[k] <o arr[first]
  inv₃ : i < j → arr[j] <o arr[first]

theorem partitionImpl.loop_invariant {α : Type} [Ord α] {n : Nat}
  (arr : Vec α n) (first i j last : Fin n)
  (fi : first ≤ i) (ij : i ≤ j)
  (inv : LoopInvariant arr first i j last)
  (result : { mid : Nat // first ≤ mid ∧ mid ≤ j } × Vec α n)
  (eq : partitionImpl arr first i j fi ij = result) :
  LoopInvariant result.2 first first ⟨result.1.val, Nat.lt_of_le_of_lt result.1.property.2 j.isLt⟩ last := by
  induction arr, first, i, j, fi, ij using partitionImpl.induct with
  | base arr first i j fi _ h =>
    revert result
    simp [*]
    have : i = first := Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_of_not_lt h) fi)
    exact this ▸ inv
  | step_lt arr first i j _ _ fi _ lt _ ih =>
    have inv : LoopInvariant arr first i.prev j last := by
      apply LoopInvariant.intro
      . intro k ik kj
        have ik : i.val ≤ k.val := by
          rw [←Nat.sub_add_cancel (Nat.zero_lt_of_lt fi)]
          exact ik
        cases Nat.eq_or_lt_of_le ik with
        | inl ik =>
          simp [Fin.eq_of_val_eq ik] at lt
          exact lt
        | inr ik => exact inv.1 k ik kj
      . exact inv.2
      . intro ij
        have ij : i.val ≤ j.val := by
          rw [←Nat.sub_add_cancel (Nat.zero_lt_of_lt fi)]
          exact ij
        cases Nat.eq_or_lt_of_le ij with
        | inl ij =>
          simp [Fin.eq_of_val_eq ij.symm]
          assumption
        | inr ij => exact inv.3 ij

    simp [*] at eq
    apply ih inv result eq
  | step_ge arr first i j _ ij fi _ _ _ ih =>
    let swapped := arr.swap i j
    have sf : swapped[first] = arr[first] := by
      apply Vec.get_swap_neq
      . apply Fin.ne_of_val_ne
        exact Nat.ne_of_lt fi
      . apply Fin.ne_of_val_ne
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le fi ij)

    let result := partitionImpl swapped first i.prev j.prev (by assumption) (by assumption)
    subst eq
    simp [*]

    have inv : LoopInvariant swapped first i.prev j.prev last := by
      apply LoopInvariant.intro
      . intro k ik kj
        have ik : i.val ≤ k.val := by
          rw [←Nat.sub_add_cancel (Nat.zero_lt_of_lt fi)]
          exact ik
        cases Nat.eq_or_lt_of_le ik with
        | inl ik =>
          have : swapped[k] = arr[j] := by
            simp [Fin.eq_of_val_eq ik.symm]
            apply Vec.get_swap_left
          rw [this, sf]
          exact inv.3 (Nat.lt_of_lt_of_le (Fin.eq_of_val_eq ik.symm ▸ kj) (Nat.sub_le ..))
        | inr ik =>
          have kj : k < j := (Nat.lt_of_lt_of_le kj (Nat.sub_le ..))
          have : swapped[k] = arr[k] := by
            apply Vec.get_swap_neq
            . apply Fin.ne_of_val_ne
              exact Nat.ne_of_gt ik
            . apply Fin.ne_of_val_ne
              exact Nat.ne_of_lt kj
          rw [this, sf]
          exact inv.1 k ik kj
      . intro k jk kl
        have jk : j.val ≤ k.val := by
          rw [←Nat.sub_add_cancel (Nat.zero_lt_of_lt (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le fi ij)))]
          exact jk
        cases Nat.eq_or_lt_of_le jk with
        | inl jk =>
          have : swapped[k] = arr[i] := by
            simp [Fin.eq_of_val_eq jk.symm]
            apply Vec.get_swap_right
          rw [this, sf]
          assumption
        | inr jk =>
          have : swapped[k] = arr[k] := by
            apply Vec.get_swap_neq
            . apply Fin.ne_of_val_ne
              exact Nat.ne_of_gt (Nat.lt_of_le_of_lt ij jk)
            . apply Fin.ne_of_val_ne
              exact Nat.ne_of_gt jk
          rw [this, sf]
          exact inv.2 k jk kl
      . intro ij
        have : j.val - 1 < j.val := by
          show j.val - 1 + 1 ≤ j.val
          rw [Nat.sub_add_cancel (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le fi (by assumption)))]
          apply Nat.le_refl
        have ij : i.val ≤ j.val - 1 := by
          rw [←Nat.sub_add_cancel (Nat.zero_lt_of_lt fi)]
          exact ij
        cases Nat.eq_or_lt_of_le ij with
        | inl ij =>
          have : swapped[j.prev] = arr[j] := by
            simp [ij.symm, Fin.prev]
            apply Vec.get_swap_left
          rw [this, sf]
          have : i < j := Nat.lt_of_le_of_lt (by assumption : i.val ≤ j.val - 1) (by assumption)
          exact inv.3 this
        | inr ij =>
          have : swapped[j.prev] = arr[j.prev] := by
            apply Vec.get_swap_neq
            . apply Fin.ne_of_val_ne
              exact Nat.ne_of_gt ij
            . apply Fin.ne_of_val_ne
              exact Nat.ne_of_lt (by assumption)
          rw [this, sf]
          apply inv.1 j.prev ij (by assumption)

    exact ih inv result (by rfl)

theorem partitionImpl.first_eq {α : Type} [Ord α] {n : Nat}
  (arr : Vec α n) (first i j : Fin n)
  (fi : first ≤ i) (ij : i ≤ j) :
  (partitionImpl arr first i j fi ij).2[first] = arr[first] := by
  induction arr, first, i, j, fi, ij using partitionImpl.induct with
  | base => simp [*]
  | step_lt => simp [*]
  | step_ge arr first i j _ ij fi =>
    simp [*]
    have fj : first < j := Nat.lt_of_lt_of_le fi ij
    apply Vec.get_swap_neq
    . apply Fin.ne_of_val_ne
      exact Nat.ne_of_lt fi
    . apply Fin.ne_of_val_ne
      exact Nat.ne_of_lt fj

theorem partition.partition {α : Type} [Ord α] {n : Nat}
  (arr : Vec α n) (first last : Fin n) (fl : first ≤ last)
  (result : { mid : Nat // first ≤ mid ∧ mid ≤ last } × Vec α n)
  (eq : partition arr first last fl = result) :
  (∀k : Fin n, first ≤ k → (km : k.val < result.1.val) →
    result.2[k] <o arr[first]) ∧
  (result.2[result.1.val]'(Nat.lt_of_le_of_lt result.1.property.2 last.isLt) = arr[first]) ∧
  (∀k : Fin n, result.1.val < k.val → (kl : k ≤ last) →
    ¬result.2[k] <o arr[first]) := by

  let afterLoop := partitionImpl arr first last last fl (Nat.le_refl _)
  let mid := afterLoop.1
  let arr' := afterLoop.2
  have : mid < n := Nat.lt_of_le_of_lt mid.property.2 last.isLt
  let swapped := arr'.swap first ⟨mid, by assumption⟩
  have : result.1 = mid := by
    rw [←eq]
    unfold partition
    simp [afterLoop]
  have : result.2 = swapped := by
    rw [←eq]
    unfold partition
    simp [afterLoop, dbgTraceIfShared]

  have first_eq : arr'[first] = arr[first] := by
    apply partitionImpl.first_eq

  let inv₀ : partitionImpl.LoopInvariant arr first last last last := by
    apply partitionImpl.LoopInvariant.intro
    . intro k lk kl
      exact (Nat.lt_irrefl k (Nat.lt_trans kl lk)).elim
    . intro k lk kl
      exact (Nat.lt_irrefl k (Nat.lt_of_le_of_lt kl lk)).elim
    . intro ll
      exact (Nat.lt_irrefl last ll).elim
  let inv := partitionImpl.loop_invariant arr first last last last fl (Nat.le_refl _) inv₀ afterLoop (by rfl)

  have p₁ (k : Fin n) (fk : first ≤ k) (km : k.val < mid) : swapped[k] <o arr[first] := by
    cases Nat.eq_or_lt_of_le fk with
    | inl fk =>
      have : swapped[k] = swapped[first] := by
        simp [Fin.eq_of_val_eq fk]
      rw [this]
      have : swapped[first] = arr'[mid.val] := by
        apply Vec.get_swap_left
      rw [this, ←first_eq]
      exact inv.3 (Fin.eq_of_val_eq fk ▸ km)
    | inr fk =>
      have : swapped[k] = arr'[k] := by
        apply Vec.get_swap_neq
        . apply Fin.ne_of_val_ne
          exact Nat.ne_of_gt fk
        . apply Fin.ne_of_val_ne
          exact Nat.ne_of_lt km
      rw [this, ←first_eq]
      exact inv.1 k fk km

  have p₂ : swapped[mid.val] = arr[first] := by
    have : swapped[mid.val] = arr'[first] := by
      apply Vec.get_swap_right
    rw [this]
    assumption

  have p₃ (k : Fin n) (mk : mid < k.val) (kl : k ≤ last) : ¬swapped[k] <o arr[first] := by
    have : swapped[k] = arr'[k] := by
      apply Vec.get_swap_neq
      . apply Fin.ne_of_val_ne
        exact Nat.ne_of_gt (Nat.lt_of_le_of_lt mid.property.1 mk)
      . apply Fin.ne_of_val_ne
        exact Nat.ne_of_gt mk
    rw [this, ←first_eq]
    exact inv.2 k mk kl

  apply And.intro
  . simp [*]
    apply p₁
  . apply And.intro
    . simp [*]
    . simp [*]
      apply p₃

inductive Nat.RangeSplit (i j x : Nat) (ij : i ≤ j) : Prop where
  | lt : i < x → j < x → Nat.RangeSplit i j x ij
  | ge : x < i → x < j → Nat.RangeSplit i j x ij
  | split : i ≤ x → x ≤ j → Nat.RangeSplit i j x ij

def Nat.range_split (i j x : Nat) (ij : i ≤ j) : Nat.RangeSplit i j x ij :=
  match Nat.lt_trichotomy j x with
  | .inl jx => .lt (Nat.lt_of_le_of_lt ij jx) jx
  | .inr (.inl jx) => .split (jx ▸ ij) (Nat.le_of_eq jx.symm)
  | .inr (.inr jx) => match Nat.decLt x i with
    | isTrue ix => .ge ix jx
    | isFalse ix => .split (Nat.le_of_not_lt ix) (Nat.le_of_lt jx)

theorem quickSortImpl.get_lt {α : Type} [Ord α] {n : Nat}
  (arr : Vec α n) (first : Nat) (last : Fin n)
  (k : Fin n) (lt : k < first) :
  (quickSortImpl arr first last)[k] = arr[k] := by
  let p := quickSortImpl_permuted arr first last
  exact p.get_lt lt

theorem quickSortImpl.get_gt {α : Type} [Ord α] {n : Nat}
  (arr : Vec α n) (first : Nat) (last : Fin n)
  (k : Fin n) (gt : k > last) :
  (quickSortImpl arr first last)[k] = arr[k] := by
  let p := quickSortImpl_permuted arr first last
  exact p.get_gt gt

theorem quickSortImpl_sortedRange {α : Type} [Order α] {n : Nat}
  (arr : Vec α n) (first : Nat) (last : Fin n) :
  sortedRange (quickSortImpl arr first last) first last := by
  induction arr, first, last using quickSortImpl.induct with
  | base arr first last h =>
    simp [*]
    intro i j fi ij jl
    have : first = last := Nat.le_antisymm (Nat.le_trans (Nat.le_trans fi ij) jl) (Nat.le_of_not_gt h)
    subst this
    have : i = last := Fin.eq_of_val_eq (Nat.le_antisymm (Nat.le_trans ij jl) fi)
    subst this
    have : i = j := Fin.eq_of_val_eq (Nat.le_antisymm ij jl)
    subst this
    apply Order.refl
  | step arr first last lt parted eq _ ih₁ ih₂ =>
    have : first < n := Nat.lt_trans lt last.isLt
    simp [*]
    intro i j fi ij jl

    let mid := parted.1
    have mn : mid.val < n := Nat.lt_of_le_of_lt mid.property.2 last.isLt
    let sorted := quickSortImpl (quickSortImpl parted.snd first ⟨mid.val - 1, by assumption⟩) (mid.val + 1) last

    let ⟨l, m, r⟩ := partition.partition arr ⟨first, by assumption⟩ last (Nat.le_of_lt lt) parted eq

    have getL (k : Fin n) (fk : first ≤ k) (km : k < mid.val) : sorted[k] <o arr[first] := by
      rw [quickSortImpl.get_lt (lt := (Nat.lt_trans km (Nat.lt_succ_self ..)))]
      let p := quickSortImpl_permuted parted.2 first ⟨mid.val - 1, by assumption⟩
      let ⟨k', ⟨index, fk', km'⟩⟩ := permuted_map_index_in_range_inv p k fk (Nat.le_sub_one_of_lt km)
      let inv := index ▸ permuted_map_index p k'
      rw [←inv]
      apply l k' fk' (Nat.lt_of_le_of_lt km' (Nat.sub_lt_self (by decide) (Nat.zero_lt_of_lt km)))

    have getM (k : Fin n) (eq : mid.val = k.val): sorted[k] = arr[first] := by
      let mid' : Fin n := ⟨mid.val, mn⟩
      have : k = mid' := by
        apply Fin.eq_of_val_eq
        simp [eq]
      subst this
      rw [quickSortImpl.get_lt (k := mid') (lt := Nat.lt_succ_self ..)]
      cases Nat.eq_zero_or_pos mid.val with
      | inl zero =>
        simp [zero] at *
        exact m
      | inr pos =>
        rw [quickSortImpl.get_gt (k := mid') (gt := Nat.sub_lt_self (by decide) (Nat.zero_lt_of_lt pos))]
        exact m

    have getR (k : Fin n) (mk : mid.val < k) (kl : k ≤ last) : ¬sorted[k] <o arr[first] := by
      let p := quickSortImpl_permuted (quickSortImpl parted.snd first ⟨mid.val - 1, by assumption⟩) (mid.val + 1) last
      let ⟨k', ⟨index, mk', kl'⟩⟩ := permuted_map_index_in_range_inv p k mk kl
      let inv := index ▸ permuted_map_index p k'
      rw [←inv]
      have : (⟨mid.val - 1, by assumption⟩ : Fin n).val ≤ mid.val := by
        simp
        exact (Nat.sub_le ..)
      rw [quickSortImpl.get_gt (gt := Nat.lt_of_le_of_lt this mk')]
      apply r k' mk' kl'

    have getLM (k : Fin n) (fk : first ≤ k) (km : k ≤ mid.val) : sorted[k] ≤o arr[first] := by
      cases Nat.eq_or_lt_of_le km with
      | inl km =>
        rw [getM k km.symm]
        apply Order.refl
      | inr km => exact Order.le_of_lt (getL k fk km)

    have getMR (k : Fin n) (mk : mid.val ≤ k) (kl : k ≤ last) : ¬sorted[k] <o arr[first] := by
      match Nat.eq_or_lt_of_le mk with
      | .inl mk =>
        rw [getM k mk]
        apply Order.irrefl
      | .inr mk => exact getR k mk kl

    cases Nat.range_split i j mid ij with
    | lt im jm =>
      rw [quickSortImpl.get_lt (lt := Nat.lt_trans im (Nat.lt_succ_self ..))]
      rw [quickSortImpl.get_lt (lt := Nat.lt_trans jm (Nat.lt_succ_self ..))]
      exact ih₁ i j fi ij (Nat.le_sub_of_add_le jm)
    | ge mi mj => exact ih₂ i j mi ij jl
    | split im mj =>
      have h₁ : sorted[i] ≤o arr[first] := getLM i fi im
      have h₂ : arr[first] ≤o sorted[j] := Order.le_of_not_lt (getMR j mj jl)
      apply Order.trans h₁ h₂

theorem quickSort'_sortedRange {α : Type} [Order α] {n : Nat} (arr : Vec α n) :
  sortedRange (quickSort' arr) 0 (n - 1) := by
  if h : n > 0 then
    simp [quickSort', h]
    apply quickSortImpl_sortedRange
  else
    intro i
    have : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    exact (Nat.not_lt_zero i.val i.isLt).elim

theorem quickSort_size {α : Type} [Order α] (arr : Array α) :
  (quickSort arr).size = arr.size := by
  let sorted := quickSort' ⟨arr, rfl⟩
  show sorted.val.size = arr.size
  simp [sorted.property]

theorem quickSort_sorted {α : Type} [Order α] (arr : Array α) :
  sorted (quickSort arr) := by
  let sr := quickSort'_sortedRange (arr : Vec α arr.size)
  intro i j ij
  have hi : 0 ≤ i.val := Nat.zero_le i.val
  have s : (quickSort arr).size = arr.size := quickSort_size arr
  have hj : j.val ≤ arr.size - 1 := Nat.le_sub_one_of_lt (s ▸ j.isLt)

  exact sr (i.cast s) (j.cast s) hi ij hj
