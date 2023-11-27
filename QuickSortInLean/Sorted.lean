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
  (arr : Vec α n) (first i j last : Nat)
  (fn : first < n) (jn : j < n) (ln : last < n) : Prop where
  intro ::
  inv₁ : ∀k, i < k → (kj : k < j) → arr[k]'(Nat.lt_trans kj jn) <o arr[first]
  inv₂ : ∀k, j < k → (kl : k ≤ last) → ¬arr[k]'(Nat.lt_of_le_of_lt kl ln) <o arr[first]
  inv₃ : i < j → arr[j] <o arr[first]

-- TODO: derivableなinequalityをdefault argumentで用意する
theorem partitionImpl.loop_invariant {α : Type} [Ord α] {n : Nat}
  (arr : Vec α n) (first i j last : Nat)
  (fi : first ≤ i) (ij : i ≤ j) (fn : first < n) (jn : j < n) (ln : last < n)
  (inv : LoopInvariant arr first i j last fn jn ln)
  (result : { mid : Nat // first ≤ mid ∧ mid ≤ j } × Vec α n)
  (eq : partitionImpl arr first i j fi ij jn = result) :
  LoopInvariant result.2 first first result.1 last fn (Nat.lt_of_le_of_lt result.1.property.2 jn) ln := by

  induction arr, first, i, j, fi, ij, jn using partitionImpl.induct with
  | base arr first i j fi _ _ _ _ h =>
    have : i = first := Nat.le_antisymm (Nat.le_of_not_lt h) fi
    rw [←eq]
    simp [*, this ▸ inv]
  | step_lt arr first i j _ _ jn _ _ fi _ lt _ ih =>
    rw [←eq]
    simp [*]

    have inv : LoopInvariant arr first (i - 1) j last fn jn ln := by
      apply LoopInvariant.intro
      . intro k ik kj
        have ik : i ≤ k := by
          rw [←Nat.sub_add_cancel (Nat.zero_lt_of_lt fi)]
          exact ik
        cases Nat.eq_or_lt_of_le ik with
        | inl ik =>
          simp [ik] at lt
          exact lt
        | inr ik => exact inv.1 k ik kj
      . exact inv.2
      . intro ij
        have ij : i ≤ j := by
          rw [←Nat.sub_add_cancel (Nat.zero_lt_of_lt fi)]
          exact ij
        cases Nat.eq_or_lt_of_le ij with
        | inl ij =>
          simp [ij.symm]
          assumption
        | inr ij => exact inv.3 ij

    exact ih (by assumption) inv (partitionImpl arr first (i - 1) j (by assumption) (by assumption) (by assumption)) (by rfl)
  | step_ge arr first i j _ ij jn _ _ fi _ _ _ _ ih =>
    let swapped := arr.swap ⟨i, by assumption⟩ ⟨j, by assumption⟩
    have sf : swapped[first] = arr[first] := by
      apply Vec.get_swap_neq
      . apply Fin.ne_of_val_ne
        exact Nat.ne_of_lt fi
      . apply Fin.ne_of_val_ne
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le fi ij)

    let result := partitionImpl swapped first (i - 1) (j - 1) (by assumption) (by assumption) (by assumption)
    rw [←eq]
    simp [*]

    have inv : LoopInvariant swapped first (i - 1) (j - 1) last fn (Nat.lt_of_le_of_lt (Nat.sub_le ..) jn) ln := by
      apply LoopInvariant.intro
      . intro k ik kj
        have : k < n := Nat.lt_trans kj (by assumption)
        have ik : i ≤ k := by
          rw [←Nat.sub_add_cancel (Nat.zero_lt_of_lt fi)]
          exact ik
        cases Nat.eq_or_lt_of_le ik with
        | inl ik =>
          have : swapped[k] = arr[j] := by
            simp [ik.symm]
            apply Vec.get_swap_left
          rw [this, sf]
          exact inv.3 (Nat.lt_of_lt_of_le (ik.symm ▸ kj) (Nat.sub_le ..))
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
        have : k < n := Nat.lt_of_le_of_lt kl (by assumption)
        have jk : j ≤ k := by
          rw [←Nat.sub_add_cancel (Nat.zero_lt_of_lt (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le fi ij)))]
          exact jk
        cases Nat.eq_or_lt_of_le jk with
        | inl jk =>
          have : swapped[k] = arr[i] := by
            simp [jk.symm]
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
        have : j - 1 < j := by
          show j - 1 + 1 ≤ j
          rw [Nat.sub_add_cancel (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le fi (by assumption)))]
          apply Nat.le_refl
        have ij : i ≤ j - 1 := by
          rw [←Nat.sub_add_cancel (Nat.zero_lt_of_lt fi)]
          exact ij
        cases Nat.eq_or_lt_of_le ij with
        | inl ij =>
          have : swapped[j - 1] = arr[j] := by
            simp [ij.symm]
            apply Vec.get_swap_left
          rw [this, sf]
          have : i < j := Nat.lt_of_le_of_lt (by assumption : i ≤ j - 1) (by assumption)
          exact inv.3 this
        | inr ij =>
          have : swapped[j - 1] = arr[j - 1] := by
            apply Vec.get_swap_neq
            . apply Fin.ne_of_val_ne
              exact Nat.ne_of_gt ij
            . apply Fin.ne_of_val_ne
              exact Nat.ne_of_lt (by assumption)
          rw [this, sf]
          apply inv.1 (j - 1) ij (by assumption)

    exact ih (by assumption) inv result (by rfl)

theorem partitionImpl.first_eq {α : Type} [Ord α] {n : Nat}
  (arr : Vec α n) (first i j : Nat)
  (fi : first ≤ i) (ij : i ≤ j) (jn : j < n) (fn : first < n := Nat.lt_of_le_of_lt (Nat.le_trans fi ij) jn):
  (partitionImpl arr first i j fi ij jn).2[first] = arr[first] := by
  induction arr, first, i, j, fi, ij, jn using partitionImpl.induct with
  | base => simp [*]
  | step_lt => simp [*]
  | step_ge arr first i j _ ij _ _ _ fi =>
    simp [*]
    have fj : first < j := Nat.lt_of_lt_of_le fi ij
    apply Vec.get_swap_neq
    . apply Fin.ne_of_val_ne
      exact Nat.ne_of_lt fi
    . apply Fin.ne_of_val_ne
      exact Nat.ne_of_lt fj

theorem partition.partition {α : Type} [Ord α] {n : Nat}
  (arr : Vec α n) (first last : Nat)
  (fl : first ≤ last) (ln : last < n)
  (result : { mid : Nat // first ≤ mid ∧ mid ≤ last } × Vec α n)
  (eq : partition arr first last fl ln = result) :
  (∀k : Nat, first ≤ k → (km : k < result.1) →
    result.2[k]'(Nat.lt_trans km (Nat.lt_of_le_of_lt result.1.property.2 ln)) <o arr[first]'(Nat.lt_of_le_of_lt fl ln)) ∧
  (result.2[result.1.val]'(Nat.lt_of_le_of_lt result.1.property.2 ln) = arr[first]'(Nat.lt_of_le_of_lt fl ln)) ∧
  (∀k : Nat, result.1 < k → (kl : k ≤ last) →
    ¬result.2[k]'(Nat.lt_of_le_of_lt kl ln) <o arr[first]'(Nat.lt_of_le_of_lt fl ln)) := by

  let afterLoop := partitionImpl arr first last last fl .refl ln
  let mid := afterLoop.1
  let arr' := afterLoop.2
  let swapped := arr'.swap ⟨first, Nat.lt_of_le_of_lt fl ln⟩ ⟨mid, Nat.lt_of_le_of_lt mid.property.2 ln⟩
  have : result.1 = mid := by
    rw [←eq]
    unfold partition
    simp [afterLoop]
  have : result.2 = swapped := by
    rw [←eq]
    unfold partition
    simp [afterLoop, dbgTraceIfShared]
  have : first < n := Nat.lt_of_le_of_lt fl ln
  have : mid < n := Nat.lt_of_le_of_lt mid.property.2 ln

  have first_eq : arr'[first] = arr[first] := by
    apply partitionImpl.first_eq

  let inv₀ : partitionImpl.LoopInvariant arr first last last last (by assumption) ln ln := by
    apply partitionImpl.LoopInvariant.intro
    . intro k lk kl
      exact (Nat.lt_irrefl k (Nat.lt_trans kl lk)).elim
    . intro k lk kl
      exact (Nat.lt_irrefl k (Nat.lt_of_le_of_lt kl lk)).elim
    . intro ll
      exact (Nat.lt_irrefl last ll).elim
  let inv := partitionImpl.loop_invariant arr first last last last fl .refl (by assumption) ln ln inv₀ afterLoop (by rfl)
  let ⟨a, b, c⟩ := inv

  have p₁ (k : Nat) (fk : first ≤ k) (km : k < mid) : swapped[k]'(Nat.lt_trans km (Nat.lt_of_le_of_lt mid.property.2 ln)) <o arr[first] := by
    have : k < n := Nat.lt_trans km (by assumption)

    cases Nat.eq_or_lt_of_le fk with
    | inl fk =>
      have : swapped[k] = swapped[first] := by
        simp [fk]
      rw [this]
      have : swapped[first] = arr'[mid.val] := by
        apply Vec.get_swap_left
      rw [this, ←first_eq]
      exact inv.3 (fk ▸ km)
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

  have p₃ (k : Nat) (mk : mid < k) (kl : k ≤ last) : ¬swapped[k]'(Nat.lt_of_le_of_lt kl ln) <o arr[first] := by
    have : k < n := Nat.lt_of_le_of_lt kl ln
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
  (arr : Vec α n) (first last : Nat) (ln : last < n)
  (k : Fin n) (lt : k < first) :
  (quickSortImpl arr first last ln)[k] = arr[k] := by
  let p := quickSortImpl_permuted arr first last ln
  exact p.get_lt lt

theorem quickSortImpl.get_gt {α : Type} [Ord α] {n : Nat}
  (arr : Vec α n) (first last : Nat) (ln : last < n)
  (k : Fin n) (gt : k > last) :
  (quickSortImpl arr first last ln)[k] = arr[k] := by
  let p := quickSortImpl_permuted arr first last ln
  exact p.get_gt gt

theorem quickSortImpl_sortedRange {α : Type} [Order α] {n : Nat}
  (arr : Vec α n) (first last : Nat) (ln : last < n) :
  sortedRange (quickSortImpl arr first last ln) first last := by
  induction arr, first, last, ln using quickSortImpl.induct with
  | base arr first last ln h =>
    simp [*]
    intro i j fi ij jl
    have : first = last := Nat.le_antisymm (Nat.le_trans (Nat.le_trans fi ij) jl) (Nat.le_of_not_gt h)
    subst this
    have hi : i = first := Nat.le_antisymm (Nat.le_trans ij jl) fi
    have hj : j = first := Nat.le_antisymm jl (Nat.le_trans fi ij)
    have : i = j := by
      apply Fin.eq_of_val_eq
      simp [hi, hj]
    subst this
    apply Order.refl
  | step arr first last ln lt parted eq ih₁ ih₂ =>
    simp [*]
    intro i j fi ij jl

    let mid := parted.1
    have : first < n := Nat.lt_trans lt ln
    have mn : mid.val < n := Nat.lt_of_le_of_lt mid.property.2 ln
    have : mid.val - 1 < n := Nat.lt_of_le_of_lt (Nat.sub_le ..) mn
    let sorted := quickSortImpl (quickSortImpl parted.snd first (parted.fst.val - 1) (by assumption))
      (parted.fst.val + 1) last ln

    let ⟨l, m, r⟩ := partition.partition arr first last (Nat.le_of_lt lt) ln parted eq

    have getL (k : Fin n) (fk : first ≤ k) (km : k < mid.val) : sorted[k] <o arr[first] := by
      rw [quickSortImpl.get_lt (lt := (Nat.lt_trans km (Nat.lt_succ_self ..)))]
      let p := quickSortImpl_permuted parted.2 first (mid.val - 1) (by assumption)
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
        rw [←m]
        simp [zero]
        rfl
      | inr pos =>
        rw [quickSortImpl.get_gt (k := mid') (gt := Nat.sub_lt_self (by decide) (Nat.zero_lt_of_lt pos))]
        exact m

    have getR (k : Fin n) (mk : mid.val < k) (kl : k ≤ last) : ¬sorted[k] <o arr[first] := by
      let p := quickSortImpl_permuted (quickSortImpl parted.snd first (parted.fst.val - 1) (by assumption)) (mid.val + 1) last ln
      let ⟨k', ⟨index, mk', kl'⟩⟩ := permuted_map_index_in_range_inv p k mk kl
      let inv := index ▸ permuted_map_index p k'
      rw [←inv]
      rw [quickSortImpl.get_gt (gt := Nat.lt_of_le_of_lt (Nat.sub_le ..) mk')]
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
