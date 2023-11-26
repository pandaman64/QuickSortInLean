import QuickSortInLean.Vec
import QuickSortInLean.QuickSort
import QuickSortInLean.Induction
import QuickSortInLean.QuickSortPermutation

def sortedRange [Ord α] (arr : Vec α n) (first last : Nat) : Prop :=
  ∀i j : Fin n, first ≤ i → i ≤ j → j ≤ last → (compare arr[i] arr[j]).isLE

def sorted [Ord α] (arr : Vec α n) : Prop :=
  ∀i j : Fin n, i ≤ j → (compare arr[i] arr[j]).isLE

structure LawfulOrd (α : Type) [Ord α] where
  trans : ∀x y z : α, (compare x y).isLE → (compare y z).isLE → (compare x z).isLE
  antisymm : ∀x y : α, (compare x y).isLE → (compare y x).isLE → x = y
  total : ∀x y : α, (compare x y).isLE ∨ (compare y x).isLE

theorem LawfulOrd.refl [Ord α] (law : LawfulOrd α) (x : α) : (compare x x).isLE :=
  match law.total x x with
  | .inl xy => xy
  | .inr yx => yx

#check BEq
#check LawfulBEq

theorem Ordering.not_lt_of_eq [Ord α] (law : LawfulOrd α) {x : α} : ¬x <o x := by
  sorry

theorem Ordering.le_of_not_lt [Ord α] (law : LawfulOrd α) {x y : α} (h : ¬x <o y) : (compare y x).isLE := by
  sorry

-- theorem Ordering.le_of_not_lt [Ord α] (law : LawfulOrd α) {x y : α} (h : ¬x <o y) : (compare y x).isLE :=
--   have h : ¬(compare x y = .lt) := sorry
--   match law.total x y with
--   | .inl xy => match cmp : compare x y with
--     | .lt => absurd cmp h
--     | .eq => sorry
--     | .gt => by
--       simp [isLE] at xy
--       contradiction
--   | .inr yx => yx

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
  | ge : x ≤ i → x ≤ j → Nat.RangeSplit i j x ij
  | split : i < x → x ≤ j → Nat.RangeSplit i j x ij

def Nat.range_split (i j x : Nat) (ij : i ≤ j) : Nat.RangeSplit i j x ij :=
  match Nat.decLt i x, Nat.decLt j x with
  | isTrue ix, isTrue jx => .lt ix jx
  | isTrue ix, isFalse jx => .split ix (Nat.le_of_not_lt jx)
  | isFalse ix, isTrue jx =>
    nomatch Nat.lt_irrefl x (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_of_not_lt ix) ij) jx)
  | isFalse ix, isFalse jx => .ge (Nat.le_of_not_lt ix) (Nat.le_of_not_lt jx)

theorem partitionImpl.get_lt {α : Type} [Ord α] {n : Nat}
  (arr : Vec α n) (first i j : Nat)
  (fi : first ≤ i) (ij : i ≤ j) (jn : j < n)
  (k : Fin n) (lt : k < first) :
  (partitionImpl arr first i j fi ij jn).2[k] = arr[k] := by
  induction arr, first, i, j, fi, ij, jn using partitionImpl.induct with
  | base => simp [*]
  | step_lt => simp [*]
  | step_ge _ _ _ _ fi ij =>
    simp [*]
    apply Vec.get_swap_neq
    . apply Fin.ne_of_val_ne
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le lt fi)
    . apply Fin.ne_of_val_ne
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le lt (Nat.le_trans fi ij))

theorem quickSortImpl.get_lt {α : Type} [Ord α] {n : Nat}
  (arr : Vec α n) (first last : Nat) (ln : last < n)
  (k : Fin n) (lt : k < first) :
  (quickSortImpl arr first last ln)[k] = arr[k] := by
  induction arr, first, last, ln using quickSortImpl.induct with
  | base => simp [*]
  | step arr first last ln fl parted eq ih₁ ih₂ =>
    let afterLoop := partitionImpl arr first last last (Nat.le_of_lt fl) .refl ln
    have : k.val < parted.1.val + 1 :=
      Nat.lt_of_lt_of_le lt (Nat.le_trans parted.1.property.1 (Nat.le_succ _))
    simp [*]
    rw [←eq, partition]
    simp [dbgTraceIfShared]
    conv =>
      lhs
      tactic =>
        apply Vec.get_swap_neq
        . apply Fin.ne_of_val_ne
          exact Nat.ne_of_lt lt
        . apply Fin.ne_of_val_ne
          exact Nat.ne_of_lt (Nat.lt_of_lt_of_le lt afterLoop.1.property.1)
    apply partitionImpl.get_lt (lt := lt)

theorem partitionImpl.get_gt {α : Type} [Ord α] {n : Nat}
  (arr : Vec α n) (first i j : Nat)
  (fi : first ≤ i) (ij : i ≤ j) (jn : j < n)
  (k : Fin n) (gt : k > j) :
  (partitionImpl arr first i j fi ij jn).2[k] = arr[k] := by
  induction arr, first, i, j, fi, ij, jn using partitionImpl.induct with
  | base => simp [*]
  | step_lt => simp [*]
  | step_ge arr _ i j fi ij =>
    have : k.val > j - 1 := Nat.lt_of_le_of_lt (Nat.sub_le ..) gt
    simp [*]
    apply Vec.get_swap_neq
    . apply Fin.ne_of_val_ne
      exact Nat.ne_of_gt (Nat.lt_of_le_of_lt ij gt)
    . apply Fin.ne_of_val_ne
      exact Nat.ne_of_gt gt

theorem quickSortImpl.get_gt {α : Type} [Ord α] {n : Nat}
  (arr : Vec α n) (first last : Nat) (ln : last < n)
  (k : Fin n) (gt : k > last) :
  (quickSortImpl arr first last ln)[k] = arr[k] := by
  induction arr, first, last, ln using quickSortImpl.induct with
  | base => simp [*]
  | step arr first last ln fl parted eq ih₁ ih₂ =>
    let afterLoop := partitionImpl arr first last last (Nat.le_of_lt fl) .refl ln
    have : k.val > parted.fst.val - 1 :=
      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le ..) parted.1.property.2) gt
    simp [*]
    rw [←eq, partition]
    simp [dbgTraceIfShared]
    conv =>
      lhs
      tactic =>
        apply Vec.get_swap_neq
        . apply Fin.ne_of_val_ne
          exact Nat.ne_of_gt (Nat.lt_trans fl gt)
        . apply Fin.ne_of_val_ne
          exact Nat.ne_of_gt (Nat.lt_of_le_of_lt afterLoop.1.property.2 gt)
    apply partitionImpl.get_gt (gt := gt)

-- theorem swap_preserve_lt {α : Type} [Ord α] {n : Nat}
--   (arr : Vec α n) (i j : Fin n) (first last : Nat)
--   (x : α) (h : ∀k : Fin n, first ≤ k → k ≤ last → arr[k] <o x) :
--   ∀k : Fin n, first ≤ k → k ≤ last → (arr.swap i j)[k] <o x := by
--   intro k
--   match decEq k i, decEq k j with
--   | isFalse ki, isFalse kj =>
--     rw [Vec.get_swap_neq _ _ _ _ ki kj]
--     exact h k
--   | isTrue ki, _ =>
--     intro fk kl
--     rw [ki]
--     rw [Vec.get_swap_left]
--     exact h fk kl
--   | _, isTrue kj =>
--     rw [kj]
--     rw [Vec.get_swap_right]
--     exact h i

-- theorem permuted_preserve_lt {α : Type} [Ord α] {n : Nat}
--   (arr arr': Vec α n) (p : permuted n arr arr')
--   (x : α) (h : ∀k : Fin n, arr[k] <o x) :
--   ∀k : Fin n, arr'[k] <o x := by
--   intro k
--   induction p with
--   | refl => exact h k
--   | step i j p ih => sorry

-- theorem quickSortImpl_preserve_lt {α : Type} [Ord α] {n : Nat}
--   (arr : Vec α n) (first last : Nat) (ln : last < n)
--   (x : α) (h : ∀k : Fin n, first ≤ k → k ≤ last → arr[k] <o x) :
--   ∀k : Fin n, first ≤ k → k ≤ last → (quickSortImpl arr first last ln)[k] <o x := by
--   induction arr, first, last, ln using quickSortImpl.induct with
--   | base => simp [*]; assumption
--   | step arr first last ln fl parted eq ih₁ ih₂ =>
--     simp [*]
--     intro k fk kl
--     sorry

theorem quickSortImpl_sortedRange {α : Type} [Ord α] (law : LawfulOrd α) {n : Nat}
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
    apply law.refl
  | step arr first last ln lt parted eq ih₁ ih₂ =>
    simp [*]
    let mid := parted.1
    intro i j fi ij jl

    let ⟨l, m, r⟩ := partition.partition arr first last (Nat.le_of_lt lt) ln parted eq

    cases Nat.range_split i j mid ij with
    | lt im jm =>
      conv =>
        lhs
        arg 1
        congr
        . tactic =>
            apply quickSortImpl.get_lt (lt := Nat.lt_trans im (Nat.lt_succ_self ..))
        . tactic =>
            apply quickSortImpl.get_lt (lt := Nat.lt_trans jm (Nat.lt_succ_self ..))
      exact ih₁ i j fi ij (Nat.le_sub_of_add_le jm)
    | ge mi mj =>
      cases Nat.lt_or_eq_of_le mi with
      | inl mi => exact ih₂ i j mi ij jl
      | inr mi =>
        let mid' : Fin n := ⟨mid.val, Nat.lt_of_le_of_lt mid.property.2 ln⟩
        have : mid'.val - 1 < n := Nat.lt_of_le_of_lt (Nat.sub_le ..) mid'.isLt
        have : i = mid' := by
          apply Fin.eq_of_val_eq
          simp [mi]
        rw [this]
        conv in compare _ _ =>
          arg 1
          apply quickSortImpl.get_lt (lt := by simp)
        have : (quickSortImpl parted.2 first (mid.val - 1) (by assumption))[mid'] = parted.2[mid'] := by
          cases Nat.eq_zero_or_pos mid.val with
          | inl eq => simp [eq]
          | inr pos => apply quickSortImpl.get_gt (gt := by simp; apply Nat.sub_lt pos (by decide))
        rw [this]

        have motive : ¬(quickSortImpl (quickSortImpl parted.2 first (parted.fst.val - 1) (by assumption))
          (mid' + 1) last ln)[j] <o parted.2[mid'] := by
          conv in _ <o _ =>
            rhs
            rw [Vec.getElem_eq_getElem]
            apply m

          cases Nat.eq_or_lt_of_le mj with
          | inl eq =>
            conv in _ <o _ =>
              arg 1
              apply quickSortImpl.get_lt (lt := by simp [eq])
            have jm : j = mid' := by
              apply Fin.eq_of_val_eq
              simp [eq]
            have : (quickSortImpl parted.2 first (parted.1.val - 1) (by assumption))[mid'] = parted.2[mid'] := by
              cases Nat.eq_zero_or_pos mid.val with
              | inl eq => simp [eq]
              | inr pos => apply quickSortImpl.get_gt (gt := by simp; apply Nat.sub_lt pos (by decide))
            simp [jm, this]
            show ¬parted.2[mid.val]'(eq.symm ▸ j.isLt) <o arr[first]'(Nat.lt_trans lt ln)
            rw [m]
            apply Ordering.not_lt_of_eq law
          | inr lt =>
            let r := r j lt jl
            sorry -- propagate order through quickSortImpl
        exact Ordering.le_of_not_lt law motive
    | split => sorry

#check Nat.sub_lt_right_of_lt_add
#check Nat.le_of_le_of_sub_le_sub_right
#check Nat.le_sub_of_add_le
#check Nat.lt_succ_of_lt
#check Nat.lt_succ_self
#check Fin
#check Nat.sub_lt
#check Array.get_eq_getElem
