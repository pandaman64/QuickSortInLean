import QuickSortInLean.Permutation
import QuickSortInLean.QuickSort

-- NOTE: somehow we need to write ∃_ : permuted arr arr', True instead of permuted arr arr'.
-- Otherwise, split tactic will not work.
theorem partition'_permutation [Ord α] :
  (partition' (arr : Array α) i j last ij jl la).2 = arr' → ∃_ : permuted arr arr', True := by
  unfold partition'
  split <;> simp [dbgTraceIfShared]
  case inl jl =>
    split
    -- | .lt | .eq
    case h_1 | h_2 =>
      intro eq
      let ⟨ih, _⟩ := partition'_permutation eq
      exact ⟨.step _ _ ih, trivial⟩
    -- | .gt
    case h_3 =>
      intro eq
      exact partition'_permutation eq
  case inr _ =>
    intro eq
    rw [←eq]
    exact ⟨.step _ _ .refl, trivial⟩
termination_by partition'_permutation α arr i j last ij jl la result ord => last - j

theorem partition_permutation [Ord α] :
  (partition (arr : Array α) first last jl la).2 = arr' → ∃_ : permuted arr arr', True := by
    simp [partition]
    exact partition'_permutation

-- TODO: It's really hard to see through the definition of quickSort'.
theorem quickSort'_permutation [Ord α] :
  (quickSort' (arr : Array α) first last la).val = arr' → ∃_ : permuted arr arr', True := by
  sorry

theorem quickSort_permutation [Ord α] :
  (quickSort (arr : Array α)) = arr' → ∃_ : permuted arr arr', True := by
  simp [quickSort]
  split
  case inl => exact quickSort'_permutation
  case inr =>
    intro eq
    rw [eq]
    exact ⟨.refl, trivial⟩

theorem quickSort_map_index_invertible {arr arr' : Array α} [Ord α] :
  quickSort arr = arr' →
  ∃f : Fin arr.size → Fin arr'.size,
    invertible f ∧ (∀i : Fin arr.size, arr[i] = arr'[f i]) := by
  intro eq
  let ⟨p, _⟩ := quickSort_permutation eq
  exact permuted_map_index_invertible p
