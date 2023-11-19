-- Partitions array[first : last + 1] into two parts.
-- The first part contains all elements that are less than or equal to the pivot.
-- The second part contains all elements that are greater than the pivot.
-- It returns the index of the pivot element in the resulting array along with the array.
axiom partition {α : Type} [Ord α]
  (arr : Array α) (first last : Nat) (jl : first ≤ last) (la : last < arr.size) : (Nat × Array α)

-- The pivot index is between first and last.
axiom partition_mid {α : Type} {result : (Nat × Array α)} [Ord α]
  (arr : Array α) (first last : Nat) (jl : first ≤ last) (la : last < arr.size) :
  partition arr first last jl la = result → first ≤ result.1 ∧ result.1 ≤ last

-- The size of the resulting array is the same as the size of the input array.
axiom partition_size {α : Type} {result : (Nat × Array α)} [Ord α]
  (arr : Array α) (first last : Nat) (jl : first ≤ last) (la : last < arr.size) :
  partition arr first last jl la = result → result.2.size = arr.size

partial def quickSort' [Ord α] (arr1 : Array α) (first last : Nat) : Array α :=
  if lt : first < last then
    match hp : partition arr1 first last (sorry : first ≤ last) (sorry : last < arr1.size) with
    | (mid, arr2) =>
      let arr3 := quickSort' arr2 first (mid - 1)
      quickSort' arr3 (mid + 1) last
  else
    arr1

mutual
def quickSort [Ord α] (arr1 : Array α) (first last : Nat) (la : last < arr1.size) : Array α :=
  if lt : first < last then
    match hp : partition arr1 first last (Nat.le_of_lt lt) la with
    | (mid, arr2) =>
      let arr3 := quickSort arr2 first (mid - 1) la
      have la' : last < arr3.size := by
        -- Call mutually recursive theorem
        have : arr3.size = arr1.size := quickSort_size arr2 first (mid - 1) la
        sorry
      quickSort arr3 (mid + 1) last la'
  else
    arr1

theorem quickSort_size [Ord α] (arr1 : Array α) (first last : Nat) (la : last < arr1.size) :
  quickSort arr1 first last la = arr2 → arr2.size = arr1.size :=
  -- Unfolds quickSort and performs induction
  sorry
end
