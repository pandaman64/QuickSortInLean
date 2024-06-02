import QuickSortInLean.Order
import QuickSortInLean.Vec

theorem sorted_of_adjacentSorted {α : Type} [Order α] {n : Nat}
  (arr : Vec α n)
  (assms : ∀i : Nat, (isLt : i + 1 < n) → arr[i]'(Nat.lt_of_le_of_lt (Nat.le_succ ..) isLt) ≤o arr[i + 1]'isLt)
  (j k : Nat) (kn : k < n) (jk : j ≤ k) :
  arr[j]'(Nat.lt_of_le_of_lt jk kn) ≤o arr[k] := by
  induction jk with
  | refl => exact Order.refl
  | step h ih =>
    apply Order.trans
    . exact ih (Nat.lt_of_le_of_lt (Nat.le_succ ..) kn)
    . apply assms
