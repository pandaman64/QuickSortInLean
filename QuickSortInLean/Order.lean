import Init.Data.Ord

-- Workaround for Ord not inheriting from LT
infix:50 " <o " => ltOfOrd.lt
infix:50 " ≤o " => leOfOrd.le

class Order (α : Type) extends Ord α where
  trans : ∀{x y z : α}, x ≤o y → y ≤o z → x ≤o z
  asymm : ∀{x y : α}, x ≤o y → y ≤o x → x = y
  symm : ∀{x y : α}, (compare x y).swap = compare y x

theorem Order.total [Order α] (x y : α) : x ≤o y ∨ y ≤o x := by
  show (compare x y).isLE ∨ (compare y x).isLE
  match cmp : compare x y with
  | .lt | .eq => simp [Ordering.isLE, cmp]
  | .gt =>
    apply Or.inr
    rw [←symm, cmp]
    decide

theorem Order.cmp_eq_of_eq [Order α] {x : α} : compare x x = Ordering.eq := by
  match cmp : compare x x with
  | .eq => rfl
  | .lt =>
    have h₁ : (compare x x).swap = .gt := by rw [cmp]; decide
    have h₂ : (compare x x).swap = .lt := by rw [symm]; assumption
    rw [h₂] at h₁
    contradiction
  | .gt =>
    have h₁ : (compare x x).swap = .lt := by rw [cmp]; decide
    have h₂ : (compare x x).swap = .gt := by rw [symm]; assumption
    rw [h₂] at h₁
    contradiction

theorem Order.refl [Order α] {x : α} : x ≤o x := by
  show (compare x x).isLE
  simp [cmp_eq_of_eq]
  decide

theorem Order.irrefl [Order α] {x : α} : ¬x <o x := by
  simp [ltOfOrd, cmp_eq_of_eq]

theorem Order.le_of_not_lt [Order α] {x y : α} (h : ¬(y <o x)) : x ≤o y := by
  show (compare x y).isLE
  match cmp : compare x y with
  | .lt | .eq => decide
  | .gt =>
    simp [ltOfOrd] at h
    have : compare y x = .lt := by rw [←symm, cmp]; decide
    rw [this] at h
    contradiction

theorem Order.not_lt_of_le [Order α] {x y : α} (h : x ≤o y) : ¬(y <o x) := by
  match cmp : compare x y with
  | .lt | .eq =>
    simp [ltOfOrd]
    rw [←symm, cmp]
    decide
  | .gt =>
    simp [leOfOrd, cmp] at h
    contradiction

theorem Order.le_of_lt [Order α] {x y : α} (h : x <o y) : x ≤o y := by
  show (compare x y).isLE
  simp [ltOfOrd] at h
  match cmp : compare x y with
  | .lt => decide
  | .eq | .gt =>
    rw [cmp] at h
    contradiction

-- instance : Order Nat where
--   trans x y z := by sorry
--   asymm x y := by sorry
--   symm x y := by
--     simp [compare, compareOfLessAndEq]
--     sorry
