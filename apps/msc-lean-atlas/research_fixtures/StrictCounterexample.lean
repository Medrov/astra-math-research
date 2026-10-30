import Mathlib.Data.Real.Basic
namespace StrictInequality
/-- A checked witness refutes the universal strict inequality. -/
theorem counterexample : ¬ (∀ a b : ℝ, 2 * a * b < a ^ 2 + b ^ 2) := by
  intro h
  have hzero := h 0 0
  norm_num at hzero
end StrictInequality
