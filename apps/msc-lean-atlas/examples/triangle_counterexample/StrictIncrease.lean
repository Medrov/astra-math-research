import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
namespace TriangleEnergy
/-- Sum of squared differences over three weighted undirected edges. -/
def graphEnergy (w01 w12 w02 x0 x1 x2 : ℝ) : ℝ :=
  w01 * (x0 - x1)^2 + w12 * (x1 - x2)^2 + w02 * (x0 - x2)^2
/-- Coordinate expression xᵀLx for the weighted triangle Laplacian. -/
def laplacianForm (w01 w12 w02 x0 x1 x2 : ℝ) : ℝ :=
  x0 * (w01 * (x0 - x1) + w02 * (x0 - x2)) +
  x1 * (w01 * (x1 - x0) + w12 * (x1 - x2)) +
  x2 * (w02 * (x2 - x0) + w12 * (x2 - x1))

end TriangleEnergy


theorem TriangleEnergy.graph_energy_eq : ∀ (w01 w12 w02 x0 x1 x2 : ℝ),
  TriangleEnergy.graphEnergy w01 w12 w02 x0 x1 x2 =
  TriangleEnergy.laplacianForm w01 w12 w02 x0 x1 x2 := by
  intro w01 w12 w02 x0 x1 x2
  unfold TriangleEnergy.graphEnergy TriangleEnergy.laplacianForm
  ring


theorem TriangleEnergy.laplacian_third_weight_difference : ∀ (w01 w12 a b x0 x1 x2 : ℝ), TriangleEnergy.laplacianForm w01 w12 b x0 x1 x2 - TriangleEnergy.laplacianForm w01 w12 a x0 x1 x2 = (b - a) * (x0 - x2)^2 := by
  intro w01 w12 a b x0 x1 x2
  unfold TriangleEnergy.laplacianForm
  ring

theorem TriangleEnergy.strict_increase_on_distinct_endpoints : ∀ (w01 w12 a b x0 x1 x2 : ℝ), a < b → x0 ≠ x2 → TriangleEnergy.laplacianForm w01 w12 a x0 x1 x2 < TriangleEnergy.laplacianForm w01 w12 b x0 x1 x2 := by
  intro w01 w12 a b x0 x1 x2 hab hne
  apply sub_pos.mp
  rw [TriangleEnergy.laplacian_third_weight_difference]
  exact mul_pos (sub_pos.mpr hab) (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))

