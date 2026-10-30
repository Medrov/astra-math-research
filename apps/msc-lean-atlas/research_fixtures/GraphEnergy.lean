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
theorem graph_energy_eq (w01 w12 w02 x0 x1 x2 : ℝ) :
    graphEnergy w01 w12 w02 x0 x1 x2 = laplacianForm w01 w12 w02 x0 x1 x2 := by
  unfold graphEnergy laplacianForm
  ring
/-- Positivity crosses the representation boundary through graph_energy_eq. -/
theorem laplacian_nonnegative (w01 w12 w02 x0 x1 x2 : ℝ)
    (h01 : 0 ≤ w01) (h12 : 0 ≤ w12) (h02 : 0 ≤ w02) :
    0 ≤ laplacianForm w01 w12 w02 x0 x1 x2 := by
  rw [← graph_energy_eq]
  unfold graphEnergy
  positivity
end TriangleEnergy
