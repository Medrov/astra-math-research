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


theorem Heldout.refute_third_edge : ¬ (∀ (w01 w12 a b x0 x1 x2 : ℝ), a < b → TriangleEnergy.laplacianForm w01 w12 a x0 x1 x2 < TriangleEnergy.laplacianForm w01 w12 b x0 x1 x2) := by
  intro h
  have hbad := h 1 1 0 1 0 0 0 (by exact zero_lt_one)
  simpa [TriangleEnergy.laplacianForm] using hbad

