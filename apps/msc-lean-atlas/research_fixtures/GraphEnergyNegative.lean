import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace TriangleEnergy

/-- The same three-edge energy, with arbitrary real weights. -/
def graphEnergy (w01 w12 w02 x0 x1 x2 : ℝ) : ℝ :=
  w01 * (x0 - x1)^2 + w12 * (x1 - x2)^2 + w02 * (x0 - x2)^2

/-- The same coordinate expression for the weighted Laplacian form. -/
def laplacianForm (w01 w12 w02 x0 x1 x2 : ℝ) : ℝ :=
  x0 * (w01 * (x0 - x1) + w02 * (x0 - x2)) +
  x1 * (w01 * (x1 - x0) + w12 * (x1 - x2)) +
  x2 * (w02 * (x2 - x0) + w12 * (x2 - x1))

theorem graph_energy_eq (w01 w12 w02 x0 x1 x2 : ℝ) :
    graphEnergy w01 w12 w02 x0 x1 x2 = laplacianForm w01 w12 w02 x0 x1 x2 := by
  unfold graphEnergy laplacianForm
  ring

end TriangleEnergy

namespace TriangleEnergyNegative

/-- A negative edge weight gives a genuinely negative form value. -/
theorem negative_weight_witness :
    TriangleEnergy.laplacianForm (-1) 0 0 1 0 0 = -1 := by
  rw [← TriangleEnergy.graph_energy_eq]
  norm_num [TriangleEnergy.graphEnergy]

/-- The representation identity survives; its unconditional positivity claim does not. -/
theorem unconditional_nonnegativity_refuted :
    ¬ (∀ (w01 w12 w02 x0 x1 x2 : ℝ),
      0 ≤ TriangleEnergy.laplacianForm w01 w12 w02 x0 x1 x2) := by
  intro h
  have hnegative := h (-1) 0 0 1 0 0
  rw [negative_weight_witness] at hnegative
  norm_num at hnegative

end TriangleEnergyNegative
