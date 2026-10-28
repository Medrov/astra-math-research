import MathResearch.AlbertMatrix
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Diagonal Albert associators and one-dimensional distance geometry

The Peirce multiplication coefficients and rigidity of labeled distances are
classical. This file investigates their precise combination in the verified
27-coordinate model: its diagonal associator encodes squared distances between
the three diagonal values. The operator acts on octonion edge coordinates; it
is an edge-weight multiplier, not itself a graph Laplacian on vertex values.
No claim of a previously unknown mathematical result is made by this file.
-/

namespace MathResearch.AlbertSpectralGeometry

open MathResearch.Albert

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

/-- A diagonal element in the actual rational 27-coordinate model. -/
def diagonal (d : Fin 3 → ℚ) : Coordinates :=
  ⟨d 0, d 1, d 2, octScalar 0, octScalar 0, octScalar 0⟩

theorem octScalar_zero : octScalar 0 = (0 : Oct) := by
  apply Prod.ext <;> simp [octScalar]

theorem octStar_scalar (r : ℚ) : octStar (octScalar r) = octScalar r := by
  apply Prod.ext <;> simp [octStar, octScalar]

theorem octMul_scalar_left (r : ℚ) (x : Oct) : octMul (octScalar r) x = r • x := by
  apply Prod.ext <;> ext <;> simp [octMul, octScalar]

theorem octMul_scalar_right (r : ℚ) (x : Oct) : octMul x (octScalar r) = r • x := by
  apply Prod.ext <;> ext <;> simp [octMul, octScalar] <;> ring

theorem octMul_zero_left (x : Oct) : octMul 0 x = 0 := by
  simpa [octScalar_zero] using octMul_scalar_left 0 x

theorem octMul_zero_right (x : Oct) : octMul x 0 = 0 := by
  simpa [octScalar_zero] using octMul_scalar_right 0 x

theorem octStar_zero : octStar (0 : Oct) = 0 := by
  apply Prod.ext <;> simp [octStar]

/-- The action is exact for arbitrary octonion coordinates, not only scalar entries. -/
theorem jordan_diagonal (d : Fin 3 → ℚ) (x : Coordinates) :
    jordan (diagonal d) x =
      ⟨d 0 * x.d₀, d 1 * x.d₁, d 2 * x.d₂,
        ((d 0 + d 1) / 2) • x.u₀₁,
        ((d 0 + d 2) / 2) • x.u₀₂,
        ((d 1 + d 2) / 2) • x.u₁₂⟩ := by
  apply Coordinates.ext <;>
    simp [jordan, diagonal, symEntry, matrixMul, toMatrix, octMul_scalar_left,
      octMul_scalar_right, octStar_scalar, octMul_zero_left, octMul_zero_right,
      octStar_zero, octScalar_zero, add_smul, smul_smul]
  all_goals try simp [octScalar]
  all_goals try ring_nf
  all_goals rw [← add_smul]

/-- Coordinate subtraction, without assuming additional structure on `Coordinates`. -/
def subtract (x y : Coordinates) : Coordinates :=
  ⟨x.d₀ - y.d₀, x.d₁ - y.d₁, x.d₂ - y.d₂,
    x.u₀₁ - y.u₀₁, x.u₀₂ - y.u₀₂, x.u₁₂ - y.u₁₂⟩

/-- The actual associator with the diagonal element repeated twice. -/
def diagonalDefect (d : Fin 3 → ℚ) (x : Coordinates) : Coordinates :=
  subtract (jordan (jordan (diagonal d) (diagonal d)) x)
    (jordan (diagonal d) (jordan (diagonal d) x))

/-- A quarter of the squared distance between two labeled diagonal entries. -/
def edgeWeight (d : Fin 3 → ℚ) (i j : Fin 3) : ℚ := (d i - d j) ^ 2 / 4

/-- Three octonion edge fibers, each multiplied by its scalar distance weight. -/
def weightedOffDiagonal (d : Fin 3 → ℚ) (x : Coordinates) : Coordinates :=
  ⟨0, 0, 0, edgeWeight d 0 1 • x.u₀₁,
    edgeWeight d 0 2 • x.u₀₂, edgeWeight d 1 2 • x.u₁₂⟩

theorem diagonal_square (d : Fin 3 → ℚ) :
    jordan (diagonal d) (diagonal d) = diagonal (fun i => (d i) ^ 2) := by
  rw [jordan_diagonal]
  apply Coordinates.ext <;> simp [diagonal, octScalar_zero, pow_two]

/-- The squared-distance action holds on all 27 coordinates. -/
theorem diagonalDefect_formula (d : Fin 3 → ℚ) (x : Coordinates) :
    diagonalDefect d x = weightedOffDiagonal d x := by
  unfold diagonalDefect
  rw [diagonal_square]
  simp only [jordan_diagonal]
  apply Coordinates.ext <;> simp only [subtract, weightedOffDiagonal, edgeWeight]
  all_goals try ring_nf
  all_goals rw [smul_smul, ← sub_smul]
  all_goals congr 1
  all_goals ring

/-- The scalar weights are nonnegative in the ordered rational field. -/
theorem edgeWeight_nonnegative (d : Fin 3 → ℚ) (i j : Fin 3) :
    0 ≤ edgeWeight d i j := by
  unfold edgeWeight
  exact div_nonneg (sq_nonneg _) (by norm_num)

theorem fin3_pointwise {f g : Fin 3 → ℚ}
    (h₀ : f 0 = g 0) (h₁ : f 1 = g 1) (h₂ : f 2 = g 2) : ∀ i, f i = g i := by
  intro i
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂

/-- Labeled squared distances of three points on a line determine them up to
translation or reflection. Coincident entries are included. -/
theorem squared_distances_rigid (d e : Fin 3 → ℚ)
    (h₀₁ : (d 0 - d 1) ^ 2 = (e 0 - e 1) ^ 2)
    (h₀₂ : (d 0 - d 2) ^ 2 = (e 0 - e 2) ^ 2)
    (h₁₂ : (d 1 - d 2) ^ 2 = (e 1 - e 2) ^ 2) :
    (∃ c : ℚ, ∀ i, e i = d i + c) ∨ (∃ c : ℚ, ∀ i, e i = -d i + c) := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h₀₁ with ha | ha <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h₀₂ with hb | hb
  · left
    refine ⟨e 0 - d 0, ?_⟩
    apply fin3_pointwise <;> dsimp only <;> linarith
  · have he₁ : e 1 = e 0 - d 0 + d 1 := by linarith
    have he₂ : e 2 = e 0 + d 0 - d 2 := by linarith
    rw [he₁, he₂] at h₁₂
    have hp : (d 0 - d 1) * (d 0 - d 2) = 0 := by nlinarith [h₁₂]
    rcases mul_eq_zero.mp hp with hz | hz
    · right
      refine ⟨e 0 + d 0, ?_⟩
      apply fin3_pointwise <;> dsimp only <;> linarith
    · left
      refine ⟨e 0 - d 0, ?_⟩
      apply fin3_pointwise <;> dsimp only <;> linarith
  · have he₁ : e 1 = e 0 + d 0 - d 1 := by linarith
    have he₂ : e 2 = e 0 - d 0 + d 2 := by linarith
    rw [he₁, he₂] at h₁₂
    have hp : (d 0 - d 1) * (d 0 - d 2) = 0 := by nlinarith [h₁₂]
    rcases mul_eq_zero.mp hp with hz | hz
    · left
      refine ⟨e 0 - d 0, ?_⟩
      apply fin3_pointwise <;> dsimp only <;> linarith
    · right
      refine ⟨e 0 + d 0, ?_⟩
      apply fin3_pointwise <;> dsimp only <;> linarith
  · right
    refine ⟨e 0 + d 0, ?_⟩
    apply fin3_pointwise <;> dsimp only <;> linarith

def probe₀₁ : Coordinates :=
  ⟨0, 0, 0, octScalar 1, octScalar 0, octScalar 0⟩

def probe₀₂ : Coordinates :=
  ⟨0, 0, 0, octScalar 0, octScalar 1, octScalar 0⟩

def probe₁₂ : Coordinates :=
  ⟨0, 0, 0, octScalar 0, octScalar 0, octScalar 1⟩

/-- Testing three scalar probes recovers the three weights of the full
octonion-fiber operator. -/
theorem edgeWeights_of_defect_eq (d e : Fin 3 → ℚ)
    (h : diagonalDefect d = diagonalDefect e) :
    edgeWeight d 0 1 = edgeWeight e 0 1 ∧
      edgeWeight d 0 2 = edgeWeight e 0 2 ∧
      edgeWeight d 1 2 = edgeWeight e 1 2 := by
  have h₀₁ := congrArg (fun F : Coordinates → Coordinates => (F probe₀₁).u₀₁.1.re) h
  have h₀₂ := congrArg (fun F : Coordinates → Coordinates => (F probe₀₂).u₀₂.1.re) h
  have h₁₂ := congrArg (fun F : Coordinates → Coordinates => (F probe₁₂).u₁₂.1.re) h
  constructor
  · simpa [diagonalDefect_formula, weightedOffDiagonal, probe₀₁, octScalar] using h₀₁
  constructor
  · simpa [diagonalDefect_formula, weightedOffDiagonal, probe₀₂, octScalar] using h₀₂
  · simpa [diagonalDefect_formula, weightedOffDiagonal, probe₁₂, octScalar] using h₁₂

/-- Exact inverse statement for the actual Albert associator operators.
The only ambiguity is a common scalar translation or reflection. -/
theorem diagonalDefect_eq_iff_translation_or_reflection (d e : Fin 3 → ℚ) :
    diagonalDefect d = diagonalDefect e ↔
      (∃ c : ℚ, ∀ i, e i = d i + c) ∨ (∃ c : ℚ, ∀ i, e i = -d i + c) := by
  constructor
  · intro h
    obtain ⟨h₀₁, h₀₂, h₁₂⟩ := edgeWeights_of_defect_eq d e h
    unfold edgeWeight at h₀₁ h₀₂ h₁₂
    apply squared_distances_rigid d e <;> linarith
  · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
    all_goals funext x
    all_goals rw [diagonalDefect_formula, diagonalDefect_formula]
    all_goals apply Coordinates.ext
    all_goals simp only [weightedOffDiagonal, edgeWeight, hc]
    all_goals congr 1
    all_goals ring

/-- The incidence gradient of three vertex values, embedded into scalar
elements of the three octonion edge fibers. -/
def gradient (f : Fin 3 → ℚ) : Coordinates :=
  ⟨0, 0, 0, octScalar (f 0 - f 1), octScalar (f 0 - f 2), octScalar (f 1 - f 2)⟩

/-- The weighted graph Laplacian on vertex values. Its edge weights come from
the diagonal Albert associator, not from a change to the octonion product. -/
def graphLaplacian (d f : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![edgeWeight d 0 1 * (f 0 - f 1) + edgeWeight d 0 2 * (f 0 - f 2),
    edgeWeight d 0 1 * (f 1 - f 0) + edgeWeight d 1 2 * (f 1 - f 2),
    edgeWeight d 0 2 * (f 2 - f 0) + edgeWeight d 1 2 * (f 2 - f 1)]

/-- The scalar edge pairing with the actual associator applied to the gradient.
Each upper-triangular edge is counted once. -/
def associatorDirichlet (d f : Fin 3 → ℚ) : ℚ :=
  (diagonalDefect d (gradient f)).u₀₁.1.re * (f 0 - f 1) +
    (diagonalDefect d (gradient f)).u₀₂.1.re * (f 0 - f 2) +
    (diagonalDefect d (gradient f)).u₁₂.1.re * (f 1 - f 2)

theorem associatorDirichlet_squares (d f : Fin 3 → ℚ) :
    associatorDirichlet d f =
      edgeWeight d 0 1 * (f 0 - f 1) ^ 2 +
        edgeWeight d 0 2 * (f 0 - f 2) ^ 2 +
        edgeWeight d 1 2 * (f 1 - f 2) ^ 2 := by
  simp [associatorDirichlet, diagonalDefect_formula, weightedOffDiagonal, gradient, octScalar]
  ring

/-- The exact incidence-transpose pairing produces graph Laplacian energy. -/
theorem associatorDirichlet_graphLaplacian (d f : Fin 3 → ℚ) :
    associatorDirichlet d f =
      f 0 * graphLaplacian d f 0 + f 1 * graphLaplacian d f 1 +
        f 2 * graphLaplacian d f 2 := by
  rw [associatorDirichlet_squares]
  simp [graphLaplacian]
  ring

theorem associatorDirichlet_nonnegative (d f : Fin 3 → ℚ) :
    0 ≤ associatorDirichlet d f := by
  rw [associatorDirichlet_squares]
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (edgeWeight_nonnegative d 0 1) (sq_nonneg _))
      (mul_nonneg (edgeWeight_nonnegative d 0 2) (sq_nonneg _)))
    (mul_nonneg (edgeWeight_nonnegative d 1 2) (sq_nonneg _))

#print axioms octScalar_zero
#print axioms octStar_scalar
#print axioms octMul_scalar_left
#print axioms octMul_scalar_right
#print axioms octMul_zero_left
#print axioms octMul_zero_right
#print axioms octStar_zero
#print axioms jordan_diagonal
#print axioms diagonal_square
#print axioms diagonalDefect_formula
#print axioms edgeWeight_nonnegative
#print axioms fin3_pointwise
#print axioms squared_distances_rigid
#print axioms edgeWeights_of_defect_eq
#print axioms diagonalDefect_eq_iff_translation_or_reflection
#print axioms associatorDirichlet_squares
#print axioms associatorDirichlet_graphLaplacian
#print axioms associatorDirichlet_nonnegative

end MathResearch.AlbertSpectralGeometry
