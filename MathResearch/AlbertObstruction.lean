import Mathlib.Algebra.Quaternion
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import MathResearch.MinimalAInfinity

/-!
# A concrete obstruction in rational Albert coordinates

The underlying coordinates are 3 scalar diagonal entries and 3 octonion
off-diagonal entries (27 rational coordinates). Octonions are quaternion pairs,
with the Cayley-Dickson convention in Baez, The Octonions, section 2.2.
The Jordan operation is read from (XY + YX)/2 on the corresponding Hermitian
3x3 matrix. Matrix multiplication here is explicitly non-associative.

We do NOT assume/prove the full Jordan identity, norm composition, a real-form
classification, or an isomorphism to E10. The decisive counterexample uses
scalar entries, but is evaluated in these actual 27-coordinate operations.
-/

namespace MathResearch.Albert

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

abbrev Oct := Quaternion ℚ × Quaternion ℚ

def octScalar (r : ℚ) : Oct := ((r : Quaternion ℚ), 0)

/-- Baez's Cayley-Dickson convention (ac - d b*, a* d + c b). -/
def octMul (x y : Oct) : Oct :=
  (x.1 * y.1 - y.2 * star x.2, star x.1 * y.2 + y.1 * x.2)

def octStar (x : Oct) : Oct := (star x.1, -x.2)

@[ext]
structure Coordinates where
  d₀ : ℚ
  d₁ : ℚ
  d₂ : ℚ
  u₀₁ : Oct
  u₀₂ : Oct
  u₁₂ : Oct

/-- A faithful placement of the 27 coordinates in a Hermitian matrix. -/
def toMatrix (x : Coordinates) : Fin 3 → Fin 3 → Oct :=
  ![![octScalar x.d₀, x.u₀₁, x.u₀₂],
    ![octStar x.u₀₁, octScalar x.d₁, x.u₁₂],
    ![octStar x.u₀₂, octStar x.u₁₂, octScalar x.d₂]]

/-- Binary matrix product: each summand is a single octonion product. -/
def matrixMul (x y : Fin 3 → Fin 3 → Oct) (i j : Fin 3) : Oct :=
  octMul (x i 0) (y 0 j) + octMul (x i 1) (y 1 j) + octMul (x i 2) (y 2 j)

def symEntry (x y : Coordinates) (i j : Fin 3) : Oct :=
  (1 / 2 : ℚ) • (matrixMul (toMatrix x) (toMatrix y) i j +
    matrixMul (toMatrix y) (toMatrix x) i j)

/-- The standard coordinate formula for the rational Albert Jordan product. -/
def jordan (x y : Coordinates) : Coordinates where
  d₀ := (symEntry x y 0 0).1.re
  d₁ := (symEntry x y 1 1).1.re
  d₂ := (symEntry x y 2 2).1.re
  u₀₁ := symEntry x y 0 1
  u₀₂ := symEntry x y 0 2
  u₁₂ := symEntry x y 1 2

def P : Coordinates := ⟨1, 0, 0, octScalar 0, octScalar 0, octScalar 0⟩
def Q : Coordinates := ⟨0, 0, 0, octScalar 1, octScalar 0, octScalar 0⟩

theorem left_bracketing_value :
    (jordan (jordan P P) Q).u₀₁.1.re = (1 / 2 : ℚ) := by
  decide +kernel

theorem right_bracketing_value :
    (jordan P (jordan P Q)).u₀₁.1.re = (1 / 4 : ℚ) := by
  decide +kernel

theorem nonassociative_witness : jordan (jordan P P) Q ≠ jordan P (jordan P Q) := by
  intro h
  have hcoord := congrArg (fun x : Coordinates => x.u₀₁.1.re) h
  change (jordan (jordan P P) Q).u₀₁.1.re = (jordan P (jordan P Q)).u₀₁.1.re at hcoord
  rw [left_bracketing_value, right_bracketing_value] at hcoord
  norm_num at hcoord

theorem not_minimal_binary_condition : ¬ MathResearch.MinimalBinaryCondition jordan :=
  MathResearch.witness_excludes_minimal_binary jordan P P Q nonassociative_witness

#print axioms left_bracketing_value
#print axioms right_bracketing_value
#print axioms nonassociative_witness
#print axioms not_minimal_binary_condition

end MathResearch.Albert
