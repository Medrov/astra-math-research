import MathResearch.AlbertObstruction
import Mathlib.Tactic.Abel

/-!
# Faithful Hermitian coordinates and closure of the rational Albert product

This file verifies that the coordinate product in `AlbertObstruction` is
exactly the symmetrized binary octonionic matrix product at every entry.
The proof uses conjugation and Hermitian symmetry; it does not use or claim
associativity of octonionic matrix multiplication or the full Jordan identity.
-/

namespace MathResearch.Albert

theorem octStar_involutive (x : Oct) : octStar (octStar x) = x := by
  apply Prod.ext <;> simp [octStar]

theorem octStar_add (x y : Oct) : octStar (x + y) = octStar x + octStar y := by
  apply Prod.ext <;> simp [octStar, add_comm]

theorem octStar_smul (r : ℚ) (x : Oct) : octStar (r • x) = r • octStar x := by
  apply Prod.ext <;> simp [octStar, Quaternion.star_smul]

/-- Conjugation reverses a single binary octonion multiplication. -/
theorem octStar_mul (x y : Oct) : octStar (octMul x y) = octMul (octStar y) (octStar x) := by
  apply Prod.ext <;> simp [octStar, octMul, star_mul, add_comm]

/-- Over the rational division octonions, a self-conjugate element is scalar. -/
theorem octStar_self_scalar {x : Oct} (h : octStar x = x) : x = octScalar x.1.re := by
  have h₁ : star x.1 = x.1 := congrArg Prod.fst h
  have h₂ : -x.2 = x.2 := congrArg Prod.snd h
  apply Prod.ext
  · change x.1 = (x.1.re : Quaternion ℚ)
    exact Quaternion.star_eq_self.mp h₁
  · change x.2 = 0
    apply Quaternion.ext
    · change x.2.re = 0
      exact CharZero.neg_eq_self_iff.mp (congrArg (fun q : Quaternion ℚ => q.re) h₂)
    · change x.2.imI = 0
      exact CharZero.neg_eq_self_iff.mp (congrArg (fun q : Quaternion ℚ => q.imI) h₂)
    · change x.2.imJ = 0
      exact CharZero.neg_eq_self_iff.mp (congrArg (fun q : Quaternion ℚ => q.imJ) h₂)
    · change x.2.imK = 0
      exact CharZero.neg_eq_self_iff.mp (congrArg (fun q : Quaternion ℚ => q.imK) h₂)

/-- Every coordinate matrix has the intended Hermitian symmetry. -/
theorem toMatrix_hermitian (x : Coordinates) (i j : Fin 3) :
    octStar (toMatrix x i j) = toMatrix x j i := by
  fin_cases i <;> fin_cases j <;> simp [toMatrix, octScalar, octStar]

/-- Matrix coordinates determine all six stored scalar/octonion components. -/
theorem toMatrix_injective : Function.Injective toMatrix := by
  intro x y h
  apply Coordinates.ext
  · simpa [toMatrix, octScalar] using congrArg (fun M => (M 0 0).1.re) h
  · simpa [toMatrix, octScalar] using congrArg (fun M => (M 1 1).1.re) h
  · simpa [toMatrix, octScalar] using congrArg (fun M => (M 2 2).1.re) h
  · simpa [toMatrix] using congrArg (fun M => M 0 1) h
  · simpa [toMatrix] using congrArg (fun M => M 0 2) h
  · simpa [toMatrix] using congrArg (fun M => M 1 2) h

/-- Hermitian inputs reverse order under entrywise conjugation and transposition. -/
theorem matrixMul_star_of_hermitian
    (X Y : Fin 3 → Fin 3 → Oct)
    (hX : ∀ i j, octStar (X i j) = X j i)
    (hY : ∀ i j, octStar (Y i j) = Y j i) (i j : Fin 3) :
    octStar (matrixMul X Y i j) = matrixMul Y X j i := by
  simp only [matrixMul, octStar_add, octStar_mul, hX, hY]

/-- Symmetrization restores Hermitian symmetry even though the binary product is nonassociative. -/
theorem symEntry_hermitian (x y : Coordinates) (i j : Fin 3) :
    octStar (symEntry x y i j) = symEntry x y j i := by
  unfold symEntry
  rw [octStar_smul, octStar_add,
    matrixMul_star_of_hermitian _ _ (toMatrix_hermitian x) (toMatrix_hermitian y),
    matrixMul_star_of_hermitian _ _ (toMatrix_hermitian y) (toMatrix_hermitian x)]
  rw [add_comm]

/-- The symmetrized diagonal entries are exactly their scalar real coordinates. -/
theorem symEntry_diagonal_scalar (x y : Coordinates) (i : Fin 3) :
    symEntry x y i i = octScalar (symEntry x y i i).1.re :=
  octStar_self_scalar (symEntry_hermitian x y i i)

/-- The stored coordinate product agrees with every entry of `(XY + YX)/2`. -/
theorem toMatrix_jordan (x y : Coordinates) (i j : Fin 3) :
    toMatrix (jordan x y) i j = symEntry x y i j := by
  fin_cases i <;> fin_cases j
  · change octScalar (symEntry x y 0 0).1.re = symEntry x y 0 0
    exact (symEntry_diagonal_scalar x y 0).symm
  · rfl
  · rfl
  · change octStar (symEntry x y 0 1) = symEntry x y 1 0
    exact symEntry_hermitian x y 0 1
  · change octScalar (symEntry x y 1 1).1.re = symEntry x y 1 1
    exact (symEntry_diagonal_scalar x y 1).symm
  · rfl
  · change octStar (symEntry x y 0 2) = symEntry x y 2 0
    exact symEntry_hermitian x y 0 2
  · change octStar (symEntry x y 1 2) = symEntry x y 2 1
    exact symEntry_hermitian x y 1 2
  · change octScalar (symEntry x y 2 2).1.re = symEntry x y 2 2
    exact (symEntry_diagonal_scalar x y 2).symm

#print axioms octStar_involutive
#print axioms octStar_add
#print axioms octStar_smul
#print axioms octStar_mul
#print axioms octStar_self_scalar
#print axioms toMatrix_hermitian
#print axioms toMatrix_injective
#print axioms matrixMul_star_of_hermitian
#print axioms symEntry_hermitian
#print axioms symEntry_diagonal_scalar
#print axioms toMatrix_jordan

end MathResearch.Albert
