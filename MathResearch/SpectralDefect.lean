import MathResearch.AlbertSpectralGeometry
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Quantitative spectral mismatch at a concrete Albert idempotent

All quantities in this file use the existing 27 rational Albert coordinates.
The squared size is the Hermitian trace-form coordinate expression: diagonal
squares plus twice the squared octonionic off-diagonal coordinates. It is not
an assumed abstract norm, and no complete Jordan or Monster construction is
postulated here.

The candidate research question is quantitative: how much one-axis product
error is forced when an eigenvector with Monster-type eigenvalue 1/4 or 1/32
is mapped homogeneously into these Albert coordinates, with the source axis
mapped to P? The classical Peirce spectrum explains the obstruction; novelty
of the precise sharp bound is not established by this formalization.
-/

namespace MathResearch.SpectralDefect

open MathResearch.Albert
open scoped Quaternion

set_option maxHeartbeats 1000000

/-- Euclidean squared size of one rational quaternion. -/
def quaternionSizeSq (q : Quaternion ℚ) : ℚ :=
  q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2

/-- Euclidean squared size of one rational Cayley-Dickson octonion. -/
def octonionSizeSq (q : Oct) : ℚ := quaternionSizeSq q.1 + quaternionSizeSq q.2

/-- The trace-form squared size on all 27 stored coordinates. -/
def sizeSq (x : Coordinates) : ℚ :=
  x.d₀ ^ 2 + x.d₁ ^ 2 + x.d₂ ^ 2 +
    2 * (octonionSizeSq x.u₀₁ + octonionSizeSq x.u₀₂ + octonionSizeSq x.u₁₂)

def scale (r : ℚ) (x : Coordinates) : Coordinates :=
  ⟨r * x.d₀, r * x.d₁, r * x.d₂, r • x.u₀₁, r • x.u₀₂, r • x.u₁₂⟩

def subtract (x y : Coordinates) : Coordinates :=
  ⟨x.d₀ - y.d₀, x.d₁ - y.d₁, x.d₂ - y.d₂,
    x.u₀₁ - y.u₀₁, x.u₀₂ - y.u₀₂, x.u₁₂ - y.u₁₂⟩

/-- The actual error of the eigenvalue equation for Albert multiplication by P. -/
def residual (lam : ℚ) (x : Coordinates) : Coordinates := subtract (jordan P x) (scale lam x)

/-- The selected concrete Albert element really is an idempotent. -/
theorem P_idempotent : jordan P P = P := by
  have hP : P = MathResearch.AlbertSpectralGeometry.diagonal ![1, 0, 0] := rfl
  rw [hP, MathResearch.AlbertSpectralGeometry.jordan_diagonal]
  apply Coordinates.ext <;>
    simp [MathResearch.AlbertSpectralGeometry.diagonal, octScalar]

/-- Coordinate form of the residual in the 0, 1/2, and 1 Peirce blocks at P. -/
def peirceResidual (lam : ℚ) (x : Coordinates) : Coordinates :=
  ⟨(1 - lam) * x.d₀, -lam * x.d₁, -lam * x.d₂,
    (1 / 2 - lam : ℚ) • x.u₀₁, (1 / 2 - lam : ℚ) • x.u₀₂, -lam • x.u₁₂⟩

theorem octonionSizeSq_nonneg (q : Oct) : 0 ≤ octonionSizeSq q := by
  unfold octonionSizeSq quaternionSizeSq
  positivity

theorem octonionSizeSq_smul (r : ℚ) (q : Oct) :
    octonionSizeSq (r • q) = r ^ 2 * octonionSizeSq q := by
  simp [octonionSizeSq, quaternionSizeSq]
  ring

@[simp]
theorem octonionSizeSq_neg (q : Oct) : octonionSizeSq (-q) = octonionSizeSq q := by
  simp [octonionSizeSq, quaternionSizeSq]

@[simp]
theorem octonionSizeSq_zero : octonionSizeSq (0 : Oct) = 0 := by
  simp [octonionSizeSq, quaternionSizeSq]

theorem sizeSq_nonneg (x : Coordinates) : 0 ≤ sizeSq x := by
  unfold sizeSq octonionSizeSq quaternionSizeSq
  positivity

theorem peirceResidual_sizeSq (lam : ℚ) (x : Coordinates) :
    sizeSq (peirceResidual lam x) - lam ^ 2 * sizeSq x =
      (1 - 2 * lam) * x.d₀ ^ 2 +
        2 * (1 / 4 - lam) * (octonionSizeSq x.u₀₁ + octonionSizeSq x.u₀₂) := by
  simp [sizeSq, peirceResidual, octonionSizeSq_smul]
  ring

theorem peirceResidual_lower_bound (lam : ℚ) (x : Coordinates)
    (hlam : lam ≤ 1 / 4) :
    lam ^ 2 * sizeSq x ≤ sizeSq (peirceResidual lam x) := by
  have h := peirceResidual_sizeSq lam x
  have h0 : 0 ≤ (1 - 2 * lam) * x.d₀ ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have h1 : 0 ≤ 2 * (1 / 4 - lam) *
      (octonionSizeSq x.u₀₁ + octonionSizeSq x.u₀₂) := by
    apply mul_nonneg
    · apply mul_nonneg (by norm_num) (by linarith)
    · exact add_nonneg (octonionSizeSq_nonneg _) (octonionSizeSq_nonneg _)
  linarith

/-- The coordinate spectral residual is the actual Albert product error at P. -/
theorem residual_eq_peirceResidual (lam : ℚ) (x : Coordinates) :
    residual lam x = peirceResidual lam x := by
  have hP : P = MathResearch.AlbertSpectralGeometry.diagonal ![1, 0, 0] := rfl
  unfold residual
  rw [hP, MathResearch.AlbertSpectralGeometry.jordan_diagonal]
  apply Coordinates.ext <;>
    simp [subtract, scale, peirceResidual, sub_smul, sub_mul]

/-- Exact quantitative mismatch at the concrete Albert axis, not an abstract spectrum. -/
theorem residual_sizeSq (lam : ℚ) (x : Coordinates) :
    sizeSq (residual lam x) - lam ^ 2 * sizeSq x =
      (1 - 2 * lam) * x.d₀ ^ 2 +
        2 * (1 / 4 - lam) * (octonionSizeSq x.u₀₁ + octonionSizeSq x.u₀₂) := by
  rw [residual_eq_peirceResidual]
  exact peirceResidual_sizeSq lam x

theorem residual_lower_bound (lam : ℚ) (x : Coordinates) (hlam : lam ≤ 1 / 4) :
    lam ^ 2 * sizeSq x ≤ sizeSq (residual lam x) := by
  rw [residual_eq_peirceResidual]
  exact peirceResidual_lower_bound lam x hlam

theorem quarter_residual_sizeSq (x : Coordinates) :
    sizeSq (residual (1 / 4) x) = (1 / 16 : ℚ) * sizeSq x + (1 / 2 : ℚ) * x.d₀ ^ 2 := by
  have h := residual_sizeSq (1 / 4) x
  norm_num at h
  linarith

theorem thirtysecond_residual_sizeSq (x : Coordinates) :
    sizeSq (residual (1 / 32) x) = (1 / 1024 : ℚ) * sizeSq x +
      (15 / 16 : ℚ) * x.d₀ ^ 2 +
      (7 / 16 : ℚ) * (octonionSizeSq x.u₀₁ + octonionSizeSq x.u₀₂) := by
  have h := residual_sizeSq (1 / 32) x
  norm_num at h
  linarith

/-- The 1/4 bound is attained precisely when the Peirce-1 diagonal component vanishes. -/
theorem quarter_equality_iff (x : Coordinates) :
    sizeSq (residual (1 / 4) x) = (1 / 16 : ℚ) * sizeSq x ↔ x.d₀ = 0 := by
  rw [quarter_residual_sizeSq]
  constructor
  · intro h
    have hs : x.d₀ ^ 2 = 0 := by linarith
    exact sq_eq_zero_iff.mp hs
  · intro h
    simp [h]

/-- At 1/32, equality forces the entire Peirce-1/2 squared size to vanish as well. -/
theorem thirtysecond_equality_iff (x : Coordinates) :
    sizeSq (residual (1 / 32) x) = (1 / 1024 : ℚ) * sizeSq x ↔
      x.d₀ = 0 ∧ octonionSizeSq x.u₀₁ + octonionSizeSq x.u₀₂ = 0 := by
  rw [thirtysecond_residual_sizeSq]
  constructor
  · intro h
    have hs : x.d₀ ^ 2 = 0 := by
      nlinarith [octonionSizeSq_nonneg x.u₀₁, octonionSizeSq_nonneg x.u₀₂]
    have hd := sq_eq_zero_iff.mp hs
    exact ⟨hd, by nlinarith⟩
  · rintro ⟨h0, hhalf⟩
    simp [h0, hhalf]

def sharpWitness : Coordinates := ⟨0, 1, 0, octScalar 0, octScalar 0, octScalar 0⟩

theorem sharpWitness_sizeSq : sizeSq sharpWitness = 1 := by
  norm_num [sizeSq, sharpWitness, octScalar, octonionSizeSq, quaternionSizeSq]

/-- Both target-residual constants are optimal on an actual nonzero Albert Peirce-0 coordinate.
This does not assert realization of the sharp case by a map from the full Griess algebra. -/
theorem sharpWitness_residual_sizeSq (lam : ℚ) :
    sizeSq (residual lam sharpWitness) = lam ^ 2 := by
  have h := residual_sizeSq lam sharpWitness
  rw [sharpWitness_sizeSq] at h
  have h0 : sharpWitness.d₀ = 0 := rfl
  have hu01 : octonionSizeSq sharpWitness.u₀₁ = 0 := by
    norm_num [sharpWitness, octScalar, octonionSizeSq, quaternionSizeSq]
  have hu02 : octonionSizeSq sharpWitness.u₀₂ = 0 := by
    norm_num [sharpWitness, octScalar, octonionSizeSq, quaternionSizeSq]
  rw [h0, hu01, hu02] at h
  norm_num at h
  linarith

/-- One-axis multiplicativity error of a candidate map into the concrete target. -/
def productError {A : Type*} [Mul A] (f : A → Coordinates) (e x : A) : Coordinates :=
  subtract (jordan (f e) (f x)) (f (e * x))

/-- Only scalar compatibility on the supplied eigenvector is needed, not an assumed homomorphism. -/
theorem productError_eq_residual {A : Type*} [Mul A] [SMul ℚ A]
    (f : A → Coordinates) (e x : A) (lam : ℚ)
    (haxis : f e = P) (heigen : e * x = lam • x)
    (hscale : f (lam • x) = scale lam (f x)) :
    productError f e x = residual lam (f x) := by
  unfold productError residual
  rw [haxis, heigen, hscale]

/-- Every homogeneous candidate map has this unavoidable one-axis product defect. -/
theorem productError_lower_bound {A : Type*} [Mul A] [SMul ℚ A]
    (f : A → Coordinates) (e x : A) (lam : ℚ)
    (haxis : f e = P) (heigen : e * x = lam • x)
    (hscale : f (lam • x) = scale lam (f x)) (hlam : lam ≤ 1 / 4) :
    lam ^ 2 * sizeSq (f x) ≤ sizeSq (productError f e x) := by
  rw [productError_eq_residual f e x lam haxis heigen hscale]
  exact residual_lower_bound lam (f x) hlam

theorem quarter_productError_lower_bound {A : Type*} [Mul A] [SMul ℚ A]
    (f : A → Coordinates) (e x : A)
    (haxis : f e = P) (heigen : e * x = (1 / 4 : ℚ) • x)
    (hscale : f ((1 / 4 : ℚ) • x) = scale (1 / 4) (f x)) :
    (1 / 16 : ℚ) * sizeSq (f x) ≤ sizeSq (productError f e x) := by
  simpa using productError_lower_bound f e x (1 / 4) haxis heigen hscale (le_refl _)

theorem thirtysecond_productError_lower_bound {A : Type*} [Mul A] [SMul ℚ A]
    (f : A → Coordinates) (e x : A)
    (haxis : f e = P) (heigen : e * x = (1 / 32 : ℚ) • x)
    (hscale : f ((1 / 32 : ℚ) • x) = scale (1 / 32) (f x)) :
    (1 / 1024 : ℚ) * sizeSq (f x) ≤ sizeSq (productError f e x) := by
  simpa using productError_lower_bound f e x (1 / 32) haxis heigen hscale (by norm_num)

theorem sizeSq_subtract_self (x : Coordinates) : sizeSq (subtract x x) = 0 := by
  simp [sizeSq, subtract]

/-- An exact product map with the supplied axis/eigenvector data must collapse its image. -/
theorem product_preserving_forces_zero_size {A : Type*} [Mul A] [SMul ℚ A]
    (f : A → Coordinates) (e x : A) (lam : ℚ)
    (haxis : f e = P) (heigen : e * x = lam • x)
    (hscale : f (lam • x) = scale lam (f x)) (hlam : lam ≤ 1 / 4)
    (hne : lam ≠ 0) (hmul : jordan (f e) (f x) = f (e * x)) :
    sizeSq (f x) = 0 := by
  have h := productError_lower_bound f e x lam haxis heigen hscale hlam
  unfold productError at h
  rw [hmul, sizeSq_subtract_self] at h
  have hp : 0 < lam ^ 2 := sq_pos_of_ne_zero hne
  have hn := sizeSq_nonneg (f x)
  nlinarith

/-- In particular, an image of positive size cannot preserve even this single product. -/
theorem product_not_preserved_of_positive_size {A : Type*} [Mul A] [SMul ℚ A]
    (f : A → Coordinates) (e x : A) (lam : ℚ)
    (haxis : f e = P) (heigen : e * x = lam • x)
    (hscale : f (lam • x) = scale lam (f x)) (hlam : lam ≤ 1 / 4)
    (hne : lam ≠ 0) (hsize : 0 < sizeSq (f x)) :
    jordan (f e) (f x) ≠ f (e * x) := by
  intro hmul
  have h := product_preserving_forces_zero_size f e x lam haxis heigen hscale hlam hne hmul
  linarith

/-- Classical Peirce polynomial, recorded separately from the quantitative candidate. -/
def peircePolynomial (lam : ℚ) : ℚ := lam * (2 * lam - 1) * (lam - 1)

def operatorPeirceDefect {E : Type*} [AddCommGroup E] [Module ℚ E]
    (L : E →ₗ[ℚ] E) (x : E) : E :=
  (2 : ℚ) • L (L (L x)) - (3 : ℚ) • L (L x) + L x

theorem operatorPeirceDefect_eigenvector {E : Type*} [AddCommGroup E] [Module ℚ E]
    (L : E →ₗ[ℚ] E) (x : E) (lam : ℚ) (heigen : L x = lam • x) :
    operatorPeirceDefect L x = peircePolynomial lam • x := by
  simp only [operatorPeirceDefect, heigen, map_smul, smul_smul]
  rw [← sub_smul, ← add_smul]
  congr 1
  unfold peircePolynomial
  ring

theorem quarter_peircePolynomial : peircePolynomial (1 / 4) = (3 / 32 : ℚ) := by
  norm_num [peircePolynomial]

theorem thirtysecond_peircePolynomial : peircePolynomial (1 / 32) = (465 / 16384 : ℚ) := by
  norm_num [peircePolynomial]

#print axioms octonionSizeSq_nonneg
#print axioms P_idempotent
#print axioms octonionSizeSq_smul
#print axioms octonionSizeSq_neg
#print axioms octonionSizeSq_zero
#print axioms sizeSq_nonneg
#print axioms peirceResidual_sizeSq
#print axioms peirceResidual_lower_bound
#print axioms residual_eq_peirceResidual
#print axioms residual_sizeSq
#print axioms residual_lower_bound
#print axioms quarter_residual_sizeSq
#print axioms thirtysecond_residual_sizeSq
#print axioms quarter_equality_iff
#print axioms thirtysecond_equality_iff
#print axioms sharpWitness_sizeSq
#print axioms sharpWitness_residual_sizeSq
#print axioms productError_eq_residual
#print axioms productError_lower_bound
#print axioms quarter_productError_lower_bound
#print axioms thirtysecond_productError_lower_bound
#print axioms sizeSq_subtract_self
#print axioms product_preserving_forces_zero_size
#print axioms product_not_preserved_of_positive_size
#print axioms operatorPeirceDefect_eigenvector
#print axioms quarter_peircePolynomial
#print axioms thirtysecond_peircePolynomial

end MathResearch.SpectralDefect
