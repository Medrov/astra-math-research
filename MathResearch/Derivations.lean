import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Tactic.Abel

/-!
# Derivations of an arbitrary bilinear multiplication

The multiplication below need not be associative, commutative, or Jordan.
This proves a common construction applicable to such products. It does not
identify the resulting Lie algebra with any named exceptional Lie algebra.
-/

namespace MathResearch.BilinearDerivations

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A linear endomorphism satisfying the Leibniz identity for a bilinear product. -/
def IsDerivation (μ : V →ₗ[R] V →ₗ[R] V) (D : Module.End R V) : Prop :=
  ∀ x y, D (μ x y) = μ (D x) y + μ x (D y)

theorem zero_isDerivation (μ : V →ₗ[R] V →ₗ[R] V) : IsDerivation μ 0 := by
  intro x y
  simp

theorem add_isDerivation (μ : V →ₗ[R] V →ₗ[R] V)
    {D E : Module.End R V} (hD : IsDerivation μ D) (hE : IsDerivation μ E) :
    IsDerivation μ (D + E) := by
  intro x y
  simp only [LinearMap.add_apply]
  rw [hD x y, hE x y]
  simp only [map_add, LinearMap.add_apply]
  abel

theorem smul_isDerivation (μ : V →ₗ[R] V →ₗ[R] V)
    {D : Module.End R V} (hD : IsDerivation μ D) (r : R) :
    IsDerivation μ (r • D) := by
  intro x y
  simp only [LinearMap.smul_apply]
  rw [hD x y]
  simp only [smul_add, map_smul, LinearMap.smul_apply]

/-- Derivations remain derivations under the commutator of endomorphisms. -/
theorem commutator_isDerivation (μ : V →ₗ[R] V →ₗ[R] V)
    {D E : Module.End R V} (hD : IsDerivation μ D) (hE : IsDerivation μ E) :
    IsDerivation μ (D * E - E * D) := by
  intro x y
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  rw [hE x y, hD x y]
  simp only [map_add]
  rw [hD (E x) y, hD x (E y), hE (D x) y, hE x (D y)]
  simp only [map_sub, LinearMap.sub_apply]
  abel

/-- The Leibniz endomorphisms form an actual Lie subalgebra of `End R V`. -/
def derivationLieSubalgebra (μ : V →ₗ[R] V →ₗ[R] V) :
    LieSubalgebra R (Module.End R V) where
  carrier := {D | IsDerivation μ D}
  zero_mem' := zero_isDerivation μ
  add_mem' := fun hD hE => add_isDerivation μ hD hE
  smul_mem' := fun r _ hD => smul_isDerivation μ hD r
  lie_mem' := fun hD hE => by
    rw [LieRing.of_associative_ring_bracket]
    exact commutator_isDerivation μ hD hE

theorem mem_derivationLieSubalgebra (μ : V →ₗ[R] V →ₗ[R] V)
    (D : Module.End R V) :
    D ∈ derivationLieSubalgebra μ ↔ IsDerivation μ D := Iff.rfl

/-- Jacobi holds for the operators, independently of the chosen product. -/
theorem endomorphism_commutator_jacobi (D E F : Module.End R V) :
    ⁅D, ⁅E, F⁆⁆ + ⁅E, ⁅F, D⁆⁆ + ⁅F, ⁅D, E⁆⁆ = 0 := lie_jacobi D E F

/-- Jacobi also holds inside the constructed Lie algebra of derivations. -/
theorem derivation_jacobi (μ : V →ₗ[R] V →ₗ[R] V)
    (D E F : derivationLieSubalgebra μ) :
    ⁅D, ⁅E, F⁆⁆ + ⁅E, ⁅F, D⁆⁆ + ⁅F, ⁅D, E⁆⁆ = 0 := lie_jacobi D E F

#print axioms zero_isDerivation
#print axioms add_isDerivation
#print axioms smul_isDerivation
#print axioms commutator_isDerivation
#print axioms mem_derivationLieSubalgebra
#print axioms endomorphism_commutator_jacobi
#print axioms derivation_jacobi

end MathResearch.BilinearDerivations
