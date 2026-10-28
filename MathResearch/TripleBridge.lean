import Mathlib.Algebra.Lie.Basic

/-!
# A triple product from an involutive Lie automorphism

For a Lie algebra and an involutive Lie automorphism tau, define
`T x y z = [[x, tau y], z]`. The generalized Jordan triple identity below
follows from Jacobi and preservation of the bracket by tau.
No identification with a particular E10, Monster, or Albert construction is
part of this theorem.
-/

namespace MathResearch.TripleBridge

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The triple multiplication associated to an involutive Lie automorphism. -/
def triple (τ : L ≃ₗ⁅R⁆ L) (x y z : L) : L := ⁅⁅x, τ y⁆, z⁆

/-- Involution turns the reversed triple into the negative adjoint term. -/
theorem involution_triple_reverse (τ : L ≃ₗ⁅R⁆ L)
    (hτ : Function.Involutive τ) (u v y : L) :
    τ (triple τ v u y) = -⁅⁅u, τ v⁆, τ y⁆ := by
  simp only [triple, LieEquiv.map_lie, hτ u]
  rw [← lie_skew (τ v) u, neg_lie]

/-- The generalized Jordan triple identity, with the reversed `v,u` term. -/
theorem generalized_jordan_triple_identity (τ : L ≃ₗ⁅R⁆ L)
    (hτ : Function.Involutive τ) (u v x y z : L) :
    triple τ u v (triple τ x y z) - triple τ x y (triple τ u v z) =
      triple τ (triple τ u v x) y z - triple τ x (triple τ v u y) z := by
  change
    ⁅⁅u, τ v⁆, ⁅⁅x, τ y⁆, z⁆⁆ - ⁅⁅x, τ y⁆, ⁅⁅u, τ v⁆, z⁆⁆ =
      ⁅⁅⁅⁅u, τ v⁆, x⁆, τ y⁆, z⁆ - ⁅⁅x, τ (triple τ v u y)⁆, z⁆
  rw [← lie_lie, involution_triple_reverse τ hτ u v y]
  simp only [lie_neg, neg_lie, sub_neg_eq_add]
  rw [leibniz_lie ⁅u, τ v⁆ x (τ y), add_lie]

#print axioms involution_triple_reverse
#print axioms generalized_jordan_triple_identity

end MathResearch.TripleBridge
