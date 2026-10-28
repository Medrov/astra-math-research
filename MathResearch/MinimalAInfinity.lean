import Mathlib.Algebra.Lie.Basic

/-!
# A necessary binary law of an uncurved minimal A-infinity algebra

This file does not define a full graded A-infinity algebra. The arity-three
Stasheff relation with m1 = 0 necessarily says that m2 is associative.
We isolate that necessary condition, so failing it rules out the proposed
binary product. Higher operations cannot change this particular condition.

Source: B. Keller, Introduction to A-infinity algebras and modules, section 3.1.
-/

namespace MathResearch

/-- Necessary arity-three condition for the binary operation of a minimal,
uncurved A-infinity structure. This is not a definition of that full structure. -/
def MinimalBinaryCondition {A : Type*} (m₂ : A → A → A) : Prop :=
  ∀ x y z, m₂ (m₂ x y) z = m₂ x (m₂ y z)

/-- The degree-zero sign convention of the third Stasheff relation.
The graded complex, degree constraints and all other arities are deliberately
not encoded here. Only its zero-differential specialization is used below,
where the Koszul signs of terms containing the differential are irrelevant. -/
def ArityThreeTemplate {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (d : A →ₗ[R] A) (m₂ : A →ₗ[R] A →ₗ[R] A)
    (m₃ : A →ₗ[R] A →ₗ[R] A →ₗ[R] A) : Prop :=
  ∀ x y z, d (m₃ x y z) + m₂ (m₂ x y) z - m₂ x (m₂ y z) +
    m₃ (d x) y z + m₃ x (d y) z + m₃ x y (d z) = 0

/-- Actual algebraic reduction: all ternary terms disappear when d = 0. -/
theorem third_stasheff_zero_differential {R A : Type*}
    [CommRing R] [AddCommGroup A] [Module R A]
    (d : A →ₗ[R] A) (m₂ : A →ₗ[R] A →ₗ[R] A)
    (m₃ : A →ₗ[R] A →ₗ[R] A →ₗ[R] A)
    (hd : d = 0) (h : ArityThreeTemplate d m₂ m₃) :
    MinimalBinaryCondition (fun x y => m₂ x y) := by
  intro x y z
  have hx := h x y z
  simp only [hd, LinearMap.zero_apply, map_zero, zero_add, add_zero] at hx
  exact sub_eq_zero.mp hx

/-- A single unequal pair of bracketings excludes the necessary condition. -/
theorem witness_excludes_minimal_binary {A : Type*} (m₂ : A → A → A)
    (x y z : A) (h : m₂ (m₂ x y) z ≠ m₂ x (m₂ y z)) :
    ¬ MinimalBinaryCondition m₂ := by
  intro hminimal
  exact h (hminimal x y z)

#print axioms third_stasheff_zero_differential
#print axioms witness_excludes_minimal_binary

end MathResearch
