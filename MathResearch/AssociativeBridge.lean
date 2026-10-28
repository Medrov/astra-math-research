import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# The universal associative envelope of a Lie algebra

These are the bracket compatibility and associative multiplication statements
for the actual mathlib universal enveloping algebra. Associative multiplication
is the prerequisite for the strict A-infinity model concentrated in degree zero;
this file does not formalize the complete graded A-infinity identities.
No injectivity of the canonical map, PBW theorem, or named E10 model is asserted.
-/

namespace MathResearch.AssociativeBridge

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The canonical Lie map preserves the bracket as an associative commutator. -/
theorem enveloping_bracket (x y : L) :
    UniversalEnvelopingAlgebra.ι R ⁅x, y⁆ =
      UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y -
        UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x := by
  rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]

/-- The envelope's multiplication is associative, unlike an arbitrary Jordan product. -/
theorem enveloping_associative (x y z : UniversalEnvelopingAlgebra R L) :
    (x * y) * z = x * (y * z) := mul_assoc x y z

/-- The arity-three obstruction vanishes for multiplication in the envelope. -/
theorem enveloping_associator_zero (x y z : UniversalEnvelopingAlgebra R L) :
    (x * y) * z - x * (y * z) = 0 := by
  rw [mul_assoc, sub_self]

/-- Every Lie representation into an associative algebra extends along the canonical map. -/
theorem enveloping_lift_extends {A : Type*} [Ring A] [Algebra R A]
    (f : L →ₗ⁅R⁆ A) (x : L) :
    UniversalEnvelopingAlgebra.lift R f (UniversalEnvelopingAlgebra.ι R x) = f x :=
  UniversalEnvelopingAlgebra.lift_ι_apply R f x

#print axioms enveloping_bracket
#print axioms enveloping_associative
#print axioms enveloping_associator_zero
#print axioms enveloping_lift_extends

end MathResearch.AssociativeBridge
