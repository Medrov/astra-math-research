import StructureInput
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

-- atlas-structure-source-sha256: f6caebe6a85beaca8e5d5cfd0bb3fcd8f1ee18f0b134604f2ee212cbbf3c1a75

/-!
Prepared control, not an agent discovery. StructureInput is a fresh compiled
copy of research_fixtures/Arxiv261038474.lean, with its namespace unchanged.
The bridge concerns the underlying maps on points. The imported polynomial
identities remain separate, stronger algebraic statements.
-/

namespace CommonStructure

/-- Subtract a base-dependent group element in each fibre. -/
def fiberShear {A B : Type*} [AddGroup B] (f : A → B) : A × B ≃ A × B :=
  Equiv.prodShear (Equiv.refl A) (fun a => Equiv.subRight (f a))

theorem fiberShear_apply {A B : Type*} [AddGroup B] (f : A → B) (a : A) (b : B) :
    fiberShear f (a, b) = (a, b - f a) := rfl

theorem fiberShear_inverse {A B : Type*} [AddGroup B] (f : A → B) (p : A × B) :
    (fiberShear f).symm (fiberShear f p) = p ∧
      fiberShear f ((fiberShear f).symm p) = p :=
  ⟨(fiberShear f).symm_apply_apply p, (fiberShear f).apply_symm_apply p⟩

theorem fiberShear_graph {A B : Type*} [AddGroup B] (f : A → B) (a : A) :
    fiberShear f (a, f a) = (a, 0) := by
  simp [fiberShear_apply]

noncomputable section

variable {K : Type*} [CommRing K]

/-- Move the graph parameter y into the base coordinate. -/
def reorder (p : K × (K × K)) : K × (K × K) :=
  (p.2.1, (p.1, p.2.2))

def pointCoordinates (p : K × (K × K)) : Fin 3 → K :=
  ![p.1, p.2.1, p.2.2]

/-- Evaluate the three polynomial coordinates, retaining their order. -/
def evaluateTriple (F : Fin 3 → MvPolynomial (Fin 3) K) (p : K × (K × K)) :
    K × (K × K) :=
  (MvPolynomial.eval₂ (RingHom.id K) (pointCoordinates p) (F 0),
    (MvPolynomial.eval₂ (RingHom.id K) (pointCoordinates p) (F 1),
     MvPolynomial.eval₂ (RingHom.id K) (pointCoordinates p) (F 2)))

def polynomialProfile (b w : Polynomial K) (t : K) : K × K :=
  (b.eval t, w.eval t)

/-- The article's coordinate permutation and subtraction is a fibrewise equivalence. -/
theorem graphSubtract_eq_prodShear (b w : Polynomial K) (p : K × (K × K)) :
    evaluateTriple (Arxiv261038474.graphSubtract b w) p =
      fiberShear (polynomialProfile b w) (reorder p) := by
  have hb : MvPolynomial.eval (pointCoordinates p) (Arxiv261038474.univariate b 1) =
      b.eval p.2.1 := by
    simpa [pointCoordinates, Polynomial.eval] using
      (Arxiv261038474.eval_univariate (RingHom.id K) (pointCoordinates p) b 1)
  have hw : MvPolynomial.eval (pointCoordinates p) (Arxiv261038474.univariate w 1) =
      w.eval p.2.1 := by
    simpa [pointCoordinates, Polynomial.eval] using
      (Arxiv261038474.eval_univariate (RingHom.id K) (pointCoordinates p) w 1)
  simp only [pointCoordinates] at hb hw
  simp [evaluateTriple, Arxiv261038474.graphSubtract, hb, hw,
    pointCoordinates, fiberShear_apply, polynomialProfile, reorder]

/-- For a graph point, the bridge agrees with the zero section of the product. -/
theorem graphSubtract_graph_to_axis (b w : Polynomial K) (t : K) :
    evaluateTriple (Arxiv261038474.graphSubtract b w) (b.eval t, (t, w.eval t)) =
      (t, (0, 0)) := by
  rw [graphSubtract_eq_prodShear]
  simpa [reorder, polynomialProfile] using
    (fiberShear_graph (polynomialProfile b w) t)

/-- Bijectivity of a nonlinear shear does not make it an additive or linear map. -/
theorem squareShear_not_additive :
    ¬ (∀ u v : ℚ × ℚ,
      fiberShear (fun t : ℚ => t ^ 2) (u + v) =
        fiberShear (fun t : ℚ => t ^ 2) u + fiberShear (fun t : ℚ => t ^ 2) v) := by
  intro h
  have bad := congrArg Prod.snd (h (1, 0) (1, 0))
  norm_num [fiberShear, Equiv.prodShear, Equiv.subRight] at bad

end

end CommonStructure
