import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
The final graph-subtraction step in arXiv:2610.38474v1, Section 9.1,
Lemma 9.1, equations (9.1)-(9.2).  The preceding automorphism (x,H,W)
is not constructed here.  All three conclusions are polynomial identities
over an arbitrary commutative coefficient ring, including the fibre x = 0.
The verifier separately exports and audits the axioms of every theorem.
-/

namespace Arxiv261038474

noncomputable section

variable {R : Type*} [CommRing R]

/-- The univariate polynomial p, placed in coordinate i. -/
def univariate (p : Polynomial R) (i : Fin 3) : MvPolynomial (Fin 3) R :=
  p.eval₂ MvPolynomial.C (MvPolynomial.X i)

/-- (x,y,z) maps to (y,x-b(y),z-w(y)). -/
def graphSubtract (b w : Polynomial R) : Fin 3 → MvPolynomial (Fin 3) R :=
  ![MvPolynomial.X 1, (MvPolynomial.X 0 : MvPolynomial (Fin 3) R) - univariate b 1,
    (MvPolynomial.X 2 : MvPolynomial (Fin 3) R) - univariate w 1]

/-- (T,X,Z) maps to (X+b(T),T,Z+w(T)). -/
def graphRestore (b w : Polynomial R) : Fin 3 → MvPolynomial (Fin 3) R :=
  ![MvPolynomial.X 1 + univariate b 0, MvPolynomial.X 0,
    MvPolynomial.X 2 + univariate w 0]

/-- Coordinatewise polynomial composition, without localization or division. -/
def compose (F G : Fin 3 → MvPolynomial (Fin 3) R) :
    Fin 3 → MvPolynomial (Fin 3) R :=
  fun i => MvPolynomial.eval₂Hom MvPolynomial.C G (F i)

/-- The graph after the preceding coordinate change: (b(t),t,w(t)). -/
def graphCurve (b w : Polynomial R) : Fin 3 → Polynomial R :=
  ![b, Polynomial.X, w]

/-- Substitute the graph into a polynomial map. -/
def alongGraph (F : Fin 3 → MvPolynomial (Fin 3) R) (b w : Polynomial R) :
    Fin 3 → Polynomial R :=
  fun i => MvPolynomial.eval₂Hom Polynomial.C (graphCurve b w) (F i)

theorem eval_univariate {S : Type*} [CommRing S] (f : R →+* S)
    (v : Fin 3 → S) (p : Polynomial R) (i : Fin 3) :
    MvPolynomial.eval₂ f v (univariate p i) = p.eval₂ f (v i) := by
  have hc : (MvPolynomial.eval₂Hom f v).comp MvPolynomial.C = f := by
    ext r
    simp
  simpa [univariate, hc] using
    (Polynomial.hom_eval₂ p MvPolynomial.C (MvPolynomial.eval₂Hom f v) (MvPolynomial.X i))

theorem subtract_restore (b w : Polynomial R) :
    compose (graphSubtract b w) (graphRestore b w) = MvPolynomial.X := by
  funext i
  fin_cases i <;> simp [compose, graphSubtract, graphRestore, eval_univariate] <;>
    simp [univariate]

theorem restore_subtract (b w : Polynomial R) :
    compose (graphRestore b w) (graphSubtract b w) = MvPolynomial.X := by
  funext i
  fin_cases i <;> simp [compose, graphSubtract, graphRestore, eval_univariate] <;>
    simp [univariate]

theorem graph_to_axis (b w : Polynomial R) :
    alongGraph (graphSubtract b w) b w = ![Polynomial.X, 0, 0] := by
  funext i
  fin_cases i <;> simp [alongGraph, graphSubtract, graphCurve, eval_univariate]

end

end Arxiv261038474
