import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Fin.VecNotation

noncomputable def gsUnivariate {K : Type*} [CommRing K]
    (p : Polynomial K) (i : Fin 3) : MvPolynomial (Fin 3) K :=
  p.eval₂ MvPolynomial.C (MvPolynomial.X i)

noncomputable def gsSubtract {K : Type*} [CommRing K]
    (b w : Polynomial K) : Fin 3 → MvPolynomial (Fin 3) K :=
  ![MvPolynomial.X 1,
    (MvPolynomial.X 0 : MvPolynomial (Fin 3) K) - gsUnivariate b 1,
    (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) - gsUnivariate w 1]

noncomputable def gsRestore {K : Type*} [CommRing K]
    (b w : Polynomial K) : Fin 3 → MvPolynomial (Fin 3) K :=
  ![MvPolynomial.X 1 + gsUnivariate b 0,
    MvPolynomial.X 0,
    MvPolynomial.X 2 + gsUnivariate w 0]

noncomputable def gsCompose {K : Type*} [CommRing K]
    (F G : Fin 3 → MvPolynomial (Fin 3) K) :
    Fin 3 → MvPolynomial (Fin 3) K :=
  fun i => MvPolynomial.eval₂Hom MvPolynomial.C G (F i)

noncomputable def gsGraph {K : Type*} [CommRing K]
    (b w : Polynomial K) : Fin 3 → Polynomial K :=
  ![b, Polynomial.X, w]

noncomputable def gsAlongGraph {K : Type*} [CommRing K]
    (F : Fin 3 → MvPolynomial (Fin 3) K) (b w : Polynomial K) :
    Fin 3 → Polynomial K :=
  fun i => MvPolynomial.eval₂Hom Polynomial.C (gsGraph b w) (F i)

theorem gs_eval_univariate : ∀ {K A : Type*} [CommRing K] [CommRing A] (f : K →+* A)
  (v : Fin 3 → A) (p : Polynomial K) (i : Fin 3),
  MvPolynomial.eval₂Hom f v (gsUnivariate p i) = p.eval₂ f (v i) := by
  intro K A _ _ f v p i
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [gsUnivariate, Polynomial.eval₂_add, map_add] using congrArg₂ (fun x y : A => x + y) hp hq
  | monomial n a =>
      simp [gsUnivariate, Polynomial.eval₂_monomial]

theorem gs_eval_univariate_raw : ∀ {K A : Type*} [CommRing K] [CommRing A] (f : K →+* A)
  (v : Fin 3 → A) (p : Polynomial K) (i : Fin 3),
  MvPolynomial.eval₂ f v (gsUnivariate p i) = p.eval₂ f (v i) := by
  intro K A _ _ f v p i
  exact gs_eval_univariate f v p i

theorem graph_subtraction_polynomial_identities : ∀ {K : Type*} [CommRing K] (b w : Polynomial K),
  gsCompose (gsRestore b w) (gsSubtract b w) =
      (fun i : Fin 3 => (MvPolynomial.X i : MvPolynomial (Fin 3) K)) ∧
  gsCompose (gsSubtract b w) (gsRestore b w) =
      (fun i : Fin 3 => (MvPolynomial.X i : MvPolynomial (Fin 3) K)) ∧
  gsAlongGraph (gsSubtract b w) b w = ![Polynomial.X, 0, 0] := by
  intro K _ b w
  refine ⟨?_, ?_, ?_⟩
  · funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.elim0 l) k) j) i
    all_goals
      simp [gsCompose, gsRestore, gsSubtract, gs_eval_univariate_raw] <;>
        simp [gsUnivariate]
  · funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.elim0 l) k) j) i
    all_goals
      simp [gsCompose, gsRestore, gsSubtract, gs_eval_univariate_raw] <;>
        simp [gsUnivariate]
  · funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.elim0 l) k) j) i
    all_goals
      simp [gsAlongGraph, gsSubtract, gsGraph, gs_eval_univariate_raw] <;>
        simp [gsUnivariate]

