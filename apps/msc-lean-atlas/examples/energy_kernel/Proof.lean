import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

universe u v

def edgeDifference {V : Type u} {E : Type v}
    (s t : E → V) (f : V → ℝ) : E → ℝ :=
  fun e => f (s e) - f (t e)

def edgeEnergy {V : Type u} {E : Type v} [Fintype E]
    (s t : E → V) (w : E → ℝ) (f : V → ℝ) : ℝ :=
  ∑ e : E, w e * (edgeDifference s t f e) ^ 2

theorem weighted_sum_sq_eq_zero_iff : ∀ {E : Type v} [Fintype E] (w x : E → ℝ), (∀ e : E, 0 < w e) → ((∑ e : E, w e * (x e) ^ 2) = 0 ↔ ∀ e : E, x e = 0) := by
  classical
  intro E _ w x hw
  constructor
  · intro hsum e
    have hnonneg : ∀ i : E, 0 ≤ w i * (x i) ^ 2 :=
      fun i => mul_nonneg (le_of_lt (hw i)) (sq_nonneg (x i))
    have hle : w e * (x e) ^ 2 ≤ ∑ i : E, w i * (x i) ^ 2 :=
      Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ e)
    have hterm : w e * (x e) ^ 2 = 0 :=
      le_antisymm (hsum ▸ hle) (hnonneg e)
    have hsq : (x e) ^ 2 = 0 :=
      (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hw e))
    have hmul : x e * x e = 0 := by
      simpa only [pow_two] using hsq
    exact (mul_eq_zero.mp hmul).elim id id
  · intro hx
    simp [hx]

theorem edgeEnergy_eq_zero_iff : ∀ {V : Type u} {E : Type v} [Fintype E] (s t : E → V) (w : E → ℝ) (f : V → ℝ), (∀ e : E, 0 < w e) → (edgeEnergy s t w f = 0 ↔ ∀ e : E, f (s e) = f (t e)) := by
  intro V E _ s t w f hw
  simpa only [edgeEnergy, edgeDifference, sub_eq_zero] using
    (weighted_sum_sq_eq_zero_iff w (edgeDifference s t f) hw)

