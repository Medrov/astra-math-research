import Mathlib.Analysis.InnerProductSpace.Basic


open RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def UpperQuad (f : E → ℝ) (g : E → E) (L : ℝ) : Prop :=
  ∀ x y, f y ≤ f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2

def LowerQuad (f : E → ℝ) (g : E → E) (μ : ℝ) : Prop :=
  ∀ x y, f x + ⟪g x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y

theorem descent (f : E → ℝ) (g : E → E) {L : ℝ} (hL0 : 0 < L)
    (hL : UpperQuad f g L) (x : E) :
    f (x - (1 / L) • g x) ≤ f x - 1 / (2 * L) * ‖g x‖ ^ 2 := by

  have h := hL x (x - (1 / L) • g x)
  have hd : x - (1 / L) • g x - x = -((1 / L) • g x) := by abel
  have hinner : ⟪g x, -((1 / L) • g x)⟫ = -(1 / L * ‖g x‖ ^ 2) := by
    rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hnorm : ‖-((1 / L) • g x)‖ = 1 / L * ‖g x‖ := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hd, hinner, hnorm] at h
  calc f (x - (1 / L) • g x)
      ≤ f x + -(1 / L * ‖g x‖ ^ 2) + L / 2 * (1 / L * ‖g x‖) ^ 2 := h
    _ = f x - 1 / (2 * L) * ‖g x‖ ^ 2 := by field_simp; ring

theorem pl_ineq (f : E → ℝ) (g : E → E) {μ : ℝ} (hμ : 0 < μ)
    (hμf : LowerQuad f g μ) (x z : E) :
    2 * μ * (f x - f z) ≤ ‖g x‖ ^ 2 := by
  have h := hμf x z
  have hcs : -(‖g x‖ * ‖z - x‖) ≤ ⟪g x, z - x⟫ := by
    have := abs_real_inner_le_norm (g x) (z - x)
    linarith [neg_abs_le ⟪g x, z - x⟫]
  nlinarith [sq_nonneg (‖g x‖ - μ * ‖z - x‖)]

theorem one_step (f : E → ℝ) (g : E → E) {μ L : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hL : UpperQuad f g L) (hμf : LowerQuad f g μ) (x z : E) :
    f (x - (1 / L) • g x) - f z ≤ (1 - μ / L) * (f x - f z) := by
  have hL0 : 0 < L := lt_of_lt_of_le hμ hμL
  have h1 := descent f g hL0 hL x
  have h2 := pl_ineq f g hμ hμf x z
  have h3 : μ / L * (f x - f z) ≤ 1 / (2 * L) * ‖g x‖ ^ 2 := by
    calc μ / L * (f x - f z)
        = 1 / (2 * L) * (2 * μ * (f x - f z)) := by field_simp
      _ ≤ 1 / (2 * L) * ‖g x‖ ^ 2 := by gcongr
  linarith

theorem gd_rate (f : E → ℝ) (g : E → E) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (hL : UpperQuad f g L) (hμf : LowerQuad f g μ)
    (x : ℕ → E) (hx : ∀ k, x (k + 1) = x k - (1 / L) • g (x k))
    (xstar : E) :
    ∀ k : ℕ, f (x k) - f xstar ≤ (1 - μ / L) ^ k * (f (x 0) - f xstar) := by
  have hL0 : 0 < L := lt_of_lt_of_le hμ hμL
  have hq : 0 ≤ 1 - μ / L := by
    rw [sub_nonneg, div_le_one hL0]
    exact hμL
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc f (x (k + 1)) - f xstar
        = f (x k - (1 / L) • g (x k)) - f xstar := by rw [hx k]
      _ ≤ (1 - μ / L) * (f (x k) - f xstar) := one_step f g hμ hμL hL hμf (x k) xstar
      _ ≤ (1 - μ / L) * ((1 - μ / L) ^ k * (f (x 0) - f xstar)) :=
          mul_le_mul_of_nonneg_left ih hq
      _ = (1 - μ / L) ^ (k + 1) * (f (x 0) - f xstar) := by ring
