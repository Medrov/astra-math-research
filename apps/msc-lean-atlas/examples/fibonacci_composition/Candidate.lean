import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Ring.Identities
import Mathlib.Algebra.Notation.Prod
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Group.Defs

def CompositionBridge.mu (x y : ℚ × ℚ) : ℚ × ℚ :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

def CompositionBridge.N (x : ℚ × ℚ) : ℚ :=
  x.1 ^ 2 + x.2 ^ 2

def CompositionBridge.compare (a b c : ℚ) : (ℚ × ℚ) × (ℚ × ℚ) :=
  ((b, a), (b, c))

def CompositionBridge.image (a b c : ℚ) : ℚ × ℚ :=
  CompositionBridge.mu (CompositionBridge.compare a b c).1
    (CompositionBridge.compare a b c).2

theorem CompositionBridge.structural_laws : (
(∀ (x x' y : ℚ × ℚ),
    CompositionBridge.mu (x + x') y = CompositionBridge.mu x y + CompositionBridge.mu x' y) ∧
  (∀ (r : ℚ) (x y : ℚ × ℚ),
    CompositionBridge.mu (r • x) y = r • CompositionBridge.mu x y) ∧
  (∀ (x y y' : ℚ × ℚ),
    CompositionBridge.mu x (y + y') = CompositionBridge.mu x y + CompositionBridge.mu x y') ∧
  (∀ (r : ℚ) (x y : ℚ × ℚ),
    CompositionBridge.mu x (r • y) = r • CompositionBridge.mu x y) ∧
  (∃ B : (ℚ × ℚ) → (ℚ × ℚ) → ℚ,
    (∀ x x' y, B (x + x') y = B x y + B x' y) ∧
    (∀ (r : ℚ) x y, B (r • x) y = r * B x y) ∧
    (∀ x y y', B x (y + y') = B x y + B x y') ∧
    (∀ (r : ℚ) x y, B x (r • y) = r * B x y) ∧
    (∀ x, CompositionBridge.N x = B x x)) ∧
  (∀ (x y : ℚ × ℚ),
    CompositionBridge.N (CompositionBridge.mu x y) =
      CompositionBridge.N x * CompositionBridge.N y)
) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x x' y
    apply Prod.ext <;>
      simp [CompositionBridge.mu, add_mul, mul_add, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm]
  · intro r x y
    apply Prod.ext <;>
      simp [CompositionBridge.mu, smul_eq_mul, add_mul, mul_add,
        sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm,
        add_assoc, add_left_comm, add_comm]
  · intro x y y'
    apply Prod.ext <;>
      simp [CompositionBridge.mu, add_mul, mul_add, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm]
  · intro r x y
    apply Prod.ext <;>
      simp [CompositionBridge.mu, smul_eq_mul, add_mul, mul_add,
        sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm,
        add_assoc, add_left_comm, add_comm]
  · refine ⟨fun x y => x.1 * y.1 + x.2 * y.2, ?_, ?_, ?_, ?_, ?_⟩
    · intro x x' y
      simp [add_mul, add_assoc, add_left_comm, add_comm]
    · intro r x y
      simp [smul_eq_mul, mul_add, mul_assoc]
    · intro x y y'
      simp [mul_add, add_assoc, add_left_comm, add_comm]
    · intro r x y
      simp [smul_eq_mul, mul_add, mul_assoc, mul_left_comm, mul_comm]
    · intro x
      simp [CompositionBridge.N, pow_two]
  · intro x y
    simpa only [CompositionBridge.N, CompositionBridge.mu] using
      (sq_add_sq_mul_sq_add_sq
        (x₁ := x.1) (x₂ := x.2) (y₁ := y.1) (y₂ := y.2)).symm

theorem CompositionBridge.normalization : (
∀ (a b c : ℚ),
  ((b ^ 4 - 2 * b ^ 2 * a * c = 1 - a ^ 2 * c ^ 2) ↔
    (b ^ 2 - a * c) ^ 2 = 1) ∧
  (c = a + b →
    b ^ 2 = (c - a) ^ 2 ∧
    b ^ 2 * (b ^ 2 - a ^ 2 - c ^ 2) = -2 * b ^ 2 * a * c ∧
    (b ^ 2 + a ^ 2) * (b ^ 2 + c ^ 2) - b ^ 2 * (a + c) ^ 2 =
      2 * b ^ 4 - b ^ 2 * a ^ 2 - b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2 ∧
    ((b ^ 2 + a ^ 2) * (b ^ 2 + c ^ 2) = 1 + b ^ 2 * (a + c) ^ 2 ↔
      2 * b ^ 4 - b ^ 2 * a ^ 2 + a ^ 2 * c ^ 2 = 1 + b ^ 2 * c ^ 2))
) := by
  intro a b c
  have hs : (b ^ 2 - a * c) ^ 2 =
      (b ^ 4 - 2 * b ^ 2 * a * c) + a ^ 2 * c ^ 2 := by
    ring
  constructor
  · rw [hs, eq_sub_iff_add_eq]
  · intro hc
    have hb : b ^ 2 = (c - a) ^ 2 := by
      simp [hc]
    have hm : b ^ 2 * (b ^ 2 - a ^ 2 - c ^ 2) =
        -2 * b ^ 2 * a * c := by
      rw [hc]
      ring
    have hp : (b ^ 2 + a ^ 2) * (b ^ 2 + c ^ 2) -
        b ^ 2 * (a + c) ^ 2 =
        2 * b ^ 4 - b ^ 2 * a ^ 2 - b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2 := by
      rw [hc]
      ring
    refine ⟨hb, hm, hp, ?_⟩
    have hz : 2 * b ^ 4 - b ^ 2 * a ^ 2 - b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2 =
        (2 * b ^ 4 - b ^ 2 * a ^ 2 + a ^ 2 * c ^ 2) - b ^ 2 * c ^ 2 := by
      ring
    calc
      ((b ^ 2 + a ^ 2) * (b ^ 2 + c ^ 2) = 1 + b ^ 2 * (a + c) ^ 2) ↔
          (b ^ 2 + a ^ 2) * (b ^ 2 + c ^ 2) - b ^ 2 * (a + c) ^ 2 = 1 :=
        sub_eq_iff_eq_add.symm
      _ ↔ 2 * b ^ 4 - b ^ 2 * a ^ 2 - b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2 = 1 := by
        rw [hp]
      _ ↔ 2 * b ^ 4 - b ^ 2 * a ^ 2 + a ^ 2 * c ^ 2 = 1 + b ^ 2 * c ^ 2 := by
        rw [hz, sub_eq_iff_eq_add]

theorem CompositionBridge.comparison_substitution : (
∀ (a b c : ℚ),
  CompositionBridge.compare a b c = ((b, a), (b, c)) ∧
  CompositionBridge.image a b c = (b ^ 2 - a * c, b * (a + c)) ∧
  CompositionBridge.N (CompositionBridge.image a b c) =
    (b ^ 2 - a * c) ^ 2 + b ^ 2 * (a + c) ^ 2 ∧
  CompositionBridge.N (CompositionBridge.image a b c) =
    CompositionBridge.N (b, a) * CompositionBridge.N (b, c) ∧
  (b ^ 2 + a ^ 2) * (b ^ 2 + c ^ 2) =
    (b ^ 2 - a * c) ^ 2 + b ^ 2 * (a + c) ^ 2
) := by
  intro a b c
  have hi : CompositionBridge.image a b c =
      (b ^ 2 - a * c, b * (a + c)) := by
    apply Prod.ext <;>
      simp [CompositionBridge.image, CompositionBridge.compare,
        CompositionBridge.mu, pow_two, mul_add, mul_comm, add_comm]
  have hn : CompositionBridge.N (CompositionBridge.image a b c) =
      (b ^ 2 - a * c) ^ 2 + b ^ 2 * (a + c) ^ 2 := by
    rw [hi]
    simp only [CompositionBridge.N, mul_pow]
  have hm : CompositionBridge.N (CompositionBridge.image a b c) =
      CompositionBridge.N (b, a) * CompositionBridge.N (b, c) := by
    simpa only [CompositionBridge.image, CompositionBridge.compare] using
      (CompositionBridge.structural_laws.2.2.2.2.2 (b, a) (b, c))
  refine ⟨rfl, hi, hn, hm, ?_⟩
  calc
    (b ^ 2 + a ^ 2) * (b ^ 2 + c ^ 2) =
        CompositionBridge.N (CompositionBridge.image a b c) := hm.symm
    _ = (b ^ 2 - a * c) ^ 2 + b ^ 2 * (a + c) ^ 2 := hn

theorem CompositionBridge.conditional_transfer : (
∀ (a b c : ℚ), c = a + b → (b ^ 2 - a * c) ^ 2 = 1 →
  CompositionBridge.image a b c = (b ^ 2 - a * c, b * (a + c)) ∧
  CompositionBridge.N (CompositionBridge.image a b c) =
    CompositionBridge.N (b, a) * CompositionBridge.N (b, c) ∧
  CompositionBridge.N (CompositionBridge.image a b c) =
    1 + b ^ 2 * (a + c) ^ 2 ∧
  (b ^ 2 + a ^ 2) * (b ^ 2 + c ^ 2) = 1 + b ^ 2 * (a + c) ^ 2 ∧
  2 * b ^ 4 - b ^ 2 * a ^ 2 + a ^ 2 * c ^ 2 = 1 + b ^ 2 * c ^ 2
) := by
  intro a b c hc hs
  rcases CompositionBridge.comparison_substitution a b c with
    ⟨hcompare, hi, hn, hm, hp⟩
  have hp1 : (b ^ 2 + a ^ 2) * (b ^ 2 + c ^ 2) =
      1 + b ^ 2 * (a + c) ^ 2 := by
    rw [hp, hs]
  refine ⟨hi, hm, ?_, hp1, ?_⟩
  · rw [hn, hs]
  · exact (((CompositionBridge.normalization a b c).2 hc).2.2.2).mp hp1

