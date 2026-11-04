import Candidate
universe u v w
set_option autoImplicit false
example : (
∀ (a b c : ℚ), c = a + b → (b ^ 2 - a * c) ^ 2 = 1 →
  CompositionBridge.image a b c = (b ^ 2 - a * c, b * (a + c)) ∧
  CompositionBridge.N (CompositionBridge.image a b c) =
    CompositionBridge.N (b, a) * CompositionBridge.N (b, c) ∧
  CompositionBridge.N (CompositionBridge.image a b c) =
    1 + b ^ 2 * (a + c) ^ 2 ∧
  (b ^ 2 + a ^ 2) * (b ^ 2 + c ^ 2) = 1 + b ^ 2 * (a + c) ^ 2 ∧
  2 * b ^ 4 - b ^ 2 * a ^ 2 + a ^ 2 * c ^ 2 = 1 + b ^ 2 * c ^ 2
) := @CompositionBridge.conditional_transfer
example : (
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
) := @CompositionBridge.structural_laws
example : (
∀ (a b c : ℚ),
  CompositionBridge.compare a b c = ((b, a), (b, c)) ∧
  CompositionBridge.image a b c = (b ^ 2 - a * c, b * (a + c)) ∧
  CompositionBridge.N (CompositionBridge.image a b c) =
    (b ^ 2 - a * c) ^ 2 + b ^ 2 * (a + c) ^ 2 ∧
  CompositionBridge.N (CompositionBridge.image a b c) =
    CompositionBridge.N (b, a) * CompositionBridge.N (b, c) ∧
  (b ^ 2 + a ^ 2) * (b ^ 2 + c ^ 2) =
    (b ^ 2 - a * c) ^ 2 + b ^ 2 * (a + c) ^ 2
) := @CompositionBridge.comparison_substitution
example : (
∀ (a b c : ℚ), c = a + b → (b ^ 2 - a * c) ^ 2 = 1 →
  CompositionBridge.image a b c = (b ^ 2 - a * c, b * (a + c)) ∧
  CompositionBridge.N (CompositionBridge.image a b c) =
    CompositionBridge.N (b, a) * CompositionBridge.N (b, c) ∧
  CompositionBridge.N (CompositionBridge.image a b c) =
    1 + b ^ 2 * (a + c) ^ 2 ∧
  (b ^ 2 + a ^ 2) * (b ^ 2 + c ^ 2) = 1 + b ^ 2 * (a + c) ^ 2 ∧
  2 * b ^ 4 - b ^ 2 * a ^ 2 + a ^ 2 * c ^ 2 = 1 + b ^ 2 * c ^ 2
) := @CompositionBridge.conditional_transfer
example : (
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
) := @CompositionBridge.normalization
