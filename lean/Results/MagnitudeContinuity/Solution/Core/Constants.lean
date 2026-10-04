import Results.MagnitudeContinuity.Solution.Core.Quadratic

/-! Scalar bookkeeping for the radius and the constant `2 n m³ / lam²`.

With the sharp half-factor, `ε = 1 - exp (-M_r/2) ≤ M_r/2 ≤ n m r`. -/

noncomputable section

namespace MagCore

theorem upper_constant (n m lam r ε : ℝ) (hlam : 0 < lam)
    (hε : ε ≤ n * m * r) :
    2 * m ^ 2 * ε / lam ^ 2 ≤ (2 * n * m ^ 3 / lam ^ 2) * r := by
  have hl2 : 0 < lam ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hl2]
  have : 0 ≤ m ^ 2 := by positivity
  nlinarith

theorem small_radius {n m lam r : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hr : r ≤ lam / (2 * n * m ^ 2)) : m * (n * m * r) ≤ lam / 2 := by
  have hd : 0 < 2 * n * m ^ 2 := by positivity
  have h := (le_div_iff₀ hd).mp hr
  nlinarith

end MagCore
