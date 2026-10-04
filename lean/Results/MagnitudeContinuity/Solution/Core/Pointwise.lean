import Results.MagnitudeContinuity.Solution.Core.Quadratic
import Mathlib.Algebra.Order.AbsoluteValue.Basic

/-!
# Pointwise geometry of threshold cuts

`d` is an arbitrary real-valued "distance" (no axioms are needed for these statements);
`f x t` plays the role of the representative `f_x(t)` and `h t` of the envelope.
Coincident coordinate values, overlapping strips and `h t = 0` are all allowed.
-/

set_option linter.unusedSectionVars false

noncomputable section
open scoped BigOperators

namespace MagCore

universe u v w

theorem threshold_stability {x a s ρ : ℝ} (hnear : |x - a| ≤ ρ) (hout : ρ < |s - a|) :
    (s < x ↔ s < a) := by
  have hb := abs_le.mp hnear
  constructor
  · intro hsx
    by_contra hsa
    have has : a ≤ s := not_lt.mp hsa
    rw [abs_of_nonneg (sub_nonneg.mpr has)] at hout
    linarith [hb.2]
  · intro hsa
    rw [abs_of_neg (sub_neg.mpr hsa)] at hout
    linarith [hb.1]

section Collapse
variable {U : Type u} {T : Type v}

/-- The deleted strips: a *union* over the finite limit set. -/
def deletedStrip (f : U → T → ℝ) (h : T → ℝ) (F : Set U) (r : ℝ) : Set (T × ℝ) :=
  {ω | ∃ a ∈ F, |ω.2 - f a ω.1| ≤ r * h ω.1}

theorem threshold_equal_outside_strip (d : U → U → ℝ) (f : U → T → ℝ) (h : T → ℝ)
    (F : Set U) (r : ℝ) (hh : ∀ t, 0 ≤ h t)
    (henv : ∀ x y t, |f x t - f y t| ≤ h t * d x y)
    {x a : U} (ha : a ∈ F) (hxa : d x a ≤ r)
    {ω : T × ℝ} (hout : ω ∉ deletedStrip f h F r) :
    (ω.2 < f x ω.1 ↔ ω.2 < f a ω.1) := by
  have hnear : |f x ω.1 - f a ω.1| ≤ r * h ω.1 :=
    calc |f x ω.1 - f a ω.1| ≤ h ω.1 * d x a := henv x a ω.1
      _ ≤ h ω.1 * r := mul_le_mul_of_nonneg_left hxa (hh ω.1)
      _ = r * h ω.1 := mul_comm _ _
  have hfar : r * h ω.1 < |ω.2 - f a ω.1| := by
    apply lt_of_not_ge
    intro hbad
    exact hout ⟨a, ha, hbad⟩
  exact threshold_stability hnear hfar

end Collapse

end MagCore
