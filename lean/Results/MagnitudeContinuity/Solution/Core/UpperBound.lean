import Results.MagnitudeContinuity.Solution.Core.FiniteCuts
import Results.MagnitudeContinuity.Solution.Core.Perturbation

/-!
# The combinatorial core of the magnitude-continuity proof

`κ` indexes the fixed finite limit set `F`, `ι` indexes an approximant `X` of **arbitrary**
finite cardinality, `p : ι → κ` sends a point to the centre of a ball containing it and
`e : κ → ι` picks one representative of `X` near each centre.

* `K0` is the retained-cut kernel on `F` (in the application `exp (-d_r(a,b))`);
* by exact collapse the retained-cut kernel on `X` is its pullback along `p`;
* `csF`, `csX` are the deleted cuts, regrouped by their (finitely many) signatures on
  `F` and on `X`; both have total half-factor `S` (in the application `S = exp (-μ(E_r)/2)`).

The conclusion is the two-sided, cardinality-free estimate
`Mag F - m² ε' / lam² ≤ Mag X ≤ Mag F + 2 m² (1 - S) / lam²`, and the cluster sums of the
weighting of `X` converge to the weighting of `F` (`cut_weight_convergence`).
-/

set_option linter.unusedSectionVars false

noncomputable section
open scoped BigOperators

namespace MagCore

universe u v

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem pullback_smul (K0 : Kernel κ) (c : ℝ) (p : ι → κ) :
    pullbackKernel (fun a b => c * K0 a b) p = fun i j => c * pullbackKernel K0 p i j := rfl

/-- Cut deletion + exact collapse give the Loewner domination `P (c • K0) Pᵀ ≤ Z_X`. -/
theorem domination_of_cuts (K0 : Kernel κ) (hK0 : qPositive K0) (p : ι → κ)
    (csX : List (FactorCut ι)) (hX : admissibleFactors csX) :
    qLE (pullbackKernel (fun a b => factorProduct csX * K0 a b) p)
      (cutProduct (pullbackKernel K0 p) csX) := by
  intro x
  rw [pullback_smul, quadratic_smul_kernel]
  exact (cutProduct_positive_lower _ (qPositive_pullback hK0 p) csX hX).2 x

/-- The auxiliary matrix `S • K0` (`S = ∏ s = exp (-M/2)`) is entrywise within `1 - S` of `Z_F`.
The difference is no longer sign-definite, only small in absolute value. -/
theorem close_of_cuts (K0 : Kernel κ) (hK0e : ∀ a b, 0 ≤ K0 a b ∧ K0 a b ≤ 1)
    (csF : List (FactorCut κ)) (hF : admissibleFactors csF) (a b : κ) :
    |cutProduct K0 csF a b - factorProduct csF * K0 a b| ≤ 1 - factorProduct csF := by
  rw [cutProduct_entry]
  obtain ⟨hl, hu⟩ := pairFactor_bounds hF a b
  obtain ⟨h0, h1⟩ := hK0e a b
  have hc0 := factorProduct_nonneg hF
  have hc1 := factorProduct_le_one hF
  have e : K0 a b * pairFactor csF a b - factorProduct csF * K0 a b =
      K0 a b * (pairFactor csF a b - factorProduct csF) := by ring
  rw [e, abs_le]
  constructor
  · nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1), mul_nonneg h0 (sub_nonneg.mpr hc1)]
  · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hc1)]

/-- **Upper bound**, uniform in the cardinality of `ι`. -/
theorem cut_upper_bound (K0 : Kernel κ) (hK0s : symmetric K0) (hK0 : qPositive K0)
    (hK0e : ∀ a b, 0 ≤ K0 a b ∧ K0 a b ≤ 1)
    (csF : List (FactorCut κ)) (hF : admissibleFactors csF)
    (csX : List (FactorCut ι)) (hX : admissibleFactors csX)
    (hc : factorProduct csX = factorProduct csF) (p : ι → κ)
    {lam : ℝ} (hlam : 0 < lam) (hZ : coercive (cutProduct K0 csF) lam)
    (hsmall : (Fintype.card κ : ℝ) * (1 - factorProduct csF) ≤ lam / 2)
    {wX : ι → ℝ} (hwX : weighting (cutProduct (pullbackKernel K0 p) csX) wX)
    {wF : κ → ℝ} (hwF : weighting (cutProduct K0 csF) wF) :
    mass wX ≤ mass wF +
      2 * (Fintype.card κ : ℝ) ^ 2 * (1 - factorProduct csF) / lam ^ 2 := by
  have hdom := domination_of_cuts K0 hK0 p csX hX
  rw [hc] at hdom
  exact upper_perturbation_additive (symmetric_cutProduct hK0s csF) hlam hZ
    (sub_nonneg.mpr (factorProduct_le_one hF)) (close_of_cuts K0 hK0e csF hF) hsmall p hdom
    hwX hwF

end MagCore
