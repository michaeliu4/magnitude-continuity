import Results.MagnitudeContinuity.Solution.Core.Quadratic

/-!
# Finite cut deletion (the Loewner-order lower bound), sharp half-factor form

A *factor cut* is a pair `(b, s)`: a binary labelling `b : ι → Bool` of the points and a
**half-factor** `s ∈ [0,1]`.  In the application a cut class of mass `w` has
`s = exp (-w/2)`, and `cutStep b s A` multiplies the entry `A i j` by `s² = exp (-w)`
exactly when the cut separates `i` from `j`.

Central theorem: applying any finite list of admissible cuts to a positive-semidefinite kernel `A`
keeps it positive semidefinite **and** dominates `(∏ s) • A` in the signed quadratic-form order.
So deleting cuts of total mass `M` costs the factor `exp (-M/2)` — not `exp (-M)` — and the cost
does not depend on `|ι|` or on the number of cuts.  The half exponent is first-order sharp
(two points at distance `d`: the best constant is `(1 + e^{-d})/2 = 1 - d/2 + O(d²)`).
-/

set_option linter.unusedSectionVars false

noncomputable section
open scoped BigOperators

namespace MagCore

universe u

variable {ι : Type u} [Fintype ι]

def cutMask (b : ι → Bool) (A : Kernel ι) : Kernel ι :=
  fun i j => if b i = b j then A i j else 0

def restrictBit (c : Bool) (b : ι → Bool) (x : ι → ℝ) : ι → ℝ :=
  fun i => if b i = c then x i else 0

def cutStep (b : ι → Bool) (s : ℝ) (A : Kernel ι) : Kernel ι :=
  fun i j => A i j * (if b i = b j then 1 else s ^ 2)

theorem restrictBit_add (b : ι → Bool) (x : ι → ℝ) :
    restrictBit false b x + restrictBit true b x = x := by
  funext i
  cases hi : b i <;> simp [restrictBit, hi]

theorem quadratic_cutMask (b : ι → Bool) (A : Kernel ι) (x : ι → ℝ) :
    quadratic (cutMask b A) x =
      quadratic A (restrictBit false b x) + quadratic A (restrictBit true b x) := by
  unfold quadratic bilinear
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  cases hi : b i <;> cases hj : b j <;> simp [cutMask, restrictBit, hi, hj]

theorem qPositive_cutMask {A : Kernel ι} (hA : qPositive A) (b : ι → Bool) :
    qPositive (cutMask b A) := by
  intro x
  rw [quadratic_cutMask]
  exact add_nonneg (hA _) (hA _)

/-- The full form is at most twice the masked form: `Q_A ≤ 2 Q_{mask}`. -/
theorem quadratic_le_two_cutMask {A : Kernel ι} (hA : qPositive A) (b : ι → Bool)
    (x : ι → ℝ) : quadratic A x ≤ 2 * quadratic (cutMask b A) x := by
  have h := quadratic_add_le hA (restrictBit false b x) (restrictBit true b x)
  rw [restrictBit_add] at h
  rw [quadratic_cutMask]
  exact h

theorem cutStep_decomposition (b : ι → Bool) (s : ℝ) (A : Kernel ι) :
    cutStep b s A = fun i j => s ^ 2 * A i j + (1 - s ^ 2) * cutMask b A i j := by
  funext i j
  by_cases h : b i = b j
  · simp only [cutStep, cutMask, h, ite_true]; ring
  · simp only [cutStep, cutMask, h, ite_false]; ring

theorem quadratic_cutStep (b : ι → Bool) (s : ℝ) (A : Kernel ι) (x : ι → ℝ) :
    quadratic (cutStep b s A) x =
      s ^ 2 * quadratic A x + (1 - s ^ 2) * quadratic (cutMask b A) x := by
  rw [cutStep_decomposition, quadratic_linear_combination]

theorem qPositive_cutStep {A : Kernel ι} (hA : qPositive A) (b : ι → Bool) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : qPositive (cutStep b s A) := by
  intro x
  rw [quadratic_cutStep]
  have h1 : s ^ 2 ≤ 1 := by nlinarith
  exact add_nonneg (mul_nonneg (sq_nonneg s) (hA x))
    (mul_nonneg (sub_nonneg.mpr h1) (qPositive_cutMask hA b x))

/-- **Sharp one-cut bound**: a cut with entry factor `s²` costs only the factor `s`. -/
theorem cutStep_lower {A : Kernel ι} (hA : qPositive A) (b : ι → Bool) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : ι → ℝ) :
    s * quadratic A x ≤ quadratic (cutStep b s A) x := by
  rw [quadratic_cutStep]
  have hT := qPositive_cutMask hA b x
  have hQ := quadratic_le_two_cutMask hA b x
  have h1 : 0 ≤ s * (1 - s) := mul_nonneg hs0 (sub_nonneg.mpr hs1)
  have h2 := mul_nonneg h1 (sub_nonneg.mpr hQ)
  have h3 := mul_nonneg (sq_nonneg (1 - s)) hT
  nlinarith

theorem symmetric_cutStep {A : Kernel ι} (hA : symmetric A) (b : ι → Bool) (s : ℝ) :
    symmetric (cutStep b s A) := by
  intro i j
  unfold cutStep
  rw [hA i j]
  by_cases h : b i = b j
  · simp [h]
  · have h' : ¬ b j = b i := fun e => h e.symm
    simp [h, h']

abbrev FactorCut (ι : Type u) := (ι → Bool) × ℝ

def cutProduct (A : Kernel ι) : List (FactorCut ι) → Kernel ι
  | [] => A
  | c :: cs => cutStep c.1 c.2 (cutProduct A cs)

/-- Product of the half-factors: `exp (-M/2)` in the application. -/
def factorProduct : List (FactorCut ι) → ℝ
  | [] => 1
  | c :: cs => c.2 * factorProduct cs

/-- The entrywise factor `∏ (if the cut separates i j then s² else 1)`. -/
def pairFactor : List (FactorCut ι) → ι → ι → ℝ
  | [], _, _ => 1
  | c :: cs, i, j => (if c.1 i = c.1 j then 1 else c.2 ^ 2) * pairFactor cs i j

def admissibleFactors (cs : List (FactorCut ι)) : Prop := ∀ c ∈ cs, 0 ≤ c.2 ∧ c.2 ≤ 1

theorem admissible_tail {c : FactorCut ι} {cs : List (FactorCut ι)}
    (h : admissibleFactors (c :: cs)) : admissibleFactors cs :=
  fun d hd => h d (List.mem_cons_of_mem _ hd)

theorem admissible_head {c : FactorCut ι} {cs : List (FactorCut ι)}
    (h : admissibleFactors (c :: cs)) : 0 ≤ c.2 ∧ c.2 ≤ 1 :=
  h c (List.mem_cons_self ..)

/-- **Central finite Loewner theorem** (all signed vectors, all finite sizes, sharp exponent). -/
theorem cutProduct_positive_lower (A : Kernel ι) (hA : qPositive A)
    (cs : List (FactorCut ι)) (hc : admissibleFactors cs) :
    qPositive (cutProduct A cs) ∧
      ∀ x : ι → ℝ, factorProduct cs * quadratic A x ≤ quadratic (cutProduct A cs) x := by
  induction cs with
  | nil =>
    refine ⟨hA, fun x => ?_⟩
    simp [cutProduct, factorProduct]
  | cons c cs ih =>
    have hhead := admissible_head hc
    obtain ⟨hp, hl⟩ := ih (admissible_tail hc)
    refine ⟨qPositive_cutStep hp c.1 hhead.1 hhead.2, fun x => ?_⟩
    calc factorProduct (c :: cs) * quadratic A x
          = c.2 * (factorProduct cs * quadratic A x) := by
            simp only [factorProduct]; ring
      _ ≤ c.2 * quadratic (cutProduct A cs) x := mul_le_mul_of_nonneg_left (hl x) hhead.1
      _ ≤ quadratic (cutProduct A (c :: cs)) x := cutStep_lower hp c.1 hhead.1 hhead.2 x

theorem symmetric_cutProduct {A : Kernel ι} (hA : symmetric A) (cs : List (FactorCut ι)) :
    symmetric (cutProduct A cs) := by
  induction cs with
  | nil => exact hA
  | cons c cs ih => exact symmetric_cutStep ih c.1 c.2

theorem cutProduct_entry (A : Kernel ι) (cs : List (FactorCut ι)) (i j : ι) :
    cutProduct A cs i j = A i j * pairFactor cs i j := by
  induction cs with
  | nil => simp [cutProduct, pairFactor]
  | cons c cs ih =>
    simp only [cutProduct, cutStep, pairFactor, ih]
    ring

theorem factorProduct_nonneg {cs : List (FactorCut ι)} (hc : admissibleFactors cs) :
    0 ≤ factorProduct cs := by
  induction cs with
  | nil => simp [factorProduct]
  | cons c cs ih =>
    exact mul_nonneg (admissible_head hc).1 (ih (admissible_tail hc))

theorem factorProduct_le_one {cs : List (FactorCut ι)} (hc : admissibleFactors cs) :
    factorProduct cs ≤ 1 := by
  induction cs with
  | nil => simp [factorProduct]
  | cons c cs ih =>
    have h1 := admissible_head hc
    have h2 := ih (admissible_tail hc)
    have h3 := factorProduct_nonneg (admissible_tail hc)
    simp only [factorProduct]
    nlinarith

/-- Every entrywise factor lies between the *square* of the half-factor product and `1`. -/
theorem pairFactor_bounds {cs : List (FactorCut ι)} (hc : admissibleFactors cs) (i j : ι) :
    factorProduct cs ^ 2 ≤ pairFactor cs i j ∧ pairFactor cs i j ≤ 1 := by
  induction cs with
  | nil => simp [factorProduct, pairFactor]
  | cons c cs ih =>
    obtain ⟨h0, h1⟩ := admissible_head hc
    obtain ⟨hl, hu⟩ := ih (admissible_tail hc)
    have hf0 := factorProduct_nonneg (admissible_tail hc)
    have hs2 : c.2 ^ 2 ≤ 1 := by nlinarith
    have hp0 : 0 ≤ pairFactor cs i j := le_trans (sq_nonneg _) hl
    simp only [factorProduct, pairFactor]
    by_cases h : c.1 i = c.1 j
    · simp only [h, ite_true, one_mul]
      refine ⟨?_, hu⟩
      have : (c.2 * factorProduct cs) ^ 2 = c.2 ^ 2 * factorProduct cs ^ 2 := by ring
      rw [this]
      nlinarith [sq_nonneg (factorProduct cs)]
    · simp only [h, ite_false]
      refine ⟨?_, by nlinarith [sq_nonneg c.2]⟩
      have : (c.2 * factorProduct cs) ^ 2 = c.2 ^ 2 * factorProduct cs ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hl (sq_nonneg _)

section OnePoint

/-- The all-ones kernel `J`; `xᵀ J x = (1ᵀx)²`. -/
def onesKernel : Kernel ι := fun _ _ => 1

theorem quadratic_onesKernel (x : ι → ℝ) : quadratic (onesKernel (ι := ι)) x = mass x ^ 2 := by
  unfold quadratic bilinear onesKernel mass
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem qPositive_onesKernel : qPositive (onesKernel (ι := ι)) := by
  intro x
  rw [quadratic_onesKernel]
  exact sq_nonneg _

end OnePoint

end MagCore
