import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Matrix.Order
import Results.MagnitudeContinuity.Defs
import Results.MagnitudeContinuity.Solution.Bridge
import Results.MagnitudeContinuity.Solution.Envelope
import Results.MagnitudeContinuity.Solution.Signature

/-!
# Subsets of `L₁` are positive definite

Every metric space isometrically embedded in `L₁(ν)` is positive definite.  This is used by
`main_of_L1` in `Solution/Main.lean`, which makes the abstract's formulation of Theorem 1.1 (subspaces of
`L₁`) unconditional; `main` itself assumes `IsPositiveDefinite U` instead.

The proof is the paper's argument after Lemma 3.2 (a cut metric gives a strictly positive definite
exponential kernel): threshold cuts and signature classes turn `exp (-d)` into the kernel
`cutProduct J cs` of a finite list `cs` of factor cuts (`exists_cutList`).  Instead of the Schur
product theorem we use the one-step estimate
`Q (cutStep b s A) ≥ (1 - s²) Q (cutStep b 0 A)` for positive `A`: iterating it over the list `cs`
replaces every nontrivial cut (`s < 1`) by a cut with `s = 0`.  Since the nontrivial cuts separate
every pair of distinct points, the resulting kernel is the identity matrix, so the quadratic form of
`exp (-d)` dominates a positive multiple of `∑ xᵢ²`.
-/

open MeasureTheory MagCore

noncomputable section

namespace Results.MagnitudeContinuity

section KernelLevel

variable {ι : Type*} [Fintype ι]

/-- A nontrivial cut (`s < 1`) is replaced by the cut with the same labelling and `s = 0`. -/
def zeroNontrivial (c : FactorCut ι) : FactorCut ι := if c.2 < 1 then (c.1, 0) else c

/-- The loss factor `1 - s²` paid for a nontrivial cut (`s < 1`); trivial cuts cost nothing. -/
def gapWeight (c : FactorCut ι) : ℝ := if c.2 < 1 then 1 - c.2 ^ 2 else 1

omit [Fintype ι] in
theorem cutStep_one (b : ι → Bool) (A : Kernel ι) : cutStep b 1 A = A := by
  funext i j
  simp [cutStep]

omit [Fintype ι] in
theorem cutStep_zero_eq_cutMask (b : ι → Bool) (A : Kernel ι) : cutStep b 0 A = cutMask b A := by
  funext i j
  by_cases h : b i = b j <;> simp [cutStep, cutMask, h]

/-- The one-step estimate: a cut with half-factor `s` costs at most `1 - s²` against the cut
with half-factor `0`. -/
theorem cutStep_lower_zero {A : Kernel ι} (hA : qPositive A) (b : ι → Bool) {s : ℝ} (x : ι → ℝ) :
    (1 - s ^ 2) * quadratic (cutStep b 0 A) x ≤ quadratic (cutStep b s A) x := by
  rw [cutStep_zero_eq_cutMask, quadratic_cutStep]
  have := mul_nonneg (sq_nonneg s) (hA x)
  linarith

/-- Cut steps commute with the product of cuts. -/
theorem cutStep_cutProduct_comm (b : ι → Bool) (s : ℝ) (M : Kernel ι)
    (cs : List (FactorCut ι)) :
    cutStep b s (cutProduct M cs) = cutProduct (cutStep b s M) cs := by
  funext i j
  simp only [cutStep, cutProduct_entry]
  ring

/-- Iterating the one-step estimate: replacing every nontrivial cut by a zero cut costs the
product of the gap weights. -/
theorem cutProduct_lower_zero (cs : List (FactorCut ι)) (hc : admissibleFactors cs) :
    ∀ M : Kernel ι, qPositive M → ∀ x : ι → ℝ,
      (cs.map gapWeight).prod * quadratic (cutProduct M (cs.map zeroNontrivial)) x ≤
        quadratic (cutProduct M cs) x := by
  induction cs with
  | nil =>
    intro M _ x
    simp [cutProduct]
  | cons c cs ih =>
    intro M hM x
    have hc' := admissible_tail hc
    obtain ⟨h0, h1⟩ := admissible_head hc
    by_cases hlt : c.2 < 1
    · have hs2 : 0 ≤ 1 - c.2 ^ 2 := by nlinarith
      have hM' : qPositive (cutStep c.1 0 M) := qPositive_cutStep hM c.1 le_rfl zero_le_one
      have hN : qPositive (cutProduct M cs) := (cutProduct_positive_lower M hM cs hc').1
      have hih := ih hc' (cutStep c.1 0 M) hM' x
      have e1 : cutProduct M ((c :: cs).map zeroNontrivial) =
          cutProduct (cutStep c.1 0 M) (cs.map zeroNontrivial) := by
        simp only [List.map_cons, zeroNontrivial, hlt, if_true, cutProduct]
        exact cutStep_cutProduct_comm c.1 0 M _
      have e2 : cutProduct M (c :: cs) = cutStep c.1 c.2 (cutProduct M cs) := rfl
      have e3 := cutStep_cutProduct_comm c.1 0 M cs
      have hstep := cutStep_lower_zero hN c.1 (s := c.2) x
      have hw : ((c :: cs).map gapWeight).prod = (1 - c.2 ^ 2) * (cs.map gapWeight).prod := by
        simp [gapWeight, hlt]
      rw [hw, e1, e2]
      rw [e3] at hstep
      calc (1 - c.2 ^ 2) * (cs.map gapWeight).prod *
            quadratic (cutProduct (cutStep c.1 0 M) (cs.map zeroNontrivial)) x
          = (1 - c.2 ^ 2) * ((cs.map gapWeight).prod *
            quadratic (cutProduct (cutStep c.1 0 M) (cs.map zeroNontrivial)) x) := by ring
        _ ≤ (1 - c.2 ^ 2) * quadratic (cutProduct (cutStep c.1 0 M) cs) x :=
            mul_le_mul_of_nonneg_left hih hs2
        _ ≤ quadratic (cutStep c.1 c.2 (cutProduct M cs)) x := hstep
    · have h1' : c.2 = 1 := le_antisymm h1 (not_lt.1 hlt)
      have e1 : cutProduct M ((c :: cs).map zeroNontrivial) =
          cutProduct M (cs.map zeroNontrivial) := by
        simp only [List.map_cons, zeroNontrivial, if_neg hlt, cutProduct]
        rw [h1']
        exact cutStep_one _ _
      have e2 : cutProduct M (c :: cs) = cutProduct M cs := by
        simp only [cutProduct, h1']
        exact cutStep_one _ _
      have hw : ((c :: cs).map gapWeight).prod = (cs.map gapWeight).prod := by
        simp [gapWeight, hlt]
      rw [hw, e1, e2]
      exact ih hc' M hM x

omit [Fintype ι] in
theorem gapWeight_pos {c : FactorCut ι} (hc : 0 ≤ c.2 ∧ c.2 ≤ 1) : 0 < gapWeight c := by
  unfold gapWeight
  split_ifs with h
  · nlinarith [hc.1]
  · exact one_pos

/-- If the nontrivial cuts of `cs` separate every pair of distinct points, then the kernel with
the nontrivial cuts replaced by zero cuts is the identity matrix. -/
theorem cutProduct_zeroNontrivial_entry [DecidableEq ι] (cs : List (FactorCut ι))
    (hsep : ∀ i j : ι, i ≠ j → ∃ c ∈ cs, c.2 < 1 ∧ c.1 i ≠ c.1 j) (i j : ι) :
    cutProduct (onesKernel (ι := ι)) (cs.map zeroNontrivial) i j = if i = j then 1 else 0 := by
  rw [cutProduct_entry, pairFactor_eq_prod, List.map_map]
  simp only [onesKernel, one_mul]
  by_cases hij : i = j
  · subst hij
    simp [Function.comp_def]
  · simp only [hij, if_false]
    obtain ⟨c, hcmem, hc1, hc2⟩ := hsep i j hij
    refine List.prod_eq_zero (List.mem_map.mpr ⟨c, hcmem, ?_⟩)
    simp [Function.comp, zeroNontrivial, hc1, hc2]

theorem quadratic_identity [DecidableEq ι] (x : ι → ℝ) :
    quadratic (fun i j : ι => if i = j then (1 : ℝ) else 0) x = ∑ i, x i ^ 2 := by
  unfold quadratic bilinear
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_ite, sq]

/-- A list of admissible cuts whose nontrivial members separate every pair of distinct points
gives a positive definite kernel, with an explicit positive coercivity constant. -/
theorem exists_coercive_cutProduct [DecidableEq ι] (cs : List (FactorCut ι))
    (hc : admissibleFactors cs)
    (hsep : ∀ i j : ι, i ≠ j → ∃ c ∈ cs, c.2 < 1 ∧ c.1 i ≠ c.1 j) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x : ι → ℝ,
      lam * ∑ i, x i ^ 2 ≤ quadratic (cutProduct (onesKernel (ι := ι)) cs) x := by
  refine ⟨(cs.map gapWeight).prod, ?_, fun x => ?_⟩
  · refine List.prod_pos fun a ha => ?_
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp ha
    exact gapWeight_pos (hc c hcm)
  · have h := cutProduct_lower_zero cs hc (onesKernel (ι := ι)) qPositive_onesKernel x
    have hid : cutProduct (onesKernel (ι := ι)) (cs.map zeroNontrivial) =
        fun i j : ι => if i = j then (1 : ℝ) else 0 := by
      funext i j
      exact cutProduct_zeroNontrivial_entry cs hsep i j
    rw [hid, quadratic_identity] at h
    exact h

/-- A pairwise separating nontrivial cut exists whenever the entrywise factor is not `1`. -/
theorem exists_sep_of_pairFactor_ne_one {cs : List (FactorCut ι)} (hc : admissibleFactors cs)
    {i j : ι} (h : pairFactor cs i j ≠ 1) : ∃ c ∈ cs, c.2 < 1 ∧ c.1 i ≠ c.1 j := by
  induction cs with
  | nil => exact absurd (by simp [pairFactor]) h
  | cons c cs ih =>
    by_cases hij : c.1 i = c.1 j
    · have h' : pairFactor cs i j ≠ 1 := by simpa [pairFactor, hij] using h
      obtain ⟨d, hd, hd1, hd2⟩ := ih (admissible_tail hc) h'
      exact ⟨d, List.mem_cons_of_mem _ hd, hd1, hd2⟩
    · by_cases hlt : c.2 < 1
      · exact ⟨c, List.mem_cons_self .., hlt, hij⟩
      · have h1 : c.2 = 1 := le_antisymm (admissible_head hc).2 (not_lt.1 hlt)
        have h' : pairFactor cs i j ≠ 1 := by simpa [pairFactor, hij, h1] using h
        obtain ⟨d, hd, hd1, hd2⟩ := ih (admissible_tail hc) h'
        exact ⟨d, List.mem_cons_of_mem _ hd, hd1, hd2⟩

/-- A symmetric kernel whose quadratic form dominates a positive multiple of `∑ xᵢ²` is a positive
definite matrix. -/
theorem posDef_of_quadratic_lower (K : Kernel ι) (hK : symmetric K) {lam : ℝ} (hlam : 0 < lam)
    (h : ∀ x : ι → ℝ, lam * ∑ i, x i ^ 2 ≤ quadratic K x) : (Matrix.of K).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, hK i j]
  · have hq := quadratic_eq_dotProduct (Matrix.of K) x
    have hq' : quadratic K x = quadratic (Matrix.of K) x := rfl
    rw [star_trivial, ← hq, ← hq']
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have hxi : x i ≠ 0 := hi
    have hsum : 0 < ∑ i, x i ^ 2 :=
      lt_of_lt_of_le (by positivity)
        (Finset.single_le_sum (f := fun i => x i ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i))
    exact lt_of_lt_of_le (mul_pos hlam hsum) (h x)

end KernelLevel

theorem isPositiveDefinite_of_isometry_Lp {S : Type*} [MetricSpace S] {T : Type*}
    [MeasurableSpace T] (ν : Measure T) [SigmaFinite ν] (ι : S → Lp ℝ 1 ν) (hι : Isometry ι) :
    IsPositiveDefinite S := by
  classical
  intro A hA
  -- measurable representatives of the images of the points of `A`
  set f : A → T → ℝ := fun i => ⇑(ι (i : S)) with hfdef
  have hfm : ∀ i, Measurable (f i) := fun i => (Lp.stronglyMeasurable (ι (i : S))).measurable
  -- the threshold cuts have measure the distance
  have hdist : ∀ i j : A, (ν.prod volume) {ω | bit f i ω ≠ bit f j ω} =
      ENNReal.ofReal (dist (i : S) (j : S)) := by
    intro i j
    rw [measure_bit_ne ν hfm i j, ← hι.dist_eq, dist_eq_norm, ofReal_norm_lp_eq_lintegral ν]
    refine lintegral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (ι (i : S)) (ι (j : S))] with t ht
    rw [ht]
    rfl
  have hfin : ∀ i j : A, (ν.prod volume) (Set.univ ∩ {ω | bit f i ω ≠ bit f j ω}) ≠ ⊤ := by
    intro i j
    rw [Set.univ_inter, hdist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨cs, hadm, hpair, -⟩ :=
    exists_cutList (ν.prod volume) (fun i : A => bit f i) (fun i => measurable_bit hfm i)
      MeasurableSet.univ hfin
  have hpair' : ∀ i j : A, pairFactor cs i j = Real.exp (-dist (i : S) (j : S)) := by
    intro i j
    rw [hpair, Set.univ_inter, hdist, ENNReal.toReal_ofReal dist_nonneg]
  have hsep : ∀ i j : A, i ≠ j → ∃ c ∈ cs, c.2 < 1 ∧ c.1 i ≠ c.1 j := by
    intro i j hij
    refine exists_sep_of_pairFactor_ne_one hadm ?_
    rw [hpair']
    intro h1
    have h2 := Real.exp_eq_one_iff _ |>.mp h1
    have h3 : 0 < dist (i : S) (j : S) := dist_pos.mpr fun h => hij (Subtype.ext h)
    linarith
  obtain ⟨lam, hlam, hcoer⟩ := exists_coercive_cutProduct cs hadm hsep
  have hker : cutProduct (onesKernel (ι := A)) cs = fun i j : A => Real.exp (-dist (i : S) (j : S)) := by
    funext i j
    rw [cutProduct_entry, hpair']
    simp [onesKernel]
  rw [hker] at hcoer
  have hsymm : symmetric (fun i j : A => Real.exp (-dist (i : S) (j : S))) := by
    intro i j
    simp only [dist_comm (i : S) (j : S)]
  exact posDef_of_quadratic_lower _ hsymm hlam hcoer

end Results.MagnitudeContinuity
