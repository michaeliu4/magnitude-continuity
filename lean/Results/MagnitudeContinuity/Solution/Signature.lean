import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Exp
import Results.MagnitudeContinuity.Solution.Core.FiniteCuts
import Results.MagnitudeContinuity.Solution.Core.Aggregation

/-!
# Signature regrouping: measurable cuts give finite cut data

Module M2.  Given a measure space `(Ω, μ)` and finitely many measurable binary labellings
(cut bits), regroup the cuts by their signature classes, producing the finite factor-cut lists
of `Solution.Core` whose kernels reproduce `exp (-d)` for `d` the measure of the disagreement set.
-/

open MeasureTheory MagCore

noncomputable section

namespace Results.MagnitudeContinuity

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The signature class of `σ` for a finite family of bits. -/
def sigClass {ι : Type*} (b : ι → Ω → Bool) (σ : ι → Bool) : Set Ω := {ω | ∀ i, b i ω = σ i}

theorem measurableSet_sigClass {ι : Type*} [Finite ι] (b : ι → Ω → Bool)
    (hb : ∀ i, Measurable (b i)) (σ : ι → Bool) : MeasurableSet (sigClass b σ) := by
  have : sigClass b σ = ⋂ i, b i ⁻¹' {σ i} := by
    ext ω; simp [sigClass]
  rw [this]
  exact MeasurableSet.iInter fun i => hb i (measurableSet_singleton _)

theorem measure_eq_sum_sigClass {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure Ω)
    (b : ι → Ω → Bool) (hb : ∀ i, Measurable (b i)) {S : Set Ω} (hS : MeasurableSet S) :
    μ S = ∑ σ : ι → Bool, μ (S ∩ sigClass b σ) := by
  have hU : S = ⋃ σ : ι → Bool, S ∩ sigClass b σ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨fun i => b i ω, h, fun i => rfl⟩, fun ⟨_, h, _⟩ => h⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun σ : ι → Bool => S ∩ sigClass b σ) := by
    intro σ τ hστ
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨_, h1⟩ ⟨_, h2⟩
    apply hστ
    funext i
    rw [← h1 i, ← h2 i]
  calc μ S = μ (⋃ σ : ι → Bool, S ∩ sigClass b σ) := by rw [← hU]
    _ = ∑' σ : ι → Bool, μ (S ∩ sigClass b σ) :=
        measure_iUnion hdisj fun σ => hS.inter (measurableSet_sigClass b hb σ)
    _ = ∑ σ : ι → Bool, μ (S ∩ sigClass b σ) := tsum_fintype _

theorem pairFactor_eq_prod {ι : Type*} (l : List (FactorCut ι)) (i j : ι) :
    pairFactor l i j = (l.map fun c => if c.1 i = c.1 j then (1 : ℝ) else c.2 ^ 2).prod := by
  induction l with
  | nil => simp [pairFactor]
  | cons c cs ih => simp [pairFactor, ih]

theorem factorProduct_eq_prod {ι : Type*} (l : List (FactorCut ι)) :
    factorProduct l = (l.map Prod.snd).prod := by
  induction l with
  | nil => simp [factorProduct]
  | cons c cs ih => simp [factorProduct, ih]

/-- Regrouping the cuts inside a measurable set `A` by signature on a finite family of bits. -/
theorem exists_cutList {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure Ω)
    (b : ι → Ω → Bool) (hb : ∀ i, Measurable (b i)) {A : Set Ω} (hA : MeasurableSet A)
    (hfin : ∀ i j, μ (A ∩ {ω | b i ω ≠ b j ω}) ≠ ⊤) :
    ∃ cs : List (FactorCut ι), admissibleFactors cs ∧
      (∀ i j, pairFactor cs i j = Real.exp (-(μ (A ∩ {ω | b i ω ≠ b j ω})).toReal)) ∧
      (μ A ≠ ⊤ → factorProduct cs = Real.exp (-(μ A).toReal / 2)) := by
  classical
  set f : (ι → Bool) → FactorCut ι :=
    fun σ => (σ, Real.exp (-(μ (A ∩ sigClass b σ)).toReal / 2)) with hf
  refine ⟨(Finset.univ : Finset (ι → Bool)).toList.map f, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hc
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    have := ENNReal.toReal_nonneg (a := μ (A ∩ sigClass b σ))
    linarith
  · intro i j
    rw [pairFactor_eq_prod, List.map_map, Finset.prod_map_toList]
    have hterm : ∀ σ : ι → Bool,
        (if σ i = σ j then (1 : ℝ) else Real.exp (-(μ (A ∩ sigClass b σ)).toReal / 2) ^ 2) =
          Real.exp (-(if σ i = σ j then 0 else (μ (A ∩ sigClass b σ)).toReal)) := by
      intro σ
      by_cases h : σ i = σ j
      · simp [h]
      · simp only [h, if_false]
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast; ring
    have hset : ∀ σ : ι → Bool, A ∩ {ω | b i ω ≠ b j ω} ∩ sigClass b σ =
        if σ i = σ j then ∅ else A ∩ sigClass b σ := by
      intro σ
      by_cases h : σ i = σ j
      · simp only [h, if_true]
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, sigClass, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨⟨-, hne⟩, hω⟩
        exact hne (by rw [hω i, hω j, h])
      · simp only [h, if_false]
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, sigClass]
        constructor
        · rintro ⟨⟨hA', -⟩, hω⟩
          exact ⟨hA', hω⟩
        · rintro ⟨hA', hω⟩
          refine ⟨⟨hA', ?_⟩, hω⟩
          rw [hω i, hω j]
          exact h
    have hsum : (μ (A ∩ {ω | b i ω ≠ b j ω})).toReal =
        ∑ σ : ι → Bool, (if σ i = σ j then 0 else (μ (A ∩ sigClass b σ)).toReal) := by
      have hmeas : MeasurableSet (A ∩ {ω | b i ω ≠ b j ω}) := by
        refine hA.inter ?_
        have : {ω | b i ω ≠ b j ω} = {ω | b i ω = b j ω}ᶜ := rfl
        rw [this]
        exact (measurableSet_eq_fun (hb i) (hb j)).compl
      rw [measure_eq_sum_sigClass μ b hb hmeas, ENNReal.toReal_sum]
      · refine Finset.sum_congr rfl fun σ _ => ?_
        rw [hset σ]
        by_cases h : σ i = σ j <;> simp [h]
      · intro σ _
        exact ne_top_of_le_ne_top (hfin i j) (measure_mono Set.inter_subset_left)
    simp only [Function.comp_apply, hf]
    simp_rw [hterm]
    rw [hsum, ← Finset.sum_neg_distrib, Real.exp_sum]
  · intro hμ
    rw [factorProduct_eq_prod, List.map_map, Finset.prod_map_toList]
    have hsum : (μ A).toReal = ∑ σ : ι → Bool, (μ (A ∩ sigClass b σ)).toReal := by
      rw [measure_eq_sum_sigClass μ b hb hA, ENNReal.toReal_sum]
      intro σ _
      exact ne_top_of_le_ne_top hμ (measure_mono Set.inter_subset_left)
    have hdiv : -(∑ σ : ι → Bool, (μ (A ∩ sigClass b σ)).toReal) / 2 =
        ∑ σ : ι → Bool, (-(μ (A ∩ sigClass b σ)).toReal / 2) := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_neg_distrib]
    rw [hsum, hdiv, Real.exp_sum]
    refine Finset.prod_congr rfl fun σ _ => ?_
    simp [hf, neg_div]

/-- Splitting a finite-measure set along a measurable set multiplies the two exponentials. -/
theorem exp_split_measure (μ : Measure Ω) {E D : Set Ω} (hE : MeasurableSet E)
    (hD : μ D ≠ ⊤) :
    Real.exp (-(μ (Eᶜ ∩ D)).toReal) * Real.exp (-(μ (E ∩ D)).toReal) =
      Real.exp (-(μ D).toReal) := by
  have h := measure_inter_add_sdiff (μ := μ) D hE
  rw [Set.inter_comm D E, Set.sdiff_eq_compl_inter] at h
  have h1 : μ (E ∩ D) ≠ ⊤ := ne_top_of_le_ne_top hD (measure_mono Set.inter_subset_right)
  have h2 : μ (Eᶜ ∩ D) ≠ ⊤ := ne_top_of_le_ne_top hD (measure_mono Set.inter_subset_right)
  rw [← Real.exp_add, ← h, ENNReal.toReal_add h1 h2]
  congr 1
  ring

/-- Finite cut data for the upper bound.  `bF` are the bits of the points of the finite limit set,
`bX` those of the approximants; `E` is the deleted set of cuts; outside `E` every approximant has
the bit of its center `p i`. -/
theorem cut_data {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    (μ : Measure Ω) (bF : κ → Ω → Bool) (bX : ι → Ω → Bool)
    (hbF : ∀ a, Measurable (bF a)) (hbX : ∀ i, Measurable (bX i))
    (hFfin : ∀ a a', μ {ω | bF a ω ≠ bF a' ω} ≠ ⊤)
    (hXfin : ∀ i j, μ {ω | bX i ω ≠ bX j ω} ≠ ⊤)
    (p : ι → κ) {E : Set Ω} (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hcollapse : ∀ ω ∉ E, ∀ i, bX i ω = bF (p i) ω) :
    ∃ (K0 : Kernel κ) (csF : List (FactorCut κ)) (csX : List (FactorCut ι)),
      symmetric K0 ∧ qPositive K0 ∧ (∀ a b, 0 ≤ K0 a b ∧ K0 a b ≤ 1) ∧
      admissibleFactors csF ∧ admissibleFactors csX ∧
      factorProduct csX = factorProduct csF ∧
      factorProduct csF = Real.exp (-(μ E).toReal / 2) ∧
      (∀ a b, cutProduct K0 csF a b = Real.exp (-(μ {ω | bF a ω ≠ bF b ω}).toReal)) ∧
      (∀ i j, cutProduct (pullbackKernel K0 p) csX i j =
        Real.exp (-(μ {ω | bX i ω ≠ bX j ω}).toReal)) := by
  classical
  obtain ⟨csR, hRadm, hRpair, -⟩ := exists_cutList μ bF hbF hE.compl
    (fun i j => ne_top_of_le_ne_top (hFfin i j) (measure_mono Set.inter_subset_right))
  obtain ⟨csF, hFadm, hFpair, hFprod⟩ := exists_cutList μ bF hbF hE
    (fun i j => ne_top_of_le_ne_top (hFfin i j) (measure_mono Set.inter_subset_right))
  obtain ⟨csX, hXadm, hXpair, hXprod⟩ := exists_cutList μ bX hbX hE
    (fun i j => ne_top_of_le_ne_top (hXfin i j) (measure_mono Set.inter_subset_right))
  have hK0 : ∀ a b, cutProduct (onesKernel (ι := κ)) csR a b =
      Real.exp (-(μ (Eᶜ ∩ {ω | bF a ω ≠ bF b ω})).toReal) := by
    intro a b
    rw [cutProduct_entry, hRpair]
    simp [onesKernel]
  refine ⟨cutProduct (onesKernel (ι := κ)) csR, csF, csX,
    symmetric_cutProduct (fun _ _ => rfl) csR,
    (cutProduct_positive_lower _ qPositive_onesKernel csR hRadm).1, ?_, hFadm, hXadm,
    ?_, hFprod hEfin, ?_, ?_⟩
  · intro a b
    rw [hK0]
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by
      have := ENNReal.toReal_nonneg (a := μ (Eᶜ ∩ {ω | bF a ω ≠ bF b ω}))
      linarith)⟩
  · rw [hXprod hEfin, hFprod hEfin]
  · intro a b
    rw [cutProduct_entry, hK0, hFpair]
    exact exp_split_measure μ hE (hFfin a b)
  · intro i j
    rw [cutProduct_entry]
    show cutProduct (onesKernel (ι := κ)) csR (p i) (p j) * pairFactor csX i j = _
    rw [hK0, hXpair]
    have hset : Eᶜ ∩ {ω | bF (p i) ω ≠ bF (p j) ω} = Eᶜ ∩ {ω | bX i ω ≠ bX j ω} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hω, h⟩
        exact ⟨hω, by rwa [hcollapse ω hω i, hcollapse ω hω j]⟩
      · rintro ⟨hω, h⟩
        exact ⟨hω, by rwa [hcollapse ω hω i, hcollapse ω hω j] at h⟩
    rw [hset]
    exact exp_split_measure μ hE (hXfin i j)

end Results.MagnitudeContinuity
