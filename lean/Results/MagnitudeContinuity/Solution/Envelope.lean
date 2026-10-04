import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Results.MagnitudeContinuity.Solution.Auerbach
import Results.MagnitudeContinuity.Solution.Core.Pointwise

/-!
# `L₁` envelope and threshold cuts

Module M3b.  From a linear isometry `J : U →ₗᵢ[ℝ] Lp ℝ 1 ν` of a finite-dimensional normed space,
produce everywhere defined measurable representatives `f x` with a common integrable envelope `h`
(`∫ h ≤ n`), and prove the Tonelli bounds for the threshold-cut model on `T × ℝ`.
-/

open MeasureTheory MagCore

noncomputable section

namespace Results.MagnitudeContinuity

section LpHelpers

variable {T : Type*} [MeasurableSpace T] (ν : Measure T)

/-- The coercion of a finite sum in `Lp` is a.e. the pointwise finite sum. -/
theorem lp_coeFn_finsetSum {ι : Type*} (s : Finset ι) (F : ι → Lp ℝ 1 ν) :
    ⇑(∑ i ∈ s, F i) =ᵐ[ν] fun t => ∑ i ∈ s, F i t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 1 ν] with t ht
    simpa using ht
  | insert a s has ih =>
    rw [Finset.sum_insert has]
    filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with t h1 h2
    rw [Finset.sum_insert has]
    simp only [Pi.add_apply] at h1
    rw [h1, h2]

/-- The `L₁` norm of an element of `Lp ℝ 1 ν` as a lower integral. -/
theorem ofReal_norm_lp_eq_lintegral (F : Lp ℝ 1 ν) :
    ENNReal.ofReal ‖F‖ = ∫⁻ t, ENNReal.ofReal |F t| ∂ν := by
  rw [ofReal_norm, Lp.enorm_def, eLpNorm_one_eq_lintegral_enorm]
  simp_rw [Real.enorm_eq_ofReal_abs]

end LpHelpers

/-- Simultaneous measurable representatives with an integrable envelope of integral at most `n`. -/
theorem exists_envelope (U : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] {T : Type*} [MeasurableSpace T] (ν : Measure T) [SigmaFinite ν]
    (J : U →ₗᵢ[ℝ] Lp ℝ 1 ν) :
    ∃ (f : U → T → ℝ) (h : T → ℝ), (∀ x, Measurable (f x)) ∧ Measurable h ∧
      (∀ t, 0 ≤ h t) ∧
      ∫⁻ t, ENNReal.ofReal (h t) ∂ν ≤ ENNReal.ofReal (Module.finrank ℝ U) ∧
      (∀ x y t, |f x t - f y t| ≤ h t * dist x y) ∧
      (∀ x y, ENNReal.ofReal (dist x y) = ∫⁻ t, ENNReal.ofReal |f x t - f y t| ∂ν) := by
  obtain ⟨e, c, he1, hec, hcb⟩ := exists_auerbach U
  set g : Fin (Module.finrank ℝ U) → T → ℝ := fun i => ⇑(J (e i)) with hgdef
  have hg : ∀ i, Measurable (g i) := fun i => (Lp.stronglyMeasurable (J (e i))).measurable
  have hga : ∀ i, Measurable fun t => |g i t| := fun i => continuous_abs.measurable.comp (hg i)
  -- every `J u` is a.e. the finite combination of the representatives
  have hJ : ∀ u : U, ⇑(J u) =ᵐ[ν] fun t => ∑ i, c u i * g i t := by
    intro u
    have h1 : J u = ∑ i, c u i • J (e i) := by
      conv_lhs => rw [← hec u]
      rw [map_sum]
      simp only [map_smul]
    rw [h1]
    refine (lp_coeFn_finsetSum ν Finset.univ (fun i => c u i • J (e i))).trans ?_
    have h2 : ∀ᵐ t ∂ν, ∀ i, (c u i • J (e i) : Lp ℝ 1 ν) t = c u i * g i t := by
      rw [ae_all_iff]
      intro i
      filter_upwards [Lp.coeFn_smul (c u i) (J (e i))] with t ht
      rw [ht]
      simp [g]
    filter_upwards [h2] with t ht
    exact Finset.sum_congr rfl fun i _ => ht i
  refine ⟨fun x t => ∑ i, c x i * g i t, fun t => ∑ i, |g i t|, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact Finset.measurable_sum _ fun i _ => (hg i).const_mul _
  · exact Finset.measurable_sum _ fun i _ => hga i
  · intro t
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  · have hmi : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ U))),
        Measurable fun t => ENNReal.ofReal |g i t| := fun i _ =>
      ENNReal.measurable_ofReal.comp (hga i)
    calc ∫⁻ t, ENNReal.ofReal (∑ i, |g i t|) ∂ν
        = ∫⁻ t, ∑ i, ENNReal.ofReal |g i t| ∂ν := by
          refine lintegral_congr fun t => ?_
          exact ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _
      _ = ∑ i, ∫⁻ t, ENNReal.ofReal |g i t| ∂ν := lintegral_finsetSum _ hmi
      _ = ∑ i, ENNReal.ofReal ‖e i‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← LinearIsometry.norm_map J (e i), ofReal_norm_lp_eq_lintegral]
      _ ≤ ∑ _i : Fin (Module.finrank ℝ U), ENNReal.ofReal 1 :=
          Finset.sum_le_sum fun i _ => ENNReal.ofReal_le_ofReal (he1 i)
      _ = ENNReal.ofReal (Module.finrank ℝ U) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_one, mul_one, ENNReal.ofReal_natCast]
  · intro x y t
    have hdiff : (∑ i, c x i * g i t) - ∑ i, c y i * g i t = ∑ i, c (x - y) i * g i t := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sub, Pi.sub_apply, sub_mul]
    show |(∑ i, c x i * g i t) - ∑ i, c y i * g i t| ≤ (∑ i, |g i t|) * dist x y
    rw [hdiff, dist_eq_norm, mul_comm, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hcb _ i) (abs_nonneg _)
  · intro x y
    have hdiff : ∀ t, (∑ i, c x i * g i t) - ∑ i, c y i * g i t = ∑ i, c (x - y) i * g i t := by
      intro t
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sub, Pi.sub_apply, sub_mul]
    have hae : ∀ᵐ t ∂ν, ENNReal.ofReal |J (x - y) t| =
        ENNReal.ofReal |(∑ i, c x i * g i t) - ∑ i, c y i * g i t| := by
      filter_upwards [hJ (x - y)] with t ht
      rw [ht, hdiff]
    rw [dist_eq_norm, ← LinearIsometry.norm_map J (x - y), ofReal_norm_lp_eq_lintegral]
    exact lintegral_congr_ae hae

section ThresholdCuts

variable {S : Type*} {T : Type*} [MeasurableSpace T] (ν : Measure T) [SigmaFinite ν]

/-- The bit of the threshold cut `ω = (t, s)` at the point `x`. -/
def bit (f : S → T → ℝ) (x : S) (ω : T × ℝ) : Bool := decide (ω.2 < f x ω.1)

theorem measurable_bit {f : S → T → ℝ} (hf : ∀ x, Measurable (f x)) (x : S) :
    Measurable (bit f x) := by
  refine measurable_to_bool ?_
  have hm : MeasurableSet {ω : T × ℝ | ω.2 < f x ω.1} :=
    measurableSet_lt measurable_snd ((hf x).comp measurable_fst)
  convert hm using 1
  ext ω
  simp [bit]

omit [SigmaFinite ν] in
/-- The cut metric of the threshold cuts is the `L₁` distance. -/
theorem measure_bit_ne {f : S → T → ℝ} (hf : ∀ x, Measurable (f x)) (x y : S) :
    (ν.prod volume) {ω | bit f x ω ≠ bit f y ω} = ∫⁻ t, ENNReal.ofReal |f x t - f y t| ∂ν := by
  have hmeas : MeasurableSet {ω : T × ℝ | bit f x ω ≠ bit f y ω} :=
    (measurableSet_eq_fun (measurable_bit hf x) (measurable_bit hf y)).compl
  rw [Measure.prod_apply hmeas]
  refine lintegral_congr fun t => ?_
  have hsec : Prod.mk t ⁻¹' {ω : T × ℝ | bit f x ω ≠ bit f y ω} =
      Set.Ico (min (f x t) (f y t)) (max (f x t) (f y t)) := by
    ext s
    simp only [Set.mem_preimage, Set.mem_setOf_eq, bit, Set.mem_Ico, ne_eq, decide_eq_decide]
    rcases le_total (f x t) (f y t) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
      constructor
      · intro hne
        by_contra hcon
        apply hne
        constructor
        · intro h1; exact lt_of_lt_of_le h1 hle
        · intro h1
          by_contra h2
          exact hcon ⟨not_lt.1 h2, h1⟩
      · rintro ⟨h1, h2⟩ hiff
        exact absurd (hiff.2 h2) (not_lt.2 h1)
    · rw [min_eq_right hle, max_eq_left hle]
      constructor
      · intro hne
        by_contra hcon
        apply hne
        constructor
        · intro h1
          by_contra h2
          exact hcon ⟨not_lt.1 h2, h1⟩
        · intro h1; exact lt_of_lt_of_le h1 hle
      · rintro ⟨h1, h2⟩ hiff
        exact absurd (hiff.1 h2) (not_lt.2 h1)
  rw [hsec, Real.volume_Ico, max_sub_min_eq_abs']

theorem measurableSet_deletedStrip {f : S → T → ℝ} (hf : ∀ x, Measurable (f x))
    {h : T → ℝ} (hh : Measurable h) (F : Finset S) (r : ℝ) :
    MeasurableSet (deletedStrip f h (F : Set S) r) := by
  have heq : deletedStrip f h (F : Set S) r =
      ⋃ a ∈ F, {ω : T × ℝ | |ω.2 - f a ω.1| ≤ r * h ω.1} := by
    ext ω
    simp [deletedStrip]
  rw [heq]
  refine Finset.measurableSet_biUnion F fun a _ => ?_
  have hm : Measurable fun ω : T × ℝ => ω.2 - f a ω.1 :=
    measurable_snd.sub ((hf a).comp measurable_fst)
  exact measurableSet_le (continuous_abs.measurable.comp hm)
    ((hh.comp measurable_fst).const_mul r)

omit [SigmaFinite ν] in
/-- Tonelli: the deleted strips have measure at most `2 r m α`. -/
theorem measure_deletedStrip_le {f : S → T → ℝ} (hf : ∀ x, Measurable (f x))
    {h : T → ℝ} (hh : Measurable h) (F : Finset S) {r : ℝ} (hr : 0 ≤ r)
    {α : ℝ} (hα : ∫⁻ t, ENNReal.ofReal (h t) ∂ν ≤ ENNReal.ofReal α) :
    (ν.prod volume) (deletedStrip f h (F : Set S) r) ≤
      ENNReal.ofReal (2 * r * F.card * α) := by
  have heq : deletedStrip f h (F : Set S) r =
      ⋃ a ∈ F, {ω : T × ℝ | |ω.2 - f a ω.1| ≤ r * h ω.1} := by
    ext ω
    simp [deletedStrip]
  have hterm : ∀ a ∈ F, (ν.prod volume) {ω : T × ℝ | |ω.2 - f a ω.1| ≤ r * h ω.1} ≤
      ENNReal.ofReal (2 * r * α) := by
    intro a _
    have hm : Measurable fun ω : T × ℝ => ω.2 - f a ω.1 :=
      measurable_snd.sub ((hf a).comp measurable_fst)
    have hmeas : MeasurableSet {ω : T × ℝ | |ω.2 - f a ω.1| ≤ r * h ω.1} :=
      measurableSet_le (continuous_abs.measurable.comp hm)
        ((hh.comp measurable_fst).const_mul r)
    rw [Measure.prod_apply hmeas]
    have hsec : ∀ t, volume (Prod.mk t ⁻¹' {ω : T × ℝ | |ω.2 - f a ω.1| ≤ r * h ω.1}) =
        ENNReal.ofReal 2 * ENNReal.ofReal r * ENNReal.ofReal (h t) := by
      intro t
      have hI : Prod.mk t ⁻¹' {ω : T × ℝ | |ω.2 - f a ω.1| ≤ r * h ω.1} =
          Set.Icc (f a t - r * h t) (f a t + r * h t) := by
        ext s
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc, abs_le]
        constructor
        · rintro ⟨h1, h2⟩; constructor <;> linarith
        · rintro ⟨h1, h2⟩; constructor <;> linarith
      rw [hI, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hr)]
      congr 1
      ring
    simp_rw [hsec]
    have hmh : Measurable fun t => ENNReal.ofReal (h t) := ENNReal.measurable_ofReal.comp hh
    rw [lintegral_const_mul _ hmh]
    calc ENNReal.ofReal 2 * ENNReal.ofReal r * ∫⁻ t, ENNReal.ofReal (h t) ∂ν
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal r * ENNReal.ofReal α := by gcongr
      _ = ENNReal.ofReal (2 * r * α) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  rw [heq]
  calc (ν.prod volume) (⋃ a ∈ F, {ω : T × ℝ | |ω.2 - f a ω.1| ≤ r * h ω.1})
      ≤ ∑ a ∈ F, (ν.prod volume) {ω : T × ℝ | |ω.2 - f a ω.1| ≤ r * h ω.1} :=
        measure_biUnion_finset_le F _
    _ ≤ ∑ a ∈ F, ENNReal.ofReal (2 * r * α) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (2 * r * F.card * α) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [show 2 * r * (F.card : ℝ) * α = (F.card : ℝ) * (2 * r * α) by ring,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end ThresholdCuts

end Results.MagnitudeContinuity
