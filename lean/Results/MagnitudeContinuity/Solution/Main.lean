import Results.MagnitudeContinuity.Solution.Assembly
import Results.MagnitudeContinuity.Solution.PosDefL1
import Results.MagnitudeContinuity.Solution.Sanity

/-!
# Theorem 1.1: proofs of the Challenge statements

Proofs of `main_of_embedding`, `main`, `main_tendsto` and `main_of_L1`, with statements identical to
`Challenge.lean`, followed by `main_of_L1_instance` and `magnitude_singleton_real`, which show that the
hypotheses of the statement are satisfiable (non-vacuity) and that the definitions give the expected value
`Mag {0} = 1` in the one-point case.
-/

open MeasureTheory Metric Filter Topology
open scoped ENNReal

universe u

namespace Results.MagnitudeContinuity

/-- **Theorem 1.1 given the embedding** (the content of the paper's proof once the published
embedding theorem has been applied): the same estimate for a finite-dimensional positive definite
normed space `U` together with a linear isometry into `L₁[0,1]`. -/
theorem main_of_embedding
    (U : Type u) [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    (hPD : IsPositiveDefinite U) (hn : 1 ≤ Module.finrank ℝ U)
    (J : U →ₗᵢ[ℝ] Lp ℝ 1 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (F : Finset U) (hF : F.Nonempty) (lam : ℝ) (hlam : IsLeastEigenvalue (simMatrix F) lam)
    (X : Set U) (hXc : IsCompact X) (hXne : X.Nonempty)
    (r : ℝ) (hr : r = hausdorffDist X (F : Set U))
    (hr1 : r ≤ lam / (2 * (Module.finrank ℝ U : ℝ) * (F.card : ℝ) ^ 2))
    (hr2 : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → 2 * r < dist a b) :
    magnitude X ≠ ⊤ ∧
      -(2 * (F.card : ℝ) ^ 2 / lam ^ 2) * r ≤ (magnitude X).toReal - magnitudeFinset F ∧
      (magnitude X).toReal - magnitudeFinset F ≤
        2 * (Module.finrank ℝ U : ℝ) * (F.card : ℝ) ^ 3 / lam ^ 2 * r := by
  classical
  have hm : (0 : ℝ) < F.card := Nat.cast_pos.2 hF.card_pos
  have hn' : (0 : ℝ) < (Module.finrank ℝ U : ℝ) := by exact_mod_cast hn
  obtain ⟨f, h, hf, hh, h0, hα, henv, hdist⟩ :=
    exists_envelope U (volume.restrict (Set.Icc (0 : ℝ) 1)) J
  have hFpd := hPD F hF
  obtain ⟨hlam0, hcoer⟩ := coercive_of_isLeastEigenvalue hF hFpd hlam
  have hr0 : 0 ≤ r := hr ▸ hausdorffDist_nonneg
  obtain ⟨hlab1, hlab2⟩ := exists_labels hXc hXne hF
  rw [← hr] at hlab1 hlab2
  have hsmall : (F.card : ℝ) * ((Module.finrank ℝ U : ℝ) * F.card * r) ≤ lam / 2 :=
    MagCore.small_radius hn' hm hr1
  have hup : magnitude X ≤
      ENNReal.ofReal (magnitudeFinset F +
        2 * (Module.finrank ℝ U : ℝ) * (F.card : ℝ) ^ 3 / lam ^ 2 * r) := by
    unfold magnitude
    refine iSup_le fun A => iSup_le fun hA => iSup_le fun hAX => ENNReal.ofReal_le_ofReal ?_
    exact finite_upper_bound hPD (volume.restrict (Set.Icc (0 : ℝ) 1)) f h hf hh h0
      (α := (Module.finrank ℝ U : ℝ)) (Nat.cast_nonneg _) hα henv hdist F hF hlam0 hcoer hr0
      hsmall A hA (fun y hy => hlab1 y (hAX hy))
  have hfin : magnitude X ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup
  obtain ⟨wF, hwF, hmF⟩ := exists_weighting_of_posDef F hFpd
  have hMF : 0 ≤ magnitudeFinset F := by
    rw [← hmF]
    exact MagCore.mass_weighting_nonneg (qPositive_simKernel_of_posDef hFpd) hwF
  have hC : 0 ≤ 2 * (Module.finrank ℝ U : ℝ) * (F.card : ℝ) ^ 3 / lam ^ 2 * r := by positivity
  have hupper : (magnitude X).toReal ≤
      magnitudeFinset F + 2 * (Module.finrank ℝ U : ℝ) * (F.card : ℝ) ^ 3 / lam ^ 2 * r :=
    ENNReal.toReal_le_of_le_ofReal (by linarith) hup
  choose e heX hed using fun a : F => hlab2 (a : U) a.2
  have hinj : Function.Injective e := by
    intro a b hab
    by_contra hne
    have hne' : (a : U) ≠ (b : U) := fun h' => hne (Subtype.ext h')
    have h1 := hr2 a a.2 b b.2 hne'
    have h2 : dist (a : U) (b : U) ≤ dist (a : U) (e a) + dist (e a) (b : U) := dist_triangle _ _ _
    have h3 : dist (e a) (b : U) = dist (e b) (b : U) := by rw [hab]
    rw [dist_comm (a : U) (e a)] at h2
    linarith [hed a, hed b]
  obtain ⟨A, hAne, hAe, hlow⟩ := finite_lower_bound hPD F hF hlam0 hcoer hr0 e hinj hed
  have hAX : (A : Set U) ⊆ X := by
    intro x hx
    obtain ⟨a, rfl⟩ := hAe x hx
    exact heX a
  have hle : ENNReal.ofReal (magnitudeFinset A) ≤ magnitude X :=
    le_iSup_of_le A (le_iSup_of_le hAne (le_iSup_of_le hAX le_rfl))
  have hlower : magnitudeFinset A ≤ (magnitude X).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfin).1 hle
  refine ⟨hfin, ?_, by linarith⟩
  have e1 : -(2 * (F.card : ℝ) ^ 2 / lam ^ 2) * r = -(2 * (F.card : ℝ) ^ 2 / lam ^ 2 * r) := by
    ring
  rw [e1]
  linarith

/-- **Theorem 1.1** (quantitative estimate), assuming the published embedding theorem. -/
theorem main (hMeckes : MeckesEmbedding.{u})
    (U : Type u) [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    (hPD : IsPositiveDefinite U) (hn : 1 ≤ Module.finrank ℝ U)
    (F : Finset U) (hF : F.Nonempty) (lam : ℝ) (hlam : IsLeastEigenvalue (simMatrix F) lam)
    (X : Set U) (hXc : IsCompact X) (hXne : X.Nonempty)
    (r : ℝ) (hr : r = hausdorffDist X (F : Set U))
    (hr1 : r ≤ lam / (2 * (Module.finrank ℝ U : ℝ) * (F.card : ℝ) ^ 2))
    (hr2 : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → 2 * r < dist a b) :
    magnitude X ≠ ⊤ ∧
      -(2 * (F.card : ℝ) ^ 2 / lam ^ 2) * r ≤ (magnitude X).toReal - magnitudeFinset F ∧
      (magnitude X).toReal - magnitudeFinset F ≤
        2 * (Module.finrank ℝ U : ℝ) * (F.card : ℝ) ^ 3 / lam ^ 2 * r := by
  obtain ⟨J⟩ := hMeckes U hPD
  exact main_of_embedding U hPD hn J F hF lam hlam X hXc hXne r hr hr1 hr2

/-- **Theorem 1.1**, convergence statement. -/
theorem main_tendsto (hMeckes : MeckesEmbedding.{u})
    (U : Type u) [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    (hPD : IsPositiveDefinite U) (hn : 1 ≤ Module.finrank ℝ U)
    (F : Finset U) (hF : F.Nonempty)
    (X : ℕ → Set U) (hXc : ∀ k, IsCompact (X k)) (hXne : ∀ k, (X k).Nonempty)
    (hconv : Tendsto (fun k => hausdorffDist (X k) (F : Set U)) atTop (𝓝 0)) :
    Tendsto (fun k => magnitude (X k)) atTop (𝓝 (ENNReal.ofReal (magnitudeFinset F))) := by
  classical
  haveI : Nonempty F := hF.to_subtype
  have hFpd := hPD F hF
  obtain ⟨lam, hlam⟩ := exists_isLeastEigenvalue (simMatrix F) hFpd.isHermitian
  obtain ⟨hlam0, -⟩ := coercive_of_isLeastEigenvalue hF hFpd hlam
  have hm : (0 : ℝ) < F.card := Nat.cast_pos.2 hF.card_pos
  have hn' : (0 : ℝ) < (Module.finrank ℝ U : ℝ) := by exact_mod_cast hn
  set rk : ℕ → ℝ := fun k => hausdorffDist (X k) (F : Set U) with hrk
  have hev1 : ∀ᶠ k in atTop,
      rk k ≤ lam / (2 * (Module.finrank ℝ U : ℝ) * (F.card : ℝ) ^ 2) := by
    have hpos : 0 < lam / (2 * (Module.finrank ℝ U : ℝ) * (F.card : ℝ) ^ 2) := by positivity
    exact (hconv.eventually (gt_mem_nhds hpos)).mono fun k hk => hk.le
  have hev2 : ∀ᶠ k in atTop, ∀ a ∈ F, ∀ b ∈ F, a ≠ b → 2 * rk k < dist a b := by
    refine (Filter.eventually_all_finset F).2 fun a ha => ?_
    refine (Filter.eventually_all_finset F).2 fun b hb => ?_
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall fun k h' => absurd hab h'
    · have hpos : 0 < dist a b := dist_pos.2 hab
      have h2 : Tendsto (fun k => 2 * rk k) atTop (𝓝 (2 * 0)) := hconv.const_mul 2
      rw [mul_zero] at h2
      exact (h2.eventually (gt_mem_nhds hpos)).mono fun k hk _ => hk
  have hmain : ∀ᶠ k in atTop, magnitude (X k) ≠ ⊤ ∧
      magnitudeFinset F - 2 * (F.card : ℝ) ^ 2 / lam ^ 2 * rk k ≤ (magnitude (X k)).toReal ∧
      (magnitude (X k)).toReal ≤ magnitudeFinset F +
        2 * (Module.finrank ℝ U : ℝ) * (F.card : ℝ) ^ 3 / lam ^ 2 * rk k := by
    filter_upwards [hev1, hev2] with k h1 h2
    obtain ⟨hfin, hlo, hhi⟩ := main hMeckes U hPD hn F hF lam hlam (X k) (hXc k) (hXne k)
      (rk k) rfl h1 h2
    refine ⟨hfin, ?_, ?_⟩
    · linarith
    · linarith
  have hlow : Tendsto (fun k => magnitudeFinset F - 2 * (F.card : ℝ) ^ 2 / lam ^ 2 * rk k)
      atTop (𝓝 (magnitudeFinset F)) := by
    have := (hconv.const_mul (2 * (F.card : ℝ) ^ 2 / lam ^ 2)).const_sub (magnitudeFinset F)
    simpa using this
  have hhigh : Tendsto (fun k => magnitudeFinset F +
      2 * (Module.finrank ℝ U : ℝ) * (F.card : ℝ) ^ 3 / lam ^ 2 * rk k)
      atTop (𝓝 (magnitudeFinset F)) := by
    have := (hconv.const_mul (2 * (Module.finrank ℝ U : ℝ) * (F.card : ℝ) ^ 3 / lam ^ 2)).const_add
      (magnitudeFinset F)
    simpa using this
  have hreal : Tendsto (fun k => (magnitude (X k)).toReal) atTop (𝓝 (magnitudeFinset F)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
      (hmain.mono fun k hk => hk.2.1) (hmain.mono fun k hk => hk.2.2)
  have hofReal : Tendsto (fun k => ENNReal.ofReal ((magnitude (X k)).toReal)) atTop
      (𝓝 (ENNReal.ofReal (magnitudeFinset F))) := ENNReal.tendsto_ofReal hreal
  refine hofReal.congr' ?_
  filter_upwards [hmain] with k hk
  exact ENNReal.ofReal_toReal hk.1

/-- **Theorem 1.1 for a finite-dimensional subspace of `L₁`** (the formulation of the abstract):
no positive definiteness hypothesis and no external theorem is needed, because subsets of `L₁` are
positive definite. -/
theorem main_of_L1
    (U : Type u) [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    (hn : 1 ≤ Module.finrank ℝ U)
    (J : U →ₗᵢ[ℝ] Lp ℝ 1 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (F : Finset U) (hF : F.Nonempty) (lam : ℝ) (hlam : IsLeastEigenvalue (simMatrix F) lam)
    (X : Set U) (hXc : IsCompact X) (hXne : X.Nonempty)
    (r : ℝ) (hr : r = hausdorffDist X (F : Set U))
    (hr1 : r ≤ lam / (2 * (Module.finrank ℝ U : ℝ) * (F.card : ℝ) ^ 2))
    (hr2 : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → 2 * r < dist a b) :
    magnitude X ≠ ⊤ ∧
      -(2 * (F.card : ℝ) ^ 2 / lam ^ 2) * r ≤ (magnitude X).toReal - magnitudeFinset F ∧
      (magnitude X).toReal - magnitudeFinset F ≤
        2 * (Module.finrank ℝ U : ℝ) * (F.card : ℝ) ^ 3 / lam ^ 2 * r := by
  have hPD : IsPositiveDefinite U :=
    isPositiveDefinite_of_isometry_Lp (volume.restrict (Set.Icc (0 : ℝ) 1)) J J.isometry
  exact main_of_embedding U hPD hn J F hF lam hlam X hXc hXne r hr hr1 hr2

/-- **The hypotheses of Theorem 1.1 are satisfiable.**  For `U = ℝ` (one-dimensional, embedded in
`L₁[0,1]` by constants), `F = X = {0}`, `r = 0` and `lam = 1` (the least eigenvalue of the `1 × 1`
similarity matrix of a singleton), every hypothesis of `main_of_L1` holds, so the statement is not
vacuous; the conclusion is the estimate with `Mag {0} = 1`. -/
theorem main_of_L1_instance :
    magnitude ({0} : Set ℝ) ≠ ⊤ ∧
      -(2 * (({0} : Finset ℝ).card : ℝ) ^ 2 / (1 : ℝ) ^ 2) * 0 ≤
        (magnitude ({0} : Set ℝ)).toReal - magnitudeFinset ({0} : Finset ℝ) ∧
      (magnitude ({0} : Set ℝ)).toReal - magnitudeFinset ({0} : Finset ℝ) ≤
        2 * (Module.finrank ℝ ℝ : ℝ) * (({0} : Finset ℝ).card : ℝ) ^ 3 / (1 : ℝ) ^ 2 * 0 :=
  main_of_L1 ℝ (by simp) constIsometry ({0} : Finset ℝ) (Finset.singleton_nonempty 0) 1
    (isLeastEigenvalue_simMatrix_singleton 0) ({0} : Set ℝ) isCompact_singleton
    (Set.singleton_nonempty 0) 0 (hausdorffDist_finset_singleton 0).symm
    (by simp)
    (fun a ha b hb hab => absurd ((Finset.mem_singleton.mp ha).trans
      (Finset.mem_singleton.mp hb).symm) hab)

/-- In the instance above the two sides are `Mag {0} = 1`: the magnitude of the one-point space is
`1`, both as a finite set and as a supremum. -/
theorem magnitude_singleton_real :
    magnitude ({0} : Set ℝ) = 1 := by
  have h := magnitude_coe_finset isPositiveDefinite_real (A := ({0} : Finset ℝ))
    (Finset.singleton_nonempty 0)
  rw [Finset.coe_singleton, magnitudeFinset_singleton] at h
  simpa using h

end Results.MagnitudeContinuity
