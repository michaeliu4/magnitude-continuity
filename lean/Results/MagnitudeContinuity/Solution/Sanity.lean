import Results.MagnitudeContinuity.Defs
import Results.MagnitudeContinuity.Solution.Bridge
import Results.MagnitudeContinuity.Solution.PosDefL1
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Sanity lemmas for the definitions of `Defs.lean`

* `magnitude_coe_finset` : the supremum magnitude of a finite set agrees with its finite magnitude
  (for a positive definite ambient space);
* `constIsometry` : the isometric embedding `ℝ → L₁[0,1]`, `c ↦ const c`;
* `isLeastEigenvalue_simMatrix_singleton` : the least eigenvalue of the `1 × 1` similarity matrix
  of a singleton is `1`;
* `isPositiveDefinite_real` : `ℝ` is positive definite;
* `hausdorffDist_finset_singleton` : a singleton has Hausdorff distance `0` from itself, read as a
  `Finset`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Results.MagnitudeContinuity

/-! ## (S1) Monotonicity of the finite magnitude and `magnitude_coe_finset` -/

section Mono

variable {U : Type*} [MetricSpace U]

/-- The inclusion `B → A` for `B ⊆ A`. -/
def inclB {A B : Finset U} (hBA : B ⊆ A) (k : B) : A := ⟨k.1, hBA k.2⟩

open scoped Classical in
/-- The zero extension of a vector on `B` to a vector on `A ⊇ B`. -/
def zeroExt {A B : Finset U} (x : B → ℝ) : A → ℝ :=
  fun a => if h : (a : U) ∈ B then x ⟨a, h⟩ else 0

omit [MetricSpace U] in
lemma inclB_injective {A B : Finset U} (hBA : B ⊆ A) : Function.Injective (inclB hBA) := by
  intro k l h
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

omit [MetricSpace U] in
lemma zeroExt_inclB {A B : Finset U} (hBA : B ⊆ A) (x : B → ℝ) (k : B) :
    zeroExt (A := A) x (inclB hBA k) = x k := by
  simp [zeroExt, inclB]

omit [MetricSpace U] in
lemma zeroExt_of_not_mem_range {A B : Finset U} (hBA : B ⊆ A) (x : B → ℝ) (a : A)
    (ha : a ∉ Set.range (inclB hBA)) : zeroExt (A := A) x a = 0 := by
  unfold zeroExt
  by_cases h : (a : U) ∈ B
  · exact absurd ⟨⟨a, h⟩, Subtype.ext rfl⟩ ha
  · simp [h]

omit [MetricSpace U] in
lemma mass_zeroExt {A B : Finset U} (hBA : B ⊆ A) (x : B → ℝ) :
    MagCore.mass (zeroExt (A := A) x) = MagCore.mass x := by
  unfold MagCore.mass
  exact (Fintype.sum_of_injective (inclB hBA) (inclB_injective hBA) x _
    (fun a ha => zeroExt_of_not_mem_range hBA x a ha)
    (fun k => (zeroExt_inclB hBA x k).symm)).symm

lemma quadratic_zeroExt {A B : Finset U} (hBA : B ⊆ A) (x : B → ℝ) :
    MagCore.quadratic (simKernel A) (zeroExt (A := A) x) =
      MagCore.quadratic (simKernel B) x := by
  unfold MagCore.quadratic MagCore.bilinear
  symm
  refine Fintype.sum_of_injective (inclB hBA) (inclB_injective hBA) _ _ ?_ ?_
  · intro a ha
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [zeroExt_of_not_mem_range hBA x a ha]
    ring
  · intro k
    refine Fintype.sum_of_injective (inclB hBA) (inclB_injective hBA) _ _ ?_ ?_
    · intro j hj
      rw [zeroExt_of_not_mem_range hBA x j hj]
      ring
    · intro l
      rw [zeroExt_inclB hBA x k, zeroExt_inclB hBA x l]
      rfl

/-- Under positive definiteness, the finite magnitude is monotone. -/
theorem magnitudeFinset_mono {A B : Finset U} (hPD : IsPositiveDefinite U) (hB : B.Nonempty)
    (hBA : B ⊆ A) : magnitudeFinset B ≤ magnitudeFinset A := by
  have hAne : A.Nonempty := hB.mono hBA
  obtain ⟨wA, hwA, hmA⟩ := exists_weighting_of_posDef A (hPD A hAne)
  obtain ⟨wB, hwB, hmB⟩ := exists_weighting_of_posDef B (hPD B hB)
  have h1 := MagCore.energy_le_weighting (simKernel_symmetric A)
    (qPositive_simKernel_of_posDef (hPD A hAne)) hwA (zeroExt (A := A) wB)
  have h2 : MagCore.energy (simKernel A) (zeroExt (A := A) wB) =
      MagCore.energy (simKernel B) wB := by
    unfold MagCore.energy
    rw [mass_zeroExt hBA, quadratic_zeroExt hBA]
  rw [h2, MagCore.energy_at_weighting hwB, hmA, hmB] at h1
  exact h1

/-- The compact/sup magnitude of a finite set agrees with its finite magnitude. -/
theorem magnitude_coe_finset (hPD : IsPositiveDefinite U) {A : Finset U} (hA : A.Nonempty) :
    magnitude (A : Set U) = ENNReal.ofReal (magnitudeFinset A) := by
  unfold magnitude
  apply le_antisymm
  · refine iSup_le (fun B => iSup_le (fun hB => iSup_le (fun hBA => ?_)))
    exact ENNReal.ofReal_le_ofReal
      (magnitudeFinset_mono hPD hB (Finset.coe_subset.mp hBA))
  · exact le_iSup_of_le A (le_iSup_of_le hA (le_iSup_of_le (Set.Subset.refl _) le_rfl))

end Mono

/-! ## (S2) The constant-function isometry `ℝ → L₁[0,1]` -/

/-- The linear isometry `ℝ →ₗᵢ[ℝ] L₁[0,1]` sending `c` to the constant function `c`. -/
def constIsometry : ℝ →ₗᵢ[ℝ] Lp ℝ 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) where
  toLinearMap := Lp.constₗ 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) ℝ
  norm_map' := fun c => by
    have h := Lp.norm_const' (p := 1) (volume.restrict (Set.Icc (0 : ℝ) 1)) c one_ne_zero
      ENNReal.one_ne_top
    simpa [Measure.real, Real.volume_Icc] using h

/-! ## (S3) The least eigenvalue of the `1 × 1` similarity matrix of a singleton -/

section LeastEig

/-- Eigenvalues of `toEuclideanLin Z` are the real `μ` with a nonzero `v` and `Z v = μ v`. -/
theorem sanity_hasEigenvalue_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (Z : Matrix ι ι ℝ)
    (μ : ℝ) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin Z) μ ↔
      ∃ v : ι → ℝ, v ≠ 0 ∧ Z.mulVec v = μ • v := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    refine ⟨WithLp.ofLp x, ?_, ?_⟩
    · intro h0
      apply hx.2
      exact (WithLp.ofLp_injective 2) (by simpa using h0)
    · have := Module.End.mem_eigenspace_iff.1 hx.1
      have h2 := congrArg WithLp.ofLp this
      simpa using h2
  · rintro ⟨v, hv, hZ⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := WithLp.toLp 2 v) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      apply WithLp.ofLp_injective 2
      simpa using hZ
    · intro h0
      apply hv
      simpa using congrArg WithLp.ofLp h0

/-- Criterion: an eigenvector together with a lower bound for all real eigenvalues. -/
theorem sanity_isLeastEigenvalue_of {ι : Type*} [Fintype ι] (Z : Matrix ι ι ℝ) (lam : ℝ)
    (v : ι → ℝ) (hv : v ≠ 0) (hZv : Z.mulVec v = lam • v)
    (hlow : ∀ (μ : ℝ) (w : ι → ℝ), w ≠ 0 → Z.mulVec w = μ • w → lam ≤ μ) :
    IsLeastEigenvalue Z lam := by
  classical
  refine ⟨(sanity_hasEigenvalue_iff Z lam).2 ⟨v, hv, hZv⟩, fun μ hμ => ?_⟩
  obtain ⟨w, hw, hZw⟩ := (sanity_hasEigenvalue_iff Z μ).1 hμ
  exact hlow μ w hw hZw

theorem sanity_exists_ne_zero {ι : Type*} (w : ι → ℝ) (hw : w ≠ 0) : ∃ i, w i ≠ 0 := by
  by_contra h
  push Not at h
  exact hw (funext h)

/-- The similarity matrix of a singleton is the `1 × 1` identity. -/
theorem simMatrix_singleton_mulVec {U : Type*} [MetricSpace U] (a : U)
    (v : ({a} : Finset U) → ℝ) : (simMatrix ({a} : Finset U)).mulVec v = v := by
  ext i
  have hsub : ∀ j : ({a} : Finset U), j = i := fun j =>
    Subtype.ext ((Finset.mem_singleton.mp j.2).trans (Finset.mem_singleton.mp i.2).symm)
  have hs : ∑ j : ({a} : Finset U), simMatrix ({a} : Finset U) i j * v j =
      simMatrix ({a} : Finset U) i i * v i :=
    Fintype.sum_eq_single i (fun j hj => absurd (hsub j) hj)
  simp only [Matrix.mulVec, dotProduct]
  rw [hs]
  simp [simMatrix]

theorem isLeastEigenvalue_simMatrix_singleton {U : Type*} [MetricSpace U] (a : U) :
    IsLeastEigenvalue (simMatrix ({a} : Finset U)) 1 := by
  refine sanity_isLeastEigenvalue_of _ 1 (fun _ => 1) ?_ ?_ ?_
  · intro h
    have := congrFun h ⟨a, Finset.mem_singleton_self a⟩
    simp at this
  · rw [simMatrix_singleton_mulVec]
    ext i
    simp
  · intro μ w hw hZ
    rw [simMatrix_singleton_mulVec] at hZ
    obtain ⟨i, hi⟩ := sanity_exists_ne_zero w hw
    have := congrFun hZ i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have h2 : (1 : ℝ) * w i = μ * w i := by simpa using this
    exact le_of_eq (mul_right_cancel₀ hi h2)

end LeastEig

/-- The magnitude of a one-point set is `1`: `Z = (1)`, so `Mag = 1ᵀ Z⁻¹ 1 = 1`. -/
theorem magnitudeFinset_singleton {U : Type*} [MetricSpace U] (a : U) :
    magnitudeFinset ({a} : Finset U) = 1 := by
  classical
  have hZ : simMatrix ({a} : Finset U) = 1 := by
    ext i j
    have hij : i = j := Subtype.ext ((Finset.mem_singleton.mp i.2).trans
      (Finset.mem_singleton.mp j.2).symm)
    subst hij
    simp [simMatrix]
  unfold magnitudeFinset
  rw [hZ, inv_one]
  simp

/-! ## (S4) `ℝ` is positive definite -/

theorem isPositiveDefinite_real : IsPositiveDefinite ℝ :=
  isPositiveDefinite_of_isometry_Lp (volume.restrict (Set.Icc (0 : ℝ) 1))
    (fun c => constIsometry c) constIsometry.isometry

/-! ## (S5) Hausdorff distance of a singleton -/

theorem hausdorffDist_finset_singleton {U : Type*} (a : U) [MetricSpace U] :
    Metric.hausdorffDist (({a} : Set U)) ((({a} : Finset U) : Finset U) : Set U) = 0 := by
  rw [Finset.coe_singleton]
  exact Metric.hausdorffDist_self_zero

end Results.MagnitudeContinuity
