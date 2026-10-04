import Results.MagnitudeContinuity.Defs
import Results.MagnitudeContinuity.Solution.Core.UpperBound
import Results.MagnitudeContinuity.Solution.Core.Constants
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Bridge from Mathlib's matrix API to the weighting/quadratic-form core

Module M1.  Turns `simMatrix`, `magnitudeFinset`, `IsLeastEigenvalue`, `hausdorffDist` into the
statements about plain kernels and weightings used in `Solution.Core`.
-/

open MagCore

noncomputable section

namespace Results.MagnitudeContinuity

variable {U : Type*} [MetricSpace U]

/-- The similarity kernel of a finite set as a plain kernel (`MagCore.Kernel`). -/
def simKernel (A : Finset U) : MagCore.Kernel A := fun x y => Real.exp (-dist (x : U) (y : U))

section Spectral

variable {ι : Type*} [Fintype ι]

lemma inner_toEuclideanLin [DecidableEq ι] (Z : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    inner ℝ (Matrix.toEuclideanLin Z x) x = x.ofLp ⬝ᵥ Z.mulVec x.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]
  simp

lemma sq_norm_eq_sum (x : EuclideanSpace ℝ ι) : ‖x‖ ^ 2 = ∑ i, x.ofLp i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp

lemma quadratic_eq_dotProduct (Z : Matrix ι ι ℝ) (x : ι → ℝ) :
    MagCore.quadratic Z x = x ⬝ᵥ Z.mulVec x := by
  simp [MagCore.quadratic, MagCore.bilinear, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

lemma sum_sq_pos {v : ι → ℝ} (hv : v ≠ 0) : 0 < ∑ i, v i ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hi' : v i ≠ 0 := hi
  exact lt_of_lt_of_le (by positivity)
    (Finset.single_le_sum (f := fun i => v i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- An eigenvector `v` of `toEuclideanLin Z` for the eigenvalue `μ` satisfies `μ ‖v‖² = vᵀ Z v`. -/
lemma eigen_quadratic [DecidableEq ι] (Z : Matrix ι ι ℝ) {μ : ℝ}
    (h : Module.End.HasEigenvalue (Matrix.toEuclideanLin Z) μ) :
    ∃ v : ι → ℝ, v ≠ 0 ∧ μ * ∑ i, v i ^ 2 = v ⬝ᵥ Z.mulVec v := by
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  refine ⟨v.ofLp, fun h0 => hv.2 ?_, ?_⟩
  · ext i; simpa using congrFun h0 i
  · have h1 := inner_toEuclideanLin Z v
    rw [hv.apply_eq_smul, inner_smul_left, real_inner_self_eq_norm_sq, sq_norm_eq_sum] at h1
    simpa using h1

/-- The infimum of the Rayleigh quotient of a symmetric operator on a nontrivial finite-dimensional
real inner product space is an eigenvalue, and it is a lower bound for the Rayleigh quotient. -/
lemma exists_eigenvalue_le_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) :
    ∃ m : ℝ, Module.End.HasEigenvalue T m ∧ ∀ x : E, m * ‖x‖ ^ 2 ≤ inner ℝ (T x) x := by
  refine ⟨_, hT.hasEigenvalue_iInf_of_finiteDimensional, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; simp
  · have hbdd : BddBelow (Set.range fun y : { x : E // x ≠ 0 } =>
        RCLike.re (inner ℝ (T y) y) / ‖(y : E)‖ ^ 2) := by
      refine ⟨-‖LinearMap.toContinuousLinearMap T‖, ?_⟩
      rintro _ ⟨y, rfl⟩
      have := ContinuousLinearMap.rayleighQuotient_le_norm (LinearMap.toContinuousLinearMap T) y
      exact (abs_le.mp this).1
    have h1 := ciInf_le hbdd ⟨x, hx⟩
    have hpos : 0 < ‖x‖ ^ 2 := by positivity
    simp only [RCLike.re_to_real] at h1
    rw [le_div_iff₀ hpos] at h1
    exact h1

lemma exists_least_rayleigh [DecidableEq ι] [Nonempty ι] (Z : Matrix ι ι ℝ) (hZ : Z.IsHermitian) :
    ∃ m : ℝ, Module.End.HasEigenvalue (Matrix.toEuclideanLin Z) m ∧
      ∀ x : ι → ℝ, m * ∑ i, x i ^ 2 ≤ x ⬝ᵥ Z.mulVec x := by
  have hT : (Matrix.toEuclideanLin Z).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hZ
  obtain ⟨m, hm, hmx⟩ := exists_eigenvalue_le_inner hT
  refine ⟨m, hm, fun x => ?_⟩
  have h := hmx (WithLp.toLp 2 x)
  rw [inner_toEuclideanLin, sq_norm_eq_sum] at h
  simpa using h

/-- If `lam` is below every eigenvalue then `lam ‖x‖² ≤ xᵀ Z x` for all `x`. -/
lemma rayleigh_ge [DecidableEq ι] [Nonempty ι] (Z : Matrix ι ι ℝ) (hZ : Z.IsHermitian) {lam : ℝ}
    (hlam : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toEuclideanLin Z) μ → lam ≤ μ)
    (x : ι → ℝ) : lam * ∑ i, x i ^ 2 ≤ x ⬝ᵥ Z.mulVec x := by
  obtain ⟨m, hm, hmx⟩ := exists_least_rayleigh Z hZ
  have h1 := hlam m hm
  have h2 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  exact (mul_le_mul_of_nonneg_right h1 h2).trans (hmx x)

lemma exists_least_eigenvalue_aux [DecidableEq ι] [Nonempty ι] (Z : Matrix ι ι ℝ)
    (hZ : Z.IsHermitian) :
    ∃ lam : ℝ, Module.End.HasEigenvalue (Matrix.toEuclideanLin Z) lam ∧
      ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toEuclideanLin Z) μ → lam ≤ μ := by
  obtain ⟨m, hm, hmx⟩ := exists_least_rayleigh Z hZ
  refine ⟨m, hm, fun μ hμ => ?_⟩
  obtain ⟨v, hv0, hv⟩ := eigen_quadratic Z hμ
  have hpos := sum_sq_pos hv0
  have := hmx v
  rw [← hv] at this
  exact le_of_mul_le_mul_right this hpos

end Spectral

theorem simKernel_symmetric (A : Finset U) : MagCore.symmetric (simKernel A) := by
  intro x y
  simp only [simKernel, dist_comm (x : U) (y : U)]

/-- A positive definite similarity matrix has a weighting whose mass is the magnitude. -/
theorem exists_weighting_of_posDef (A : Finset U) (hA : (simMatrix A).PosDef) :
    ∃ w : A → ℝ, MagCore.weighting (simKernel A) w ∧ MagCore.mass w = magnitudeFinset A := by
  classical
  have hdet : IsUnit (simMatrix A).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hmul : simMatrix A * (simMatrix A)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  refine ⟨(simMatrix A)⁻¹.mulVec 1, ?_, ?_⟩
  · intro i
    have h1 : (simMatrix A).mulVec ((simMatrix A)⁻¹.mulVec 1) = 1 := by
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
    have h2 := congrFun h1 i
    simpa [Matrix.mulVec, dotProduct, simKernel, simMatrix] using h2
  · unfold MagCore.mass magnitudeFinset
    simp [Matrix.mulVec, dotProduct]

theorem qPositive_simKernel_of_posDef {A : Finset U} (hA : (simMatrix A).PosDef) :
    MagCore.qPositive (simKernel A) := by
  intro x
  by_cases hx : x = 0
  · subst hx
    exact (MagCore.quadratic_zero _).ge
  · have h := hA.dotProduct_mulVec_pos hx
    have e : MagCore.quadratic (simKernel A) x = x ⬝ᵥ (simMatrix A).mulVec x :=
      quadratic_eq_dotProduct (simMatrix A) x
    rw [e]
    simpa using h.le

/-- The least eigenvalue of a positive definite similarity matrix is positive and is a coercivity
constant for the quadratic form. -/
theorem coercive_of_isLeastEigenvalue {A : Finset U} (hne : A.Nonempty)
    (hA : (simMatrix A).PosDef) {lam : ℝ} (hlam : IsLeastEigenvalue (simMatrix A) lam) :
    0 < lam ∧ MagCore.coercive (simKernel A) lam := by
  -- the decidable-equality instance must be the one used in `IsLeastEigenvalue`
  letI : DecidableEq A := fun a b => Classical.propDecidable (a = b)
  haveI : Nonempty A := hne.to_subtype
  obtain ⟨h1, h2⟩ := hlam
  refine ⟨?_, fun x => ?_⟩
  · obtain ⟨v, hv0, hv⟩ := eigen_quadratic (simMatrix A) h1
    have hpos : 0 < v ⬝ᵥ (simMatrix A).mulVec v := by simpa using hA.dotProduct_mulVec_pos hv0
    rw [← hv] at hpos
    by_contra hle
    exact absurd hpos
      (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hle) (sum_sq_pos hv0).le))
  · have h := rayleigh_ge (simMatrix A) hA.isHermitian h2 x
    have e : MagCore.quadratic (simKernel A) x = x ⬝ᵥ (simMatrix A).mulVec x :=
      quadratic_eq_dotProduct (simMatrix A) x
    rw [e]
    exact h

/-- A symmetric real matrix over a nonempty index type has a least eigenvalue. -/
theorem exists_isLeastEigenvalue {ι : Type*} [Fintype ι] [Nonempty ι] (Z : Matrix ι ι ℝ)
    (hZ : Z.IsHermitian) : ∃ lam, IsLeastEigenvalue Z lam := by
  classical
  obtain ⟨lam, h⟩ := exists_least_eigenvalue_aux Z hZ
  exact ⟨lam, h⟩

set_option linter.unusedSectionVars false in
/-- An injective family `e : κ → U` is a bijective labelling of a finite subset: there are a finite set
`A ⊆ U` and a bijection `φ : κ ≃ A` with `(φ a : U) = e a`. -/
theorem exists_equiv_image {κ : Type*} [Fintype κ] (e : κ → U) (he : Function.Injective e) :
    ∃ (A : Finset U) (φ : κ ≃ A), ∀ a, (φ a : U) = e a := by
  classical
  let f : κ → (Finset.univ.image e) := fun a => ⟨e a, Finset.mem_image_of_mem e (Finset.mem_univ a)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact he (congrArg Subtype.val hab)
    · rintro ⟨u, hu⟩
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨a, rfl⟩
  exact ⟨Finset.univ.image e, Equiv.ofBijective f hf, fun a => rfl⟩

/-- Nearest-point labels coming from the Hausdorff distance of a compact set to a finite set. -/
theorem exists_labels {X : Set U} {F : Finset U} (hXc : IsCompact X) (hXne : X.Nonempty)
    (hF : F.Nonempty) :
    (∀ y ∈ X, ∃ a ∈ F, dist y a ≤ Metric.hausdorffDist X (F : Set U)) ∧
      (∀ a ∈ F, ∃ y ∈ X, dist y a ≤ Metric.hausdorffDist X (F : Set U)) := by
  have hFne : (F : Set U).Nonempty := Finset.coe_nonempty.mpr hF
  have hFc : IsCompact (F : Set U) := F.finite_toSet.isCompact
  have htop : Metric.hausdorffEDist X (F : Set U) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hXne hFne hXc.isBounded hFc.isBounded
  have htop' : Metric.hausdorffEDist (F : Set U) X ≠ ⊤ := by
    rwa [Metric.hausdorffEDist_comm]
  constructor
  · intro y hy
    obtain ⟨a, ha, hya⟩ := hFc.exists_infDist_eq_dist hFne y
    refine ⟨a, Finset.mem_coe.mp ha, ?_⟩
    rw [← hya]
    exact Metric.infDist_le_hausdorffDist_of_mem hy htop
  · intro a ha
    obtain ⟨y, hy, hay⟩ := hXc.exists_infDist_eq_dist hXne a
    refine ⟨y, hy, ?_⟩
    rw [dist_comm, ← hay, Metric.hausdorffDist_comm]
    exact Metric.infDist_le_hausdorffDist_of_mem (Finset.mem_coe.mpr ha) htop'

end Results.MagnitudeContinuity
