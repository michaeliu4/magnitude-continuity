import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant

/-!
# Auerbach basis

Module M3a.  Mathlib has no Auerbach lemma; it is proved here by maximizing the absolute value of
the determinant over the closed unit ball.
-/

noncomputable section

namespace Results.MagnitudeContinuity

/-- **Auerbach's lemma** in the form needed: a basis `e` of vectors of norm at most one whose
coordinate functionals `c` are linear of norm at most one. -/
theorem exists_auerbach (U : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] :
    ∃ (e : Fin (Module.finrank ℝ U) → U) (c : U →ₗ[ℝ] (Fin (Module.finrank ℝ U) → ℝ)),
      (∀ i, ‖e i‖ ≤ 1) ∧ (∀ u, ∑ i, c u i • e i = u) ∧ (∀ u i, |c u i| ≤ ‖u‖) := by
  classical
  -- a reference basis and the associated determinant
  let B : Module.Basis (Fin (Module.finrank ℝ U)) ℝ U := Module.finBasis ℝ U
  have hcont : Continuous fun v : Fin (Module.finrank ℝ U) → U => B.det v :=
    Continuous.matrix_det B.continuous_toMatrix
  -- the unit cube
  set S : Set (Fin (Module.finrank ℝ U) → U) :=
    Set.pi Set.univ (fun _ => Metric.closedBall (0 : U) 1) with hS
  have hSc : IsCompact S :=
    isCompact_univ_pi (fun _ => isCompact_closedBall (0 : U) 1)
  have hmem : ∀ v : Fin (Module.finrank ℝ U) → U, v ∈ S ↔ ∀ i, ‖v i‖ ≤ 1 := by
    intro v
    simp [hS]
  -- a point of the cube where the determinant is nonzero
  obtain ⟨v₀, hv₀S, hv₀⟩ : ∃ v₀ ∈ S, B.det v₀ ≠ 0 := by
    set t : ℝ := (1 + ∑ i, ‖B i‖)⁻¹ with ht
    have hpos : 0 < 1 + ∑ i, ‖B i‖ :=
      add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => norm_nonneg _)
    have htpos : 0 < t := inv_pos.mpr hpos
    refine ⟨fun i => t • B i, ?_, ?_⟩
    · rw [hmem]
      intro i
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, ht]
      have hle : ‖B i‖ ≤ 1 + ∑ j, ‖B j‖ := by
        have : ‖B i‖ ≤ ∑ j, ‖B j‖ :=
          Finset.single_le_sum (f := fun j => ‖B j‖) (fun j _ => norm_nonneg _)
            (Finset.mem_univ i)
        linarith
      rw [inv_mul_le_iff₀ hpos]
      linarith
    · have := (B.det).map_smul_univ (fun _ => t) (fun i => B i)
      simp only [smul_eq_mul] at this
      have hB : B.det (fun i => B i) = 1 := B.det_self
      change B.det (fun i => t • B i) ≠ 0
      rw [this, hB, mul_one]
      exact Finset.prod_ne_zero_iff.mpr (fun _ _ => htpos.ne')
  -- maximize `|det|` on the cube
  obtain ⟨v, hvS, hvmax⟩ :=
    hSc.exists_isMaxOn ⟨v₀, hv₀S⟩ (continuous_abs.comp hcont).continuousOn
  have hDv : B.det v ≠ 0 := by
    intro h0
    have := hvmax hv₀S
    simp only [Set.mem_setOf_eq, Function.comp_apply, h0, abs_zero] at this
    exact hv₀ (abs_nonpos_iff.mp this)
  have hDvpos : 0 < |B.det v| := abs_pos.mpr hDv
  have hunit : IsUnit (B.det v) := isUnit_iff_ne_zero.mpr hDv
  obtain ⟨hli, hsp⟩ := (B.is_basis_iff_det).mpr hunit
  let b' : Module.Basis (Fin (Module.finrank ℝ U)) ℝ U := Module.Basis.mk hli hsp.ge
  have hb' : ∀ i, b' i = v i := fun i => by simp [b']
  -- Cramer's rule for the new basis
  have hcramer : ∀ (i : Fin (Module.finrank ℝ U)) (u : U),
      B.det (Function.update v i u) = B.det v * b'.coord i u := by
    intro i u
    have h1 := B.det_smul_mk_coord_eq_det_update hli hsp.ge i
    have h2 := congrArg (fun f => f u) h1
    simp only [LinearMap.smul_apply, smul_eq_mul, MultilinearMap.toLinearMap_apply,
      AlternatingMap.coe_multilinearMap] at h2
    exact h2.symm
  -- the unit-ball bound
  have hunitball : ∀ (u : U) (i : Fin (Module.finrank ℝ U)), ‖u‖ ≤ 1 → |b'.coord i u| ≤ 1 := by
    intro u i hu
    have hupd : Function.update v i u ∈ S := by
      rw [hmem]
      intro j
      by_cases hj : j = i
      · subst hj
        simpa using hu
      · rw [Function.update_of_ne hj]
        exact (hmem v).mp hvS j
    have hle := hvmax hupd
    simp only [Set.mem_setOf_eq, Function.comp_apply] at hle
    rw [hcramer, abs_mul] at hle
    by_contra hcon
    have hcon' := not_le.mp hcon
    have := mul_lt_mul_of_pos_left hcon' hDvpos
    linarith
  refine ⟨v, LinearMap.pi (fun i => b'.coord i), fun i => (hmem v).mp hvS i, ?_, ?_⟩
  · intro u
    have := b'.sum_repr u
    simpa [hb'] using this
  · intro u i
    show |b'.coord i u| ≤ ‖u‖
    by_cases hu : u = 0
    · subst hu
      simp
    · have hnpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have h1 := hunitball (‖u‖⁻¹ • u) i (by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnpos.ne'])
      rw [map_smul, smul_eq_mul, abs_mul, abs_inv, abs_norm] at h1
      rw [inv_mul_le_iff₀ hnpos] at h1
      linarith

end Results.MagnitudeContinuity
