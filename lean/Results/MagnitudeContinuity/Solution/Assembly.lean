import Results.MagnitudeContinuity.Solution.Bridge
import Results.MagnitudeContinuity.Solution.Signature
import Results.MagnitudeContinuity.Solution.Envelope

/-!
# Assembly of the proof of Theorem 1.1

Upper bound for every finite subset of `X` (cut deletion + aggregation), lower bound from chosen
representatives (Lipschitz perturbation), then the supremum defining `magnitude X`.
-/

open MeasureTheory MagCore Metric Filter Topology
open scoped ENNReal

noncomputable section

namespace Results.MagnitudeContinuity

/-- `u ↦ e^{-u}` is `1`-Lipschitz on `[0, ∞)`. -/
theorem abs_exp_neg_sub_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.exp (-u) - Real.exp (-v)| ≤ |u - v| := by
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → Real.exp (-a) - Real.exp (-b) ≤ b - a := by
    intro a b ha hab
    have h1 : Real.exp (-a) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    have h2 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : -(b - a) + 1 ≤ Real.exp (-(b - a)) := Real.add_one_le_exp _
    have h4 : Real.exp (-(b - a)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    have h5 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
    have h6 : Real.exp (-a) * (1 - Real.exp (-(b - a))) ≤ 1 * (1 - Real.exp (-(b - a))) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    rw [h2]
    nlinarith
  rcases le_total u v with h | h
  · have h1 : Real.exp (-v) ≤ Real.exp (-u) := Real.exp_le_exp.2 (neg_le_neg h)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    have := key u v hu h
    linarith
  · have h1 : Real.exp (-u) ≤ Real.exp (-v) := Real.exp_le_exp.2 (neg_le_neg h)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    have := key v u hv h
    linarith

section FiniteBounds

variable {U : Type*} [NormedAddCommGroup U]

/-- **Upper bound for one finite subset**: cut deletion of the strips around the limit set `F`,
exact collapse, and aggregation (the author-side `cut_upper_bound`). -/
theorem finite_upper_bound (hPD : IsPositiveDefinite U)
    {T : Type*} [MeasurableSpace T] (ν : Measure T) [SigmaFinite ν]
    (f : U → T → ℝ) (h : T → ℝ) (hf : ∀ x, Measurable (f x)) (hh : Measurable h)
    (h0 : ∀ t, 0 ≤ h t) {α : ℝ} (hα0 : 0 ≤ α)
    (hα : ∫⁻ t, ENNReal.ofReal (h t) ∂ν ≤ ENNReal.ofReal α)
    (henv : ∀ x y t, |f x t - f y t| ≤ h t * dist x y)
    (hdist : ∀ x y, ENNReal.ofReal (dist x y) = ∫⁻ t, ENNReal.ofReal |f x t - f y t| ∂ν)
    (F : Finset U) (hF : F.Nonempty) {lam : ℝ} (hlam : 0 < lam)
    (hcoer : MagCore.coercive (simKernel F) lam) {r : ℝ} (hr : 0 ≤ r)
    (hsmall : (F.card : ℝ) * (α * F.card * r) ≤ lam / 2)
    (A : Finset U) (hA : A.Nonempty) (hnear : ∀ y ∈ A, ∃ a ∈ F, dist y a ≤ r) :
    magnitudeFinset A ≤ magnitudeFinset F + 2 * α * (F.card : ℝ) ^ 3 / lam ^ 2 * r := by
  classical
  have hFpd := hPD F hF
  have hApd := hPD A hA
  set μ : Measure (T × ℝ) := ν.prod volume with hμ
  choose p hpF hpd using fun y : A => hnear (y : U) y.2
  let p' : A → F := fun y => ⟨p y, hpF y⟩
  have hfin : ∀ x y : U, μ {ω | bit f x ω ≠ bit f y ω} = ENNReal.ofReal (dist x y) := by
    intro x y
    rw [hμ, measure_bit_ne ν hf x y, hdist]
  have hEmeas : MeasurableSet (deletedStrip f h (F : Set U) r) :=
    measurableSet_deletedStrip hf hh F r
  have hEle := measure_deletedStrip_le ν hf hh F hr hα
  have hEfin : μ (deletedStrip f h (F : Set U) r) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEle
  have hcollapse : ∀ ω ∉ deletedStrip f h (F : Set U) r, ∀ y : A,
      bit f (y : U) ω = bit f ((p' y : F) : U) ω := by
    intro ω hω y
    have hiff := threshold_equal_outside_strip (fun x y => dist x y) f h (F : Set U) r h0 henv
      (x := (y : U)) (a := p y) (Finset.mem_coe.2 (hpF y)) (hpd y) hω
    simp only [bit, p']
    exact decide_eq_decide.mpr hiff
  obtain ⟨K0, csF, csX, hK0s, hK0, hK0e, hcsF, hcsX, hc, hS, hkF, hkX⟩ :=
    cut_data (Ω := T × ℝ) μ (fun a : F => bit f (a : U)) (fun y : A => bit f (y : U))
      (fun a => measurable_bit hf _) (fun y => measurable_bit hf _)
      (fun a a' => by rw [hfin]; exact ENNReal.ofReal_ne_top)
      (fun i j => by rw [hfin]; exact ENNReal.ofReal_ne_top)
      p' hEmeas hEfin hcollapse
  have hkX' : MagCore.cutProduct (MagCore.pullbackKernel K0 p') csX = simKernel A := by
    funext i j
    rw [hkX, hfin, ENNReal.toReal_ofReal dist_nonneg]
    rfl
  have hkF' : MagCore.cutProduct K0 csF = simKernel F := by
    funext a b
    rw [hkF, hfin, ENNReal.toReal_ofReal dist_nonneg]
    rfl
  obtain ⟨wA, hwA, hmA⟩ := exists_weighting_of_posDef A hApd
  obtain ⟨wF, hwF, hmF⟩ := exists_weighting_of_posDef F hFpd
  have hwA' : MagCore.weighting (MagCore.cutProduct (MagCore.pullbackKernel K0 p') csX) wA := by
    rw [hkX']; exact hwA
  have hwF' : MagCore.weighting (MagCore.cutProduct K0 csF) wF := by
    rw [hkF']; exact hwF
  have hcoer' : MagCore.coercive (MagCore.cutProduct K0 csF) lam := by
    rw [hkF']; exact hcoer
  have hmuE : (μ (deletedStrip f h (F : Set U) r)).toReal ≤ 2 * r * F.card * α := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hEle
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  have hS1 : 1 - MagCore.factorProduct csF ≤ α * F.card * r := by
    rw [hS]
    have h1 := Real.add_one_le_exp (-((μ (deletedStrip f h (F : Set U) r)).toReal / 2))
    have h2 : -((μ (deletedStrip f h (F : Set U) r)).toReal / 2) =
        -(μ (deletedStrip f h (F : Set U) r)).toReal / 2 := by ring
    rw [h2] at h1
    nlinarith
  have hcard : (Fintype.card F : ℝ) = F.card := by simp
  have hsmall' : (Fintype.card F : ℝ) * (1 - MagCore.factorProduct csF) ≤ lam / 2 := by
    rw [hcard]
    have hm0 : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hS1 hm0
    linarith
  have key := MagCore.cut_upper_bound K0 hK0s hK0 hK0e csF hcsF csX hcsX hc p' hlam hcoer'
    hsmall' hwA' hwF'
  have hconst := MagCore.upper_constant α (F.card : ℝ) lam r (1 - MagCore.factorProduct csF)
    hlam hS1
  rw [hcard] at key
  rw [← hmA, ← hmF]
  linarith

/-- **Lower bound**: one representative per point of `F`. -/
theorem finite_lower_bound (hPD : IsPositiveDefinite U)
    (F : Finset U) (hF : F.Nonempty) {lam : ℝ} (hlam : 0 < lam)
    (hcoer : MagCore.coercive (simKernel F) lam) {r : ℝ} (hr : 0 ≤ r)
    (e : F → U) (hinj : Function.Injective e) (hnear : ∀ a : F, dist (e a) (a : U) ≤ r) :
    ∃ A : Finset U, A.Nonempty ∧ (∀ x ∈ A, ∃ a : F, x = e a) ∧
      magnitudeFinset F - 2 * (F.card : ℝ) ^ 2 / lam ^ 2 * r ≤ magnitudeFinset A := by
  classical
  obtain ⟨A, φ, hφ⟩ := exists_equiv_image e hinj
  have hAne : A.Nonempty := by
    obtain ⟨a, ha⟩ := hF
    exact ⟨φ ⟨a, ha⟩, (φ ⟨a, ha⟩).2⟩
  have hApd := hPD A hAne
  have hFpd := hPD F hF
  obtain ⟨wA, hwA, hmA⟩ := exists_weighting_of_posDef A hApd
  obtain ⟨wF, hwF, hmF⟩ := exists_weighting_of_posDef F hFpd
  have hwY : MagCore.weighting (MagCore.pullbackKernel (simKernel A) φ) (fun a => wA (φ a)) := by
    intro a
    have h1 := hwA (φ a)
    have h2 := Equiv.sum_comp φ (fun x => simKernel A (φ a) x * wA x)
    simpa [MagCore.pullbackKernel] using h2.trans h1
  have hmY : MagCore.mass (fun a => wA (φ a)) = magnitudeFinset A := by
    unfold MagCore.mass
    rw [Equiv.sum_comp φ wA]
    exact hmA
  have hclose : ∀ a b, |simKernel F a b - MagCore.pullbackKernel (simKernel A) φ a b| ≤ 2 * r := by
    intro a b
    simp only [simKernel, MagCore.pullbackKernel, hφ]
    calc |Real.exp (-dist (a : U) (b : U)) - Real.exp (-dist (e a) (e b))|
        ≤ |dist (a : U) (b : U) - dist (e a) (e b)| :=
          abs_exp_neg_sub_le dist_nonneg dist_nonneg
      _ ≤ dist (a : U) (e a) + dist (b : U) (e b) := by
          have := dist_dist_dist_le (a : U) (b : U) (e a) (e b)
          rwa [Real.dist_eq] at this
      _ ≤ 2 * r := by
          rw [dist_comm (a : U), dist_comm (b : U)]
          linarith [hnear a, hnear b]
  have hsY := MagCore.symmetric_pullback (simKernel_symmetric A) φ
  have hpY := MagCore.qPositive_pullback (qPositive_simKernel_of_posDef hApd) φ
  have h := MagCore.lower_perturbation_additive hlam hcoer (by linarith : (0 : ℝ) ≤ 2 * r)
    hclose hsY hpY hwY hwF
  refine ⟨A, hAne, ?_, ?_⟩
  · intro x hx
    refine ⟨φ.symm ⟨x, hx⟩, ?_⟩
    rw [← hφ, Equiv.apply_symm_apply]
  · have hcard : (Fintype.card F : ℝ) = F.card := by simp
    rw [hmF, hmY, hcard] at h
    have e1 : (F.card : ℝ) ^ 2 * (2 * r) / lam ^ 2 = 2 * (F.card : ℝ) ^ 2 / lam ^ 2 * r := by
      ring
    linarith

end FiniteBounds

end Results.MagnitudeContinuity
