import Results.MagnitudeContinuity.Solution.Core.Aggregation

/-!
# Cardinality-free perturbation estimates

Everything is expressed through quadratic forms and weightings; no operator norm,
no spectral theorem and no matrix inverse is used.  `coercive Z lam` says
`lam * ‖x‖₂² ≤ xᵀ Z x`, i.e. `lam` is a lower bound for the smallest eigenvalue.
-/

set_option linter.unusedSectionVars false

noncomputable section
open scoped BigOperators

namespace MagCore

universe u v

section Norms
variable {ι : Type u} [Fintype ι]

def l1 (x : ι → ℝ) : ℝ := ∑ i, |x i|

def sqNorm (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

def coercive (Z : Kernel ι) (lam : ℝ) : Prop := ∀ x : ι → ℝ, lam * sqNorm x ≤ quadratic Z x

theorem l1_nonneg (x : ι → ℝ) : 0 ≤ l1 x := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem sqNorm_nonneg (x : ι → ℝ) : 0 ≤ sqNorm x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem mass_le_l1 (x : ι → ℝ) : mass x ≤ l1 x :=
  Finset.sum_le_sum (fun i _ => le_abs_self (x i))

/-- Cauchy–Schwarz in the form `‖x‖₁² ≤ |ι| ‖x‖₂²`, proved from `∑ᵢⱼ (|xᵢ| - |xⱼ|)² ≥ 0`. -/
theorem l1_sq_le (x : ι → ℝ) : l1 x ^ 2 ≤ (Fintype.card ι : ℝ) * sqNorm x := by
  have key : 0 ≤ ∑ i, ∑ j, (|x i| - |x j|) ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have expand : ∑ i, ∑ j, (|x i| - |x j|) ^ 2 =
      2 * ((Fintype.card ι : ℝ) * sqNorm x) - 2 * l1 x ^ 2 := by
    have h1 : ∀ i j, (|x i| - |x j|) ^ 2 = x i ^ 2 + x j ^ 2 - 2 * (|x i| * |x j|) := by
      intro i j
      have a := sq_abs (x i)
      have b := sq_abs (x j)
      nlinarith
    simp only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    have h2 : ∑ i, |x i| * ∑ j, |x j| = l1 x ^ 2 := by
      unfold l1
      rw [← Finset.sum_mul, sq]
    have h3 : ∑ i : ι, ∑ _j : ι, x i ^ 2 = (Fintype.card ι : ℝ) * sqNorm x := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      unfold sqNorm
      rw [Finset.mul_sum]
    have h4 : ∑ _i : ι, ∑ j : ι, x j ^ 2 = (Fintype.card ι : ℝ) * sqNorm x := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rfl
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h3 h4 ⊢
    unfold sqNorm l1 at *
    rw [← Finset.mul_sum] at *
    nlinarith [h2]
  rw [expand] at key
  linarith

/-- Entrywise smallness controls the signed quadratic form by `ε ‖x‖₁²`. -/
theorem abs_quadratic_le (D : Kernel ι) {ε : ℝ} (hD : ∀ i j, |D i j| ≤ ε) (x : ι → ℝ) :
    |quadratic D x| ≤ ε * l1 x ^ 2 := by
  unfold quadratic bilinear
  calc |∑ i, ∑ j, x i * D i j * x j|
        ≤ ∑ i, |∑ j, x i * D i j * x j| :=
          Finset.abs_sum_le_sum_abs (fun i => ∑ j, x i * D i j * x j) Finset.univ
    _ ≤ ∑ i, ∑ j, |x i * D i j * x j| :=
        Finset.sum_le_sum (fun i _ =>
          Finset.abs_sum_le_sum_abs (fun j => x i * D i j * x j) Finset.univ)
    _ ≤ ∑ i, ∑ j, |x i| * ε * |x j| := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
        rw [abs_mul, abs_mul]
        have h1 := hD i j
        have h2 := abs_nonneg (x i)
        have h3 := abs_nonneg (x j)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) h3
    _ = ε * l1 x ^ 2 := by
        have e : ∀ i, ∑ j, |x i| * ε * |x j| = |x i| * ε * l1 x := by
          intro i
          exact (Finset.mul_sum Finset.univ (fun j => |x j|) (|x i| * ε)).symm
        have e1 : ∑ i, |x i| * ε * l1 x = (∑ i, |x i| * ε) * l1 x :=
          (Finset.sum_mul Finset.univ (fun i => |x i| * ε) (l1 x)).symm
        have e2 : ∑ i, |x i| * ε = l1 x * ε :=
          (Finset.sum_mul Finset.univ (fun i => |x i|) ε).symm
        rw [Finset.sum_congr rfl (fun i _ => e i), e1, e2]
        ring

theorem coercive_qPositive {Z : Kernel ι} {lam : ℝ} (hlam : 0 ≤ lam) (hZ : coercive Z lam) :
    qPositive Z := fun x => le_trans (mul_nonneg hlam (sqNorm_nonneg x)) (hZ x)

/-- If `B` is entrywise `ε`-close to a coercive `Z`, then `(1 - |ι| ε / lam) Z ≤ B`. -/
theorem close_lower {Z B : Kernel ι} {lam ε : ℝ} (hlam : 0 < lam) (hε : 0 ≤ ε)
    (hZ : coercive Z lam) (hclose : ∀ i j, |Z i j - B i j| ≤ ε) (x : ι → ℝ) :
    (1 - (Fintype.card ι : ℝ) * ε / lam) * quadratic Z x ≤ quadratic B x := by
  have hdiff := abs_quadratic_le (fun i j => Z i j - B i j) hclose x
  rw [quadratic_sub_kernel] at hdiff
  have h1 := (abs_le.mp hdiff).2
  have h2 := l1_sq_le x
  have h4 : ε * l1 x ^ 2 ≤ ε * ((Fintype.card ι : ℝ) * sqNorm x) :=
    mul_le_mul_of_nonneg_left h2 hε
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have h6 : sqNorm x ≤ quadratic Z x / lam := by
    rw [le_div_iff₀ hlam]; linarith [hZ x]
  have h5 : (Fintype.card ι : ℝ) * ε * sqNorm x ≤
      (Fintype.card ι : ℝ) * ε * (quadratic Z x / lam) :=
    mul_le_mul_of_nonneg_left h6 (mul_nonneg hcard hε)
  have h7 : (Fintype.card ι : ℝ) * ε / lam * quadratic Z x =
      (Fintype.card ι : ℝ) * ε * (quadratic Z x / lam) := by ring
  linarith

/-- If `B` is entrywise `ε`-close to a coercive `Z`, then `B ≤ (1 + |ι| ε / lam) Z`. -/
theorem close_upper {Z B : Kernel ι} {lam ε : ℝ} (hlam : 0 < lam) (hε : 0 ≤ ε)
    (hZ : coercive Z lam) (hclose : ∀ i j, |Z i j - B i j| ≤ ε) (x : ι → ℝ) :
    quadratic B x ≤ (1 + (Fintype.card ι : ℝ) * ε / lam) * quadratic Z x := by
  have hdiff := abs_quadratic_le (fun i j => Z i j - B i j) hclose x
  rw [quadratic_sub_kernel] at hdiff
  have h1 := (abs_le.mp hdiff).1
  have h2 := l1_sq_le x
  have h4 : ε * l1 x ^ 2 ≤ ε * ((Fintype.card ι : ℝ) * sqNorm x) :=
    mul_le_mul_of_nonneg_left h2 hε
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have h6 : sqNorm x ≤ quadratic Z x / lam := by
    rw [le_div_iff₀ hlam]; linarith [hZ x]
  have h5 : (Fintype.card ι : ℝ) * ε * sqNorm x ≤
      (Fintype.card ι : ℝ) * ε * (quadratic Z x / lam) :=
    mul_le_mul_of_nonneg_left h6 (mul_nonneg hcard hε)
  have h7 : (Fintype.card ι : ℝ) * ε / lam * quadratic Z x =
      (Fintype.card ι : ℝ) * ε * (quadratic Z x / lam) := by ring
  linarith

theorem mass_weighting_nonneg {Z : Kernel ι} (hp : qPositive Z) {w : ι → ℝ}
    (hw : weighting Z w) : 0 ≤ mass w := by
  rw [← quadratic_weighting hw]; exact hp w

/-- A priori bound `Mag ≤ |ι| / lam`, with no assumption on the signs of the weights. -/
theorem mass_weighting_le {Z : Kernel ι} {lam : ℝ} (hlam : 0 < lam) (hZ : coercive Z lam)
    {w : ι → ℝ} (hw : weighting Z w) : mass w ≤ (Fintype.card ι : ℝ) / lam := by
  have hQ : quadratic Z w = mass w := quadratic_weighting hw
  have h1 : lam * sqNorm w ≤ mass w := hQ ▸ hZ w
  have h2 : mass w ≤ l1 w := mass_le_l1 w
  have h3 := l1_sq_le w
  have hS := l1_nonneg w
  rw [le_div_iff₀ hlam]
  by_cases hS0 : l1 w = 0
  · have : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
    nlinarith
  · have hSpos : 0 < l1 w := lt_of_le_of_ne hS (Ne.symm hS0)
    have h4 : lam * l1 w ^ 2 ≤ (Fintype.card ι : ℝ) * l1 w := by nlinarith
    have h5 : lam * l1 w ≤ (Fintype.card ι : ℝ) := by
      have : lam * l1 w * l1 w ≤ (Fintype.card ι : ℝ) * l1 w := by nlinarith
      exact le_of_mul_le_mul_right this hSpos
    nlinarith

end Norms

section Perturb
variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Rescaled variational bound: `2·1ᵀc - θ cᵀZc ≤ Mag(Z)/θ` for every signed `c`. -/
theorem scaled_energy_le {Z : Kernel κ} (hs : symmetric Z) (hp : qPositive Z) {w : κ → ℝ}
    (hw : weighting Z w) {θ : ℝ} (hθ : 0 < θ) (c : κ → ℝ) :
    2 * mass c - θ * quadratic Z c ≤ mass w / θ := by
  have h := energy_le_weighting hs hp hw (fun a => θ * c a)
  unfold energy at h
  rw [mass_smul_vec, quadratic_smul_vec] at h
  rw [le_div_iff₀ hθ]
  nlinarith

/-- **Upper perturbation bound.**  `A` lives on the (arbitrarily large) index type `ι`,
`Z` and `B` on the fixed type `κ`.  No weighting or inverse of `B` is needed. -/
theorem upper_perturbation {Z B : Kernel κ} {A : Kernel ι} {lam ε : ℝ}
    (hs : symmetric Z) (hlam : 0 < lam) (hZ : coercive Z lam) (hε : 0 ≤ ε)
    (hclose : ∀ a b, |Z a b - B a b| ≤ ε)
    (hsmall : (Fintype.card κ : ℝ) * ε < lam)
    (p : ι → κ) (hdom : qLE (pullbackKernel B p) A)
    {wA : ι → ℝ} (hwA : weighting A wA) {wZ : κ → ℝ} (hwZ : weighting Z wZ) :
    mass wA ≤ mass wZ / (1 - (Fintype.card κ : ℝ) * ε / lam) := by
  have hθ : 0 < 1 - (Fintype.card κ : ℝ) * ε / lam := by
    rw [sub_pos, div_lt_one hlam]; exact hsmall
  have hp : qPositive Z := coercive_qPositive hlam.le hZ
  have h1 : energy A wA ≤ energy B (aggregate p wA) :=
    energy_le_energy_aggregate A B p hdom wA
  rw [energy_at_weighting hwA] at h1
  have h2 := close_lower hlam hε hZ hclose (aggregate p wA)
  have h3 := scaled_energy_le hs hp hwZ hθ (aggregate p wA)
  unfold energy at h1
  linarith

theorem upper_perturbation_additive {Z B : Kernel κ} {A : Kernel ι} {lam ε : ℝ}
    (hs : symmetric Z) (hlam : 0 < lam) (hZ : coercive Z lam) (hε : 0 ≤ ε)
    (hclose : ∀ a b, |Z a b - B a b| ≤ ε)
    (hsmall : (Fintype.card κ : ℝ) * ε ≤ lam / 2)
    (p : ι → κ) (hdom : qLE (pullbackKernel B p) A)
    {wA : ι → ℝ} (hwA : weighting A wA) {wZ : κ → ℝ} (hwZ : weighting Z wZ) :
    mass wA ≤ mass wZ + 2 * (Fintype.card κ : ℝ) ^ 2 * ε / lam ^ 2 := by
  have hsmall' : (Fintype.card κ : ℝ) * ε < lam := by linarith
  have h := upper_perturbation hs hlam hZ hε hclose hsmall' p hdom hwA hwZ
  have hp : qPositive Z := coercive_qPositive hlam.le hZ
  have hM0 := mass_weighting_nonneg hp hwZ
  have hM1 := mass_weighting_le hlam hZ hwZ
  set m : ℝ := (Fintype.card κ : ℝ) with hm
  set M : ℝ := mass wZ with hM
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  set δ : ℝ := m * ε / lam with hδ
  have hδ0 : 0 ≤ δ := div_nonneg (mul_nonneg hm0 hε) hlam.le
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ hlam]; linarith
  have hθ : 0 < 1 - δ := by linarith
  have hstep : M / (1 - δ) ≤ M + 2 * M * δ := by
    rw [div_le_iff₀ hθ]
    nlinarith [mul_nonneg hM0 hδ0, mul_nonneg (mul_nonneg hM0 hδ0) (sub_nonneg.mpr hδ1)]
  have hfin : 2 * M * δ ≤ 2 * m ^ 2 * ε / lam ^ 2 := by
    have : 2 * m ^ 2 * ε / lam ^ 2 = 2 * (m / lam) * δ := by
      rw [hδ]; field_simp
    rw [this]
    have := mul_le_mul_of_nonneg_right hM1 hδ0
    linarith
  linarith

/-- **Lower perturbation bound** for two kernels on the same fixed index type. -/
theorem lower_perturbation {Z Y : Kernel κ} {lam ε : ℝ}
    (hlam : 0 < lam) (hZ : coercive Z lam) (hε : 0 ≤ ε)
    (hclose : ∀ a b, |Z a b - Y a b| ≤ ε)
    (hsY : symmetric Y) (hpY : qPositive Y)
    {wY : κ → ℝ} (hwY : weighting Y wY) {wZ : κ → ℝ} (hwZ : weighting Z wZ) :
    mass wZ / (1 + (Fintype.card κ : ℝ) * ε / lam) ≤ mass wY := by
  have hm0 : (0 : ℝ) ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hη : 0 < 1 + (Fintype.card κ : ℝ) * ε / lam := by
    have := div_nonneg (mul_nonneg hm0 hε) hlam.le
    linarith
  set η : ℝ := 1 + (Fintype.card κ : ℝ) * ε / lam with hηdef
  have h := energy_le_weighting hsY hpY hwY (fun a => (1 / η) * wZ a)
  unfold energy at h
  rw [mass_smul_vec, quadratic_smul_vec] at h
  have hup := close_upper hlam hε hZ hclose wZ
  rw [quadratic_weighting hwZ] at hup
  rw [div_le_iff₀ hη]
  have hQ : (1 / η) ^ 2 * quadratic Y wZ ≤ (1 / η) ^ 2 * (η * mass wZ) :=
    mul_le_mul_of_nonneg_left hup (sq_nonneg _)
  have e1 : (1 / η) ^ 2 * (η * mass wZ) = (1 / η) * mass wZ := by
    field_simp
  have e2 : (1 / η) * mass wZ * η = mass wZ := by field_simp
  nlinarith

theorem lower_perturbation_additive {Z Y : Kernel κ} {lam ε : ℝ}
    (hlam : 0 < lam) (hZ : coercive Z lam) (hε : 0 ≤ ε)
    (hclose : ∀ a b, |Z a b - Y a b| ≤ ε)
    (hsY : symmetric Y) (hpY : qPositive Y)
    {wY : κ → ℝ} (hwY : weighting Y wY) {wZ : κ → ℝ} (hwZ : weighting Z wZ) :
    mass wZ - (Fintype.card κ : ℝ) ^ 2 * ε / lam ^ 2 ≤ mass wY := by
  have h := lower_perturbation hlam hZ hε hclose hsY hpY hwY hwZ
  have hp : qPositive Z := coercive_qPositive hlam.le hZ
  have hM0 := mass_weighting_nonneg hp hwZ
  have hM1 := mass_weighting_le hlam hZ hwZ
  set m : ℝ := (Fintype.card κ : ℝ) with hm
  set M : ℝ := mass wZ with hM
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  set δ : ℝ := m * ε / lam with hδ
  have hδ0 : 0 ≤ δ := div_nonneg (mul_nonneg hm0 hε) hlam.le
  have hη : 0 < 1 + δ := by linarith
  have hstep : M - M * δ ≤ M / (1 + δ) := by
    rw [le_div_iff₀ hη]
    nlinarith [mul_nonneg hM0 (sq_nonneg δ)]
  have hfin : M * δ ≤ m ^ 2 * ε / lam ^ 2 := by
    have : m ^ 2 * ε / lam ^ 2 = (m / lam) * δ := by
      rw [hδ]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hM1 hδ0
  linarith

end Perturb

end MagCore
