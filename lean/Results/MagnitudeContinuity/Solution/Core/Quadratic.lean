import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Signed quadratic forms, weightings and the variational characterisation

Kernels are plain functions `ι → ι → ℝ` (definitionally the same as `Matrix ι ι ℝ`).
Positivity is quantified over **all** real coefficient vectors; no sign restriction.
Magnitude is handled through *weightings* (`A w = 1`), so no matrix inverse is needed
in this layer.
-/

noncomputable section
open scoped BigOperators

namespace MagCore

universe u v

abbrev Kernel (ι : Type u) := ι → ι → ℝ

variable {ι : Type u} [Fintype ι]

def bilinear (A : Kernel ι) (x y : ι → ℝ) : ℝ := ∑ i, ∑ j, x i * A i j * y j

def quadratic (A : Kernel ι) (x : ι → ℝ) : ℝ := bilinear A x x

def mass (x : ι → ℝ) : ℝ := ∑ i, x i

def symmetric (A : Kernel ι) : Prop := ∀ i j, A i j = A j i

def qPositive (A : Kernel ι) : Prop := ∀ x : ι → ℝ, 0 ≤ quadratic A x

/-- `A ≤ B` in the signed quadratic-form (Loewner) order. -/
def qLE (A B : Kernel ι) : Prop := ∀ x : ι → ℝ, quadratic A x ≤ quadratic B x

/-- `w` is a weighting of `A`:  `A w = 1`. -/
def weighting (A : Kernel ι) (w : ι → ℝ) : Prop := ∀ i, ∑ j, A i j * w j = 1

def energy (A : Kernel ι) (x : ι → ℝ) : ℝ := 2 * mass x - quadratic A x

theorem quadratic_zero (A : Kernel ι) : quadratic A (0 : ι → ℝ) = 0 := by
  simp [quadratic, bilinear]

theorem bilinear_sub_left (A : Kernel ι) (x y z : ι → ℝ) :
    bilinear A (x - y) z = bilinear A x z - bilinear A y z := by
  simp only [bilinear, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem bilinear_sub_right (A : Kernel ι) (x y z : ι → ℝ) :
    bilinear A x (y - z) = bilinear A x y - bilinear A x z := by
  simp only [bilinear, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem bilinear_add_left (A : Kernel ι) (x y z : ι → ℝ) :
    bilinear A (x + y) z = bilinear A x z + bilinear A y z := by
  simp only [bilinear, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem bilinear_add_right (A : Kernel ι) (x y z : ι → ℝ) :
    bilinear A x (y + z) = bilinear A x y + bilinear A x z := by
  simp only [bilinear, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem quadratic_add (A : Kernel ι) (x y : ι → ℝ) :
    quadratic A (x + y) =
      quadratic A x + bilinear A y x + bilinear A x y + quadratic A y := by
  unfold quadratic
  rw [bilinear_add_left, bilinear_add_right, bilinear_add_right]
  ring

theorem quadratic_sub (A : Kernel ι) (x y : ι → ℝ) :
    quadratic A (x - y) =
      quadratic A x - bilinear A y x - bilinear A x y + quadratic A y := by
  unfold quadratic
  rw [bilinear_sub_left, bilinear_sub_right, bilinear_sub_right]
  ring

/-- For a positive form, `Q(x + y) ≤ 2 (Q x + Q y)` (parallelogram-type bound; no symmetry needed). -/
theorem quadratic_add_le {A : Kernel ι} (hA : qPositive A) (x y : ι → ℝ) :
    quadratic A (x + y) ≤ 2 * (quadratic A x + quadratic A y) := by
  have h := hA (x - y)
  rw [quadratic_sub] at h
  rw [quadratic_add]
  linarith

theorem bilinear_symm {A : Kernel ι} (hA : symmetric A) (x y : ι → ℝ) :
    bilinear A x y = bilinear A y x := by
  unfold bilinear
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [hA i j]
  ring

theorem quadratic_linear_combination (A B : Kernel ι) (a b : ℝ) (x : ι → ℝ) :
    quadratic (fun i j => a * A i j + b * B i j) x =
      a * quadratic A x + b * quadratic B x := by
  unfold quadratic bilinear
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

theorem quadratic_smul_kernel (A : Kernel ι) (a : ℝ) (x : ι → ℝ) :
    quadratic (fun i j => a * A i j) x = a * quadratic A x := by
  have h := quadratic_linear_combination A A a 0 x
  simpa using h

theorem quadratic_sub_kernel (A B : Kernel ι) (x : ι → ℝ) :
    quadratic (fun i j => A i j - B i j) x = quadratic A x - quadratic B x := by
  have h := quadratic_linear_combination A B 1 (-1) x
  have e : (fun i j => 1 * A i j + (-1) * B i j) = (fun i j => A i j - B i j) := by
    funext i j; ring
  rw [e] at h
  rw [h]; ring

theorem quadratic_smul_vec (A : Kernel ι) (t : ℝ) (x : ι → ℝ) :
    quadratic A (fun i => t * x i) = t ^ 2 * quadratic A x := by
  unfold quadratic bilinear
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

theorem mass_smul_vec (t : ℝ) (x : ι → ℝ) : mass (fun i => t * x i) = t * mass x := by
  unfold mass
  rw [Finset.mul_sum]

theorem bilinear_weighting {A : Kernel ι} {w : ι → ℝ} (hw : weighting A w) (x : ι → ℝ) :
    bilinear A x w = mass x := by
  unfold bilinear mass
  refine Finset.sum_congr rfl (fun i _ => ?_)
  calc (∑ j, x i * A i j * w j) = x i * ∑ j, A i j * w j := by
        simp only [Finset.mul_sum, mul_assoc]
    _ = x i := by rw [hw i, mul_one]

theorem quadratic_weighting {A : Kernel ι} {w : ι → ℝ} (hw : weighting A w) :
    quadratic A w = mass w := bilinear_weighting hw w

theorem square_completion {A : Kernel ι} (hA : symmetric A) {w : ι → ℝ}
    (hw : weighting A w) (x : ι → ℝ) :
    energy A x = mass w - quadratic A (x - w) := by
  have hxw : bilinear A x w = mass x := bilinear_weighting hw x
  have hwx : bilinear A w x = mass x := (bilinear_symm hA w x).trans hxw
  have hww : quadratic A w = mass w := quadratic_weighting hw
  rw [quadratic_sub, hxw, hwx, hww]
  unfold energy
  ring

theorem energy_at_weighting {A : Kernel ι} {w : ι → ℝ} (hw : weighting A w) :
    energy A w = mass w := by
  unfold energy
  rw [quadratic_weighting hw]
  ring

/-- Variational principle: a weighting maximises the energy over *all signed* vectors. -/
theorem energy_le_weighting {A : Kernel ι} (hs : symmetric A) (hp : qPositive A)
    {w : ι → ℝ} (hw : weighting A w) (x : ι → ℝ) : energy A x ≤ mass w := by
  rw [square_completion hs hw]
  exact sub_le_self _ (hp (x - w))

/-- The total mass of a weighting does not depend on the weighting chosen. -/
theorem mass_weighting_unique {A : Kernel ι} (hs : symmetric A) (hp : qPositive A)
    {w w' : ι → ℝ} (hw : weighting A w) (hw' : weighting A w') : mass w = mass w' := by
  have h1 := energy_le_weighting hs hp hw w'
  have h2 := energy_le_weighting hs hp hw' w
  rw [energy_at_weighting hw'] at h1
  rw [energy_at_weighting hw] at h2
  exact le_antisymm h2 h1

end MagCore
