import Results.MagnitudeContinuity.Solution.Core.Quadratic

/-!
# Signed aggregation along an arbitrary labelling map

`p : ι → κ` need be neither injective nor surjective (empty clusters and arbitrarily
many colliding points are allowed); coefficient vectors are arbitrary real vectors.
-/

set_option linter.unusedSectionVars false

noncomputable section
open scoped BigOperators

namespace MagCore

universe u v

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq κ]

def aggregate (p : ι → κ) (x : ι → ℝ) : κ → ℝ := fun a => ∑ i, if p i = a then x i else 0

def pullbackKernel (B : Kernel κ) (p : ι → κ) : Kernel ι := fun i j => B (p i) (p j)

theorem aggregate_mass (p : ι → κ) (x : ι → ℝ) : mass (aggregate p x) = mass x := by
  unfold mass aggregate
  rw [Finset.sum_comm]
  simp

theorem sum_aggregate_mul (p : ι → κ) (x : ι → ℝ) (f : κ → ℝ) :
    (∑ a, aggregate p x a * f a) = ∑ i, x i * f (p i) := by
  unfold aggregate
  calc (∑ a, (∑ i, if p i = a then x i else 0) * f a)
        = ∑ a, ∑ i, if p i = a then x i * f a else 0 := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          by_cases h : p i = a <;> simp [h]
    _ = ∑ i, ∑ a, if p i = a then x i * f a else 0 := Finset.sum_comm
    _ = ∑ i, x i * f (p i) := by simp

theorem bilinear_aggregate (B : Kernel κ) (p : ι → κ) (x y : ι → ℝ) :
    bilinear B (aggregate p x) (aggregate p y) = bilinear (pullbackKernel B p) x y := by
  unfold bilinear
  calc (∑ a, ∑ b, aggregate p x a * B a b * aggregate p y b)
        = ∑ a, aggregate p x a * (∑ b, aggregate p y b * B a b) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          ring
    _ = ∑ a, aggregate p x a * (∑ j, y j * B a (p j)) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [sum_aggregate_mul]
    _ = ∑ i, x i * (∑ j, y j * B (p i) (p j)) :=
          sum_aggregate_mul p x (fun a => ∑ j, y j * B a (p j))
    _ = ∑ i, ∑ j, x i * pullbackKernel B p i j * y j := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          unfold pullbackKernel
          ring

theorem quadratic_aggregate (B : Kernel κ) (p : ι → κ) (x : ι → ℝ) :
    quadratic B (aggregate p x) = quadratic (pullbackKernel B p) x :=
  bilinear_aggregate B p x x

theorem qPositive_pullback {B : Kernel κ} (hB : qPositive B) (p : ι → κ) :
    qPositive (pullbackKernel B p) := by
  intro x
  rw [← quadratic_aggregate]
  exact hB _

theorem symmetric_pullback {B : Kernel κ} (hB : symmetric B) (p : ι → κ) :
    symmetric (pullbackKernel B p) := fun i j => hB (p i) (p j)

/-- The energy of any signed vector on `ι` is dominated by the energy of its aggregate. -/
theorem energy_le_energy_aggregate (A : Kernel ι) (B : Kernel κ) (p : ι → κ)
    (hAB : qLE (pullbackKernel B p) A) (x : ι → ℝ) :
    energy A x ≤ energy B (aggregate p x) := by
  unfold energy
  rw [aggregate_mass, quadratic_aggregate]
  linarith [hAB x]

end MagCore
