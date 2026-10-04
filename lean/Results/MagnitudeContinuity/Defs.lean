import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Magnitude continuity at finite sets: definitions

Definitions for the statement of Theorem 1.1 of "Magnitude continuity at finite sets in
finite-dimensional `L₁` subspaces" (M. Liu).  The paper's notation is kept:

* `simMatrix A` is the similarity matrix `Z_A = (e^{-d(x,y)})_{x,y∈A}` of a finite set;
* `magnitudeFinset A` is `Mag A = 1ᵀ Z_A⁻¹ 1`;
* `magnitude K` is `Mag K = sup {Mag A : ∅ ≠ A ⊆ K finite}` (equation (1.3) of the paper),
  valued in `[0,∞]`;
* `IsPositiveDefinite U` says that `Z_A` is positive definite for every nonempty finite `A ⊆ U`;
* `IsLeastEigenvalue Z lam` says that `lam` is the least eigenvalue of the real matrix `Z`;
* `MeckesEmbedding` is the published external input used in the paper (Meckes, Proposition 3.4 with
  `p = 1` and Corollary 3.5, resting on Bretagnolle–Dacunha-Castelle–Krivine, in the form of the paper's
  Lemma 4.1): every finite-dimensional positive definite normed space is linearly isometric to a
  subspace of `L₁[0,1]`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

universe u

namespace Results.MagnitudeContinuity

section Finite

variable {U : Type*} [MetricSpace U]

/-- The similarity matrix `Z_A = (e^{-d(x,y)})_{x,y ∈ A}` of a finite subset `A` of a metric space. -/
def simMatrix (A : Finset U) : Matrix A A ℝ :=
  Matrix.of fun x y => Real.exp (-dist (x : U) (y : U))

open scoped Classical in
/-- The magnitude `Mag A = 1ᵀ Z_A⁻¹ 1` of a finite set (the sum of all entries of `Z_A⁻¹`).  It is
meaningful when `Z_A` is invertible, in particular when `Z_A` is positive definite. -/
def magnitudeFinset (A : Finset U) : ℝ :=
  ∑ x, ∑ y, (simMatrix A)⁻¹ x y

/-- The magnitude of an arbitrary subset `K`: the supremum of the magnitudes of its nonempty finite
subsets, in `[0, ∞]` (equation (1.3) of the paper; for a compact positive definite space this is
Meckes' definition). -/
def magnitude (K : Set U) : ℝ≥0∞ :=
  ⨆ (A : Finset U) (_ : A.Nonempty) (_ : (A : Set U) ⊆ K), ENNReal.ofReal (magnitudeFinset A)

/-- A metric space is positive definite when `Z_A` is positive definite for every nonempty finite
subset `A`. -/
def IsPositiveDefinite (U : Type*) [MetricSpace U] : Prop :=
  ∀ A : Finset U, A.Nonempty → (simMatrix A).PosDef

end Finite

open scoped Classical in
/-- `lam` is the least eigenvalue of the real matrix `Z` (acting on Euclidean space). -/
def IsLeastEigenvalue {ι : Type*} [Fintype ι] (Z : Matrix ι ι ℝ) (lam : ℝ) : Prop :=
  Module.End.HasEigenvalue (Matrix.toEuclideanLin Z) lam ∧
    ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toEuclideanLin Z) μ → lam ≤ μ

/-- **External input** (Meckes, Proposition 3.4 with `p = 1` and Corollary 3.5, via
Bretagnolle–Dacunha-Castelle–Krivine, as quoted in the proof of the paper's Lemma 4.1): every
finite-dimensional positive definite normed space is linearly isometric to a subspace of
`L₁[0,1]`.  This published theorem is not in Mathlib; it is carried as an explicit hypothesis of
the main theorem, never as an axiom. -/
def MeckesEmbedding : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    IsPositiveDefinite V →
      Nonempty (V →ₗᵢ[ℝ] Lp ℝ 1 (volume.restrict (Set.Icc (0 : ℝ) 1)))

end Results.MagnitudeContinuity
