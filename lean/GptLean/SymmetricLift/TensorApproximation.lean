import GptLean.SymmetricLift.BoundedTensorMetric
import GptLean.SymmetricLift.PairEnergyIntegrability
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
Classical differentiation of the configuration tensor from ordinary
one-particle differentiability and static tensor multilinearity. The derivative
is the finite sum obtained by replacing one factor at a time.

These results do not assert density in the local Sobolev norm. In particular,
joint approximation of a weakly differentiable function and its derivatives
remains a separate analytic step.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace GptLean.SymmetricLift

open TopologicalSpace
open scoped BigOperators

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [SeparableSpace V]

theorem particle_single_same {n : ℕ} (i : Fin n) (μ : Fin 3) :
    particle (EuclideanSpace.single (i, μ) (1 : ℝ)) i = EuclideanSpace.single μ 1 := by
  ext ν
  simp [particle, PiLp.single_apply]

theorem particle_single_ne {n : ℕ} (i : Fin n) (μ : Fin 3) {j : Fin n}
    (hji : j ≠ i) : particle (EuclideanSpace.single (i, μ) (1 : ℝ)) j = 0 := by
  ext ν
  simp [particle, hji]

namespace TensorMultilinearData

variable {B : TensorBackground V} (M : TensorMultilinearData B)
include M

/-- The ordinary chain-rule derivative of the pure configuration tensor. -/
def configurationTensorDerivative {n : ℕ}
    (t : EuclideanSpace ℝ (Fin 3) → V) (x : Configuration n) :
    Configuration n →L[ℝ] B.H n :=
  (((M.pureMap n).restrictScalars ℝ).linearDeriv (fun i => t (particle x i))).comp
    (ContinuousLinearMap.pi fun i =>
      (fderiv ℝ t (particle x i)).comp (particleLinear i).toContinuousLinearMap)

theorem hasFDerivAt_configurationTensor {n : ℕ}
    (t : EuclideanSpace ℝ (Fin 3) → V) (x : Configuration n)
    (ht : ∀ i, DifferentiableAt ℝ t (particle x i)) :
    HasFDerivAt (configurationTensor B t) (M.configurationTensorDerivative t x) x := by
  change HasFDerivAt (fun y : Configuration n => B.pure n (fun i => t (particle y i)))
    (M.configurationTensorDerivative t x) x
  have hp : HasFDerivAt (fun y : Configuration n => fun i => t (particle y i))
      (ContinuousLinearMap.pi fun i =>
        (fderiv ℝ t (particle x i)).comp (particleLinear i).toContinuousLinearMap) x :=
    hasFDerivAt_pi.2 fun i =>
      (ht i).hasFDerivAt.comp x (particleLinear i).toContinuousLinearMap.hasFDerivAt
  have h := (((M.pureMap n).restrictScalars ℝ).hasFDerivAt
    (fun i => t (particle x i))).comp x hp
  simpa only [Function.comp_def, ContinuousMultilinearMap.coe_restrictScalars,
    M.pure_eq, configurationTensorDerivative, configurationTensor] using h

theorem differentiableAt_configurationTensor {n : ℕ}
    (t : EuclideanSpace ℝ (Fin 3) → V) (x : Configuration n)
    (ht : ∀ i, DifferentiableAt ℝ t (particle x i)) :
    DifferentiableAt ℝ (configurationTensor B t) x :=
  (M.hasFDerivAt_configurationTensor t x ht).differentiableAt

theorem differentiable_configurationTensor {n : ℕ}
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : Differentiable ℝ t) :
    Differentiable ℝ (configurationTensor B t : Configuration n → B.H n) :=
  fun x => M.differentiableAt_configurationTensor t x (fun i => ht (particle x i))

/-- Each summand differentiates exactly one one-particle factor. -/
theorem fderiv_configurationTensor_apply {n : ℕ}
    (t : EuclideanSpace ℝ (Fin 3) → V) (x d : Configuration n)
    (ht : ∀ i, DifferentiableAt ℝ t (particle x i)) :
    fderiv ℝ (configurationTensor B t) x d =
      ∑ i : Fin n, B.pure n (Function.update (fun j => t (particle x j)) i
        (fderiv ℝ t (particle x i) (particle d i))) := by
  rw [(M.hasFDerivAt_configurationTensor t x ht).fderiv]
  simp only [configurationTensorDerivative, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.linearDeriv_apply, ContinuousLinearMap.pi_apply,
    ContinuousMultilinearMap.coe_restrictScalars, M.pure_eq,
    LinearMap.coe_toContinuousLinearMap', particleLinear]
  rfl

/-- A configuration coordinate differentiates only its own particle factor. -/
theorem fderiv_configurationTensor_single {n : ℕ}
    (t : EuclideanSpace ℝ (Fin 3) → V) (x : Configuration n)
    (i : Fin n) (μ : Fin 3)
    (ht : ∀ j, DifferentiableAt ℝ t (particle x j)) :
    fderiv ℝ (configurationTensor B t) x (EuclideanSpace.single (i, μ) 1) =
      B.pure n (Function.update (fun j => t (particle x j)) i
        (fderiv ℝ t (particle x i) (EuclideanSpace.single μ 1))) := by
  rw [M.fderiv_configurationTensor_apply t x _ ht, Finset.sum_eq_single i]
  · rw [particle_single_same]
  · intro j _ hji
    rw [particle_single_ne i μ hji, map_zero]
    exact M.pure_zero_of_factor_zero _ j (by simp)
  · simp

end TensorMultilinearData
end GptLean.SymmetricLift
