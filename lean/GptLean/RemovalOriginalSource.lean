import GptLean.RemovalOriginalTests

/-!
Primitive original spectral vectors and electronic localization data.
The conditioned source and all source estimates are constructed from
these data. No localized normalization or constraint sum is a field.
-/

noncomputable section

namespace GptLean.RemovalSource

open MeasureTheory ElectronicLocalization RemovalEnergy

variable {Q X J H K Hr Kr Hs : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace Q] [MeasurableSpace X]
  {μ : Measure Q} {ν : Measure X} [SFinite μ] [SFinite ν] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup Kr] [InnerProductSpace ℂ Kr]
  [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

structure OriginalSource (μ : Measure Q) (ν : Measure X) (J H K Hr Kr Hs : Type*)
    [Fintype J] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
    [NormedAddCommGroup Kr] [InnerProductSpace ℂ Kr]
    [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] where
  wis : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν)
  wisRest : Lp Hr 2 ν ≃ₗᵢ[ℂ] Lp Kr 2 (μ.prod ν)
  cutoff : ℕ → X → ℝ
  locallyFinite : LocallyFinite (fun a => Function.support (cutoff a))
  differentiable : ∀ a, Differentiable ℝ (cutoff a)
  nonneg : ∀ a x, 0 ≤ cutoff a x
  partition : ∀ x, HasSum (fun a => cutoff a x ^ 2) 1
  measurable : ∀ a, AEStronglyMeasurable (cutoff a) ν
  vector : ℕ → Lp H 2 ν
  covariant : ℕ → J → Lp H 2 ν
  rest : ℕ → Lp Hr 2 ν
  soft : ℕ → Lp Hs 2 ν
  direction : J → X
  derivative_measurable : ∀ a j,
    AEStronglyMeasurable (fun x => fderiv ℝ (cutoff a) x (direction j)) ν
  metric : J → ℝ
  metric_bound : ∀ j x, (∑' a, fderiv ℝ (cutoff a) x (direction j) ^ 2) ≤ metric j
  normalized : HasSum (fun n => ‖vector n‖ ^ 2) 1
  kinetic_summable : ∀ j, Summable (fun n => ‖covariant n j‖ ^ 2)
  rest_summable : Summable (fun n => ‖rest n‖ ^ 2)
  soft_summable : Summable (fun n => ‖soft n‖ ^ 2)

namespace OriginalSource

variable (A : OriginalSource μ ν J H K Hr Kr Hs)

def conditionedSource : ConditionedSource μ ν J K Kr :=
  localizedConditionedSource A.wis A.wisRest A.cutoff A.locallyFinite A.differentiable A.nonneg
    A.partition A.measurable A.vector A.covariant A.rest A.soft A.direction A.derivative_measurable
    A.metric A.metric_bound A.normalized A.kinetic_summable A.rest_summable A.soft_summable

def energy : ℝ := ((1 / 2 : ℝ) * ∑ j, ∑' n, ‖A.covariant n j‖ ^ 2) +
  (∑' n, ‖A.rest n‖ ^ 2) + (∑' n, ‖A.soft n‖ ^ 2)

theorem input_bound : (∑' i, A.conditionedSource.input i) ≤ A.energy + (1 / 2 : ℝ) * ∑ j, A.metric j :=
  localizedConditionedSource_input_bound A.wis A.wisRest A.cutoff A.locallyFinite A.differentiable A.nonneg
    A.partition A.measurable A.vector A.covariant A.rest A.soft A.direction A.derivative_measurable
    A.metric A.metric_bound A.normalized A.kinetic_summable A.rest_summable A.soft_summable

theorem soft_hasSum : HasSum A.conditionedSource.soft (∑' n, ‖A.soft n‖ ^ 2) :=
  localizedConditionedSource_soft_hasSum A.wis A.wisRest A.cutoff A.locallyFinite A.differentiable A.nonneg
    A.partition A.measurable A.vector A.covariant A.rest A.soft A.direction A.derivative_measurable
    A.metric A.metric_bound A.normalized A.kinetic_summable A.rest_summable A.soft_summable A.soft_summable.hasSum

variable {T F DensityTest CurrentTest : Type*}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {R : Gaussian.RankOneData (Lp K 2 ν) T} {marginal : T →L[ℝ] F}
  {densityTarget : DensityTest → ℝ} {currentTarget : CurrentTest → ℝ} {hardTarget : F}
  (D : OriginalSourceTests A.wis A.vector A.covariant R marginal densityTarget currentTarget hardTarget)

theorem density_source (w : ℕ → Q × X → ℂ) (hw : ∀ i qx, ‖w i qx‖ = 1) (t : DensityTest) :
    HasSum (fun i => ∫ q, ∫ x, (D.density t).weight x *
      ‖A.conditionedSource.phasedSource w i (q, x)‖ ^ 2 ∂ν ∂μ) (densityTarget t) :=
  D.density_source A.wis A.wisRest A.cutoff A.locallyFinite A.differentiable A.nonneg
    A.partition A.measurable A.vector A.covariant A.rest A.soft A.direction A.derivative_measurable
    A.metric A.metric_bound A.normalized A.kinetic_summable A.rest_summable A.soft_summable w hw t

theorem current_source (w : ℕ → Q × X → ℂ) (s : ℕ → J → Q × X → ℝ)
    (hw : ∀ i qx, ‖w i qx‖ = 1) (t : CurrentTest) :
    HasSum (fun i => ∫ q, (∫ x,
      inner ℂ (A.conditionedSource.phasedSource w i (q, x))
        (((D.current t).weight x : ℂ) • A.conditionedSource.phasedHardDerivative w s i (D.direction t) (q, x)) +
      (((D.current t).weight x * s i (D.direction t) (q, x) : ℝ) : ℂ) *
        ‖A.conditionedSource.phasedSource w i (q, x)‖ ^ 2 ∂ν).re ∂μ) (currentTarget t) :=
  D.current_source A.wis A.wisRest A.cutoff A.locallyFinite A.differentiable A.nonneg
    A.partition A.measurable A.vector A.covariant A.rest A.soft A.direction A.derivative_measurable
    A.metric A.metric_bound A.normalized A.kinetic_summable A.rest_summable A.soft_summable w s hw t

include D in
theorem marginal_source [IsSeparable ν] [TopologicalSpace.SeparableSpace K]
    (w : ℕ → Q × X → ℂ) (hwm : ∀ i, StronglyMeasurable (w i)) (hw : ∀ i qx, ‖w i qx‖ = 1) :
    HasSum (fun i => productSourceMarginal (μ := μ) R marginal
      (A.conditionedSource.phasedSource w i)) hardTarget :=
  D.marginal_source A.wis A.wisRest A.cutoff A.locallyFinite A.differentiable A.nonneg
    A.partition A.measurable A.vector A.covariant A.rest A.soft A.direction A.derivative_measurable
    A.metric A.metric_bound A.normalized A.kinetic_summable A.rest_summable A.soft_summable w hwm hw

end OriginalSource
end GptLean.RemovalSource
