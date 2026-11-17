import GptLean.RemovalSourceConditionedEnergy
import GptLean.RemovalSourceTrace

/-!
One package of original spectral density, current and hard-marginal
tests. Localized and phased source identities are derived by its methods.
No field contains a localized sum or a conclusion about the output state.
-/

noncomputable section

namespace GptLean.RemovalSource

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open MeasureTheory MeasureTheory.Measure Filter ElectronicLocalization RemovalEnergy

variable {Q X J H K Hr Kr Hs T F DensityTest CurrentTest : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace Q] [MeasurableSpace X] {μ : Measure Q} {ν : Measure X}
  [SFinite μ] [SFinite ν] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup Kr] [InnerProductSpace ℂ Kr]
  [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

structure OriginalSourceTests
    (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν))
    (ψ : ℕ → Lp H 2 ν) (dψ : ℕ → J → Lp H 2 ν)
    (R : Gaussian.RankOneData (Lp K 2 ν) T) (marginal : T →L[ℝ] F)
    (densityTarget : DensityTest → ℝ) (currentTarget : CurrentTest → ℝ) (hardTarget : F) where
  density : ∀ t, ProductDensityTest U ψ (densityTarget t)
  direction : CurrentTest → J
  current : ∀ t, ProductCurrentData U ψ (fun n => dψ n (direction t)) (currentTarget t)
  hardTests : ℕ → F →L[ℝ] ℝ
  hard : ∀ t, ProductTestData U ψ (hardTests t hardTarget : ℂ)
  separating : ∀ a b : F, (∀ t, hardTests t a = hardTests t b) → a = b
  hard_rankOne : ∀ t q (v : Lp K 2 ν), hardTests t (marginal (R.rankOne v)) =
    (∫ x, inner ℂ (v x) ((hard t).targetMultiplier (q, x) (v x)) ∂ν).re

section Localized

variable
    (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν))
    (Ur : Lp Hr 2 ν ≃ₗᵢ[ℂ] Lp Kr 2 (μ.prod ν))
    (f : ℕ → X → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (f a)))
    (hd : ∀ a, Differentiable ℝ (f a)) (hpos : ∀ a x, 0 ≤ f a x)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν)
    (ψ : ℕ → Lp H 2 ν) (dψ : ℕ → J → Lp H 2 ν)
    (rest : ℕ → Lp Hr 2 ν) (soft : ℕ → Lp Hs 2 ν) (v : J → X)
    (hdf : ∀ a j, AEStronglyMeasurable (fun x => fderiv ℝ (f a) x (v j)) ν)
    (C : J → ℝ) (hmetric : ∀ j x, (∑' a, fderiv ℝ (f a) x (v j) ^ 2) ≤ C j)
    (hmass : HasSum (fun n => ‖ψ n‖ ^ 2) 1)
    (hkinetic : ∀ j, Summable (fun n => ‖dψ n j‖ ^ 2))
    (hrest : Summable (fun n => ‖rest n‖ ^ 2))
    (hsoft : Summable (fun n => ‖soft n‖ ^ 2))
    {R : Gaussian.RankOneData (Lp K 2 ν) T} {marginal : T →L[ℝ] F}
    {densityTarget : DensityTest → ℝ} {currentTarget : CurrentTest → ℝ} {hardTarget : F}
    (D : OriginalSourceTests U ψ dψ R marginal densityTarget currentTarget hardTarget)

local notation "S" => localizedConditionedSource U Ur f hloc hd hpos hpart hf ψ dψ rest soft v
  hdf C hmetric hmass hkinetic hrest hsoft

theorem OriginalSourceTests.density_source
    (w : ℕ → Q × X → ℂ) (hw : ∀ i qx, ‖w i qx‖ = 1) (t : DensityTest) :
    HasSum (fun i => ∫ q, ∫ x, (D.density t).weight x *
      ‖(S).phasedSource w i (q, x)‖ ^ 2 ∂ν ∂μ) (densityTarget t) :=
  (D.density t).phased_density_hasSum f hpart hf hmass.summable w hw

theorem OriginalSourceTests.current_source
    (w : ℕ → Q × X → ℂ) (s : ℕ → J → Q × X → ℝ)
    (hw : ∀ i qx, ‖w i qx‖ = 1) (t : CurrentTest) :
    HasSum (fun i => ∫ q, (∫ x,
      inner ℂ ((S).phasedSource w i (q, x))
        (((D.current t).weight x : ℂ) • (S).phasedHardDerivative w s i (D.direction t) (q, x)) +
      (((D.current t).weight x * s i (D.direction t) (q, x) : ℝ) : ℂ) *
        ‖(S).phasedSource w i (q, x)‖ ^ 2 ∂ν).re ∂μ) (currentTarget t) := by
  let j := D.direction t
  have hi (n : ℕ) : Integrable (fun x => ‖dψ n j x‖ ^ 2 +
      (∑' a, fderiv ℝ (f a) x (v j) ^ 2) * ‖ψ n x‖ ^ 2) ν :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp (dψ n j)).1).mp (Lp.memLp (dψ n j))).add
      (localizedSourceMetric_integrable f (v j) (fun a => hdf a j) (ψ n) (hmetric j))
  let hm (n a : ℕ) : MemLp (localizedDerivative f (dψ n j) (ψ n) (v j) a) 2 ν :=
    localizedDerivative_memLp f hloc hd hpos hpart hf (ψ n) (dψ n j) (v j)
      (fun a => hdf a j) (hi n) a
  have hk := localizedDerivativeVector_summable f hloc hd hpos hpart hf ψ (fun n => dψ n j)
    (v j) (fun a => hdf a j) hi hm (hmetric j) hmass.summable (hkinetic j)
  exact (D.current t).phased_current_hasSum f hpart hf (v j) hm hmass.summable hk
    w (fun i => s i j) hw

/- The hard-marginal source series is evaluated on the actual phased
L² sections. Norm bounds and local tested identities are proved from the
ordinary rank-one trace data and universal original hard tests. -/
include D in
theorem OriginalSourceTests.marginal_source
    [IsSeparable ν] [TopologicalSpace.SeparableSpace K]
    (w : ℕ → Q × X → ℂ) (hwm : ∀ i, StronglyMeasurable (w i))
    (hw : ∀ i qx, ‖w i qx‖ = 1) :
    HasSum (fun i => productSourceMarginal (μ := μ) R marginal ((S).phasedSource w i)) hardTarget := by
  have hΦ (i : ℕ) : StronglyMeasurable ((S).phasedSource w i) :=
    (S).phasedSource_stronglyMeasurable w hwm i
  have hm (i : ℕ) : MemLp ((S).phasedSource w i) 2 (μ.prod ν) :=
    (Lp.memLp ((S).source i)).smul
      (memLp_top_of_bound (hwm i).aestronglyMeasurable 1
        (Eventually.of_forall (fun qx => (hw i qx).le)))
  apply ProductTestData.marginal_hasSum hardTarget D.hardTests D.hard f hpart hf hmass
    (fun i => productSourceMarginal (μ := μ) R marginal ((S).phasedSource w i)) D.separating ‖marginal‖
  · intro i
    have hb := productSourceMarginal_norm_le R marginal (hΦ i) (hm i)
    have he : (∫ qx, ‖(S).phasedSource w i qx‖ ^ 2 ∂μ.prod ν) =
        ‖localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2‖ ^ 2 := by
      simp only [ConditionedSource.phasedSource, norm_smul, hw, one_mul]
      rw [← lp_norm_sq]
      exact congrArg (fun r : ℝ => r ^ 2) (U.norm_map _)
    exact hb.trans_eq (congrArg (fun r : ℝ => ‖marginal‖ * r) he)
  · intro t i
    let a := (hm i).toLp ((S).phasedSource w i)
    have hi : Integrable (fun qx => inner ℂ ((S).phasedSource w i qx)
        ((D.hard t).targetMultiplier qx ((S).phasedSource w i qx))) (μ.prod ν) := by
      have hbase := fiber_quadratic_integrable (D.hard t).targetMultiplier
        (D.hard t).target_bounded a ((D.hard t).target_measurable a)
      apply hbase.congr
      filter_upwards [(hm i).coeFn_toLp] with qx hqx
      change inner ℂ ((hm i).toLp _ qx)
        ((D.hard t).targetMultiplier qx ((hm i).toLp _ qx)) = _
      rw [hqx]
    rw [productSourceMarginal_test R marginal (D.hardTests t) (D.hard t).targetMultiplier
      (D.hard_rankOne t) (hΦ i) (hm i) hi]
    congr 1
    apply integral_congr_ae
    filter_upwards with q
    apply integral_congr_ae
    filter_upwards with x
    exact phaseSource_test (w i (q, x)) (hw i (q, x))
      (localizedFiber U f hpart hf ψ i (q, x)) ((D.hard t).targetMultiplier (q, x))

end Localized
end GptLean.RemovalSource
