import PfHk.SpatialFieldParameterDerivative
import PfHk.L2ParameterContinuity

/-! Strong continuity of actual spatial Segal fields from continuous
weighted kernels and a local uniform kernel bound. -/

noncomputable section
namespace PfHk.SpatialFieldParameterDerivative

open MeasureTheory Filter GptLean.PhysicalFock
open scoped ENNReal Topology

set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true

variable (C : CanonicalSectorCCR photonMeasure)
  {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem spatialField_continuousAt
    (a : ℝ → X → WeightedPhotonKernel)
    (ha : ∀ s, AEStronglyMeasurable (a s) μ)
    (M : ℝ → ℝ) (hM : ∀ s, ∀ᵐ x ∂μ, ‖a s x‖ ≤ M s)
    (q : SpatialRadiationGraph μ) (t D : ℝ)
    (hc : ∀ᵐ x ∂μ, ContinuousAt (fun s => a s x) t)
    (hb : ∀ᶠ s in 𝓝 t, ∀ᵐ x ∂μ, ‖a s x‖ ≤ D) :
    ContinuousAt (fun s => fieldValue C μ (a s) (ha s) (M s) (hM s) q) t := by
  apply L2ParameterContinuity.continuousAt_of_norm_bound (C := 3*D) q
    (φ := fun s x => kernelField C (a s x) (q x))
  · intro s
    unfold fieldValue
    exact spatialField_ae μ C (a s) (ha s) (M s) (hM s) q
  · filter_upwards [hc] with x hx
    exact ((kernelField_continuous C).continuousAt.comp hx).clm_apply continuousAt_const
  · filter_upwards [hb] with s hs
    filter_upwards [hs] with x hx
    exact (field_norm_le_graph C (a s x) (q x)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 3)) (norm_nonneg _))

end PfHk.SpatialFieldParameterDerivative
