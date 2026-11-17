import PfHk.SpatialFieldParameterDerivative

noncomputable section
namespace PfHk.SpatialFieldParameterDerivative

open MeasureTheory GptLean GptLean.PhysicalFock
open scoped ENNReal
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
attribute [local irreducible] kernelField

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  (C : CanonicalSectorCCR photonMeasure)

theorem spatialField_opNorm_le (a : X → WeightedPhotonKernel)
    (ha : AEStronglyMeasurable a μ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂μ, ‖a x‖ ≤ M) :
    ‖spatialField μ C a ha M hbound‖ ≤ 3 * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hM)
  intro q
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [spatialField_ae μ C a ha M hbound q, hbound] with x hx hb
  calc
    ‖spatialField μ C a ha M hbound q x‖ = ‖kernelField C (a x) (q x)‖ := congrArg norm hx
    _ ≤ 3 * ‖a x‖ * ‖q x‖ := field_norm_le_graph C (a x) (q x)
    _ ≤ 3 * M * ‖q x‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (by norm_num)) (norm_nonneg _)

end PfHk.SpatialFieldParameterDerivative
