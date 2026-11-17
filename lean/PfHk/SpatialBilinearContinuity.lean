import PfHk.SpatialBilinearDerivative
import PfHk.L2ParameterContinuity

/-! Strong continuity of spatial bilinear maps under pointwise kernel
continuity and a local uniform coefficient bound. -/

noncomputable section
namespace PfHk.SpatialBilinearDerivative

open MeasureTheory Filter
open scoped ENNReal Topology

set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {X K Q H : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  (B : K →L[ℂ] Q →L[ℂ] H)

theorem operator_continuousAt
    (a : ℝ → X → K) (ha : ∀ s, AEStronglyMeasurable (a s) μ)
    (M : ℝ → ℝ) (hM : ∀ s, ∀ᵐ x ∂μ, ‖a s x‖ ≤ M s)
    (q : Lp Q 2 μ) (t D : ℝ)
    (hc : ∀ᵐ x ∂μ, ContinuousAt (fun s => a s x) t)
    (hb : ∀ᶠ s in 𝓝 t, ∀ᵐ x ∂μ, ‖a s x‖ ≤ D) :
    ContinuousAt (fun s => operator μ B (a s) (ha s) (M s) (hM s) q) t := by
  apply L2ParameterContinuity.continuousAt_of_norm_bound (C := ‖B‖*D) q
    (φ := fun s x => B (a s x) (q x))
  · exact fun s => operator_ae μ B (a s) (ha s) (M s) (hM s) q
  · filter_upwards [hc] with x hx
    exact (B.continuous.continuousAt.comp hx).clm_apply continuousAt_const
  · filter_upwards [hb] with s hs
    filter_upwards [hs] with x hx
    exact ((B (a s x)).le_opNorm (q x)).trans
      (mul_le_mul_of_nonneg_right ((B.le_opNorm (a s x)).trans
        (mul_le_mul_of_nonneg_left hx (norm_nonneg _))) (norm_nonneg _))

end PfHk.SpatialBilinearDerivative
