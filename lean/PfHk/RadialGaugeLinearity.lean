import PfHk.RadialGaugeConnection

/-! The physical radial connection as a continuous real-linear one-form.
This makes the tangent condition available to the ordinary polar calculus. -/

noncomputable section
namespace PfHk.RadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian PfHk.PhysicalFieldRegularity
open scoped ENNReal InnerProductSpace Interval

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)

theorem directionKernel_add (i : Fin 3) (v w x : FieldSpace) :
    directionKernel F χ hUV i (v + w) x =
      directionKernel F χ hUV i v x + directionKernel F χ hUV i w x := by
  apply WeightedPhotonKernel.ext_fst
  change (directionKernel F χ hUV i (v + w) x).val.1 =
    (directionKernel F χ hUV i v x).val.1 + (directionKernel F χ hUV i w x).val.1
  simp_rw [directionKernel_fst]
  apply Lp.ext
  filter_upwards [TransformationsKernelCovariance.fourierKernel_ae (directionFactors F χ hUV (v + w)) rfl i x,
    TransformationsKernelCovariance.fourierKernel_ae (directionFactors F χ hUV v) rfl i x,
    TransformationsKernelCovariance.fourierKernel_ae (directionFactors F χ hUV w) rfl i x,
    Lp.coeFn_add ((directionFactors F χ hUV v).fourierKernel (i, x))
      ((directionFactors F χ hUV w).fourierKernel (i, x))] with p hp hv hw hs
  rw [hs, Pi.add_apply, hp, hv, hw]
  change _ * directionBase Prod.fst (v + w) (base F χ i) p =
    _ * directionBase Prod.fst v (base F χ i) p + _ * directionBase Prod.fst w (base F χ i) p
  simp only [directionBase, inner_add_right, Complex.ofReal_add]
  ring

theorem couplingDerivative_add (j : Fin N × Fin 3) (v w X : Configuration N) :
    couplingDerivative F χ hUV e j (v + w) X =
      couplingDerivative F χ hUV e j v X + couplingDerivative F χ hUV e j w X := by
  change (-e) • directionKernel F χ hUV j.2 (particle v j.1 + particle w j.1) (particle X j.1) = _
  rw [directionKernel_add, smul_add]
  rfl

theorem curvature_add_right (X v w z : Configuration N) :
    curvature F χ hUV e X v (w + z) =
      curvature F χ hUV e X v w + curvature F χ hUV e X v z := by
  simp only [curvature, couplingDerivative_add, PiLp.add_apply, add_smul, smul_add,
    Finset.sum_add_distrib]
  module

theorem curvature_real_smul_right (X v w : Configuration N) (c : ℝ) :
    curvature F χ hUV e X v (c • w) = c • curvature F χ hUV e X v w := by
  rw [curvature_swap, curvature_real_smul_left, curvature_swap F χ hUV e X w v,
    smul_neg, neg_neg]

theorem radialConnection_add (X v w : Configuration N) :
    radialConnection F χ hUV e X (v + w) =
      radialConnection F χ hUV e X v + radialConnection F χ hUV e X w := by
  unfold radialConnection
  simp_rw [curvature_add_right, smul_add]
  exact intervalIntegral.integral_add
    ((angularIntegrand_continuous F χ hUV e X v).intervalIntegrable 0 1)
    ((angularIntegrand_continuous F χ hUV e X w).intervalIntegrable 0 1)

theorem radialConnection_real_smul (X v : Configuration N) (c : ℝ) :
    radialConnection F χ hUV e X (c • v) = c • radialConnection F χ hUV e X v := by
  unfold radialConnection
  simp_rw [curvature_real_smul_right, smul_comm _ c]
  exact intervalIntegral.integral_smul c _

/-- The actual connection is a continuous real-linear differential form. -/
def connectionMap (X : Configuration N) : Configuration N →L[ℝ] WeightedPhotonKernel :=
  LinearMap.toContinuousLinearMap
    { toFun := radialConnection F χ hUV e X
      map_add' := radialConnection_add F χ hUV e X
      map_smul' := fun c v => radialConnection_real_smul F χ hUV e X v c }

@[simp] theorem connectionMap_apply (X v : Configuration N) :
    connectionMap F χ hUV e X v = radialConnection F χ hUV e X v := rfl

/-- Cartesian component contraction gives zero in radial gauge. -/
theorem radialConnection_components (X : Configuration N) :
    (∑ j : Fin N × Fin 3, X j • radialConnection F χ hUV e X (EuclideanSpace.single j 1)) = 0 := by
  have hX : (∑ j : Fin N × Fin 3, X j • EuclideanSpace.single j 1) = X := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin N × Fin 3) ℝ).sum_repr X
  have h := congrArg (connectionMap F χ hUV e X) hX
  simpa only [map_sum, map_smul, connectionMap_apply, radialConnection_radial] using h



/-- The angular connection is tangent in the actual ambient Cartesian
components used for the sphere gradient. -/
theorem angularLabel_components (θ : Configuration N) (r : ℝ) :
    (∑ j : Fin N × Fin 3, θ j • angularLabel F χ hUV e θ (EuclideanSpace.single j 1) r) = 0 := by
  have hθ : (∑ j : Fin N × Fin 3, θ j • EuclideanSpace.single j 1) = θ := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin N × Fin 3) ℝ).sum_repr θ
  simp_rw [angularLabel_eq_radialConnection, smul_comm _ r]
  rw [← Finset.smul_sum]
  change r • (∑ j : Fin N × Fin 3, θ j • connectionMap F χ hUV e (r • θ) (EuclideanSpace.single j 1)) = 0
  simp_rw [← map_smul]
  rw [← map_sum, hθ, ← map_smul]
  exact radialConnection_radial F χ hUV e (r • θ)

end PfHk.RadialGauge
