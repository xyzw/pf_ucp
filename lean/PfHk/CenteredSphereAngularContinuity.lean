import PfHk.CenteredSphereFormProductRules
import PfHk.SpatialFieldParameterContinuity
import PfHk.SphereCoreGeometry
import PfHk.L2StrongContinuity

/-! Continuity of the actual angular coefficient derivative and of its
quadratic form along genuine sphere core curves. -/

noncomputable section
namespace PfHk.CenteredSphereAngularField

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.CenteredRadialGauge PfHk.PolarCalculus PfHk.SphereCoreGeometry
open PfHk.SphereAngularField (Sphere SpherePhoton SphereRadiation)
open PfHk.RadialGauge (curvatureConstant curvatureConstant_nonneg)
open scoped ENNReal Topology InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

local instance angularContinuityPhotonReal : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
local instance angularContinuityRadiationComplex : NormedSpace ℂ RadiationGraphSpace := radiationRoot.graph.normedSpace
local instance angularContinuityRadiationReal : NormedSpace ℝ RadiationGraphSpace :=
  NormedSpace.restrictScalars ℝ ℂ _
attribute [local irreducible] field fieldDerivative angularVector formDerivative

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)

theorem derivativeCoefficient_continuous (j : Fin N × Fin 3) (θ : Sphere N) :
    Continuous (fun t => derivativeCoefficient F χ hUV e O j t θ) := by
  have hr : Continuous (fun t : ℝ => Real.exp (-t)) := Real.continuous_exp.comp continuous_neg
  unfold derivativeCoefficient
  exact (hr.pow 2).neg.smul
    ((curvature_continuous F χ hUV e O θ.val (EuclideanSpace.single j 1)).comp
      (hr.smul continuous_const))

theorem derivativeCoefficient_local_bound (j : Fin N × Fin 3) (t : ℝ) :
    ∀ᶠ s in 𝓝 t, ∀ᵐ θ ∂sphereMeasure (Fin N × Fin 3),
      ‖derivativeCoefficient F χ hUV e O j s θ‖ ≤
        Real.exp (4-2*t) * curvatureConstant (N := N) F χ hUV e := by
  filter_upwards [Ioo_mem_nhds (by linarith : t-1<t) (by linarith : t<t+1)] with s hs
  filter_upwards [derivativeCoefficient_bound F χ hUV e O j s] with θ hθ
  exact hθ.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by linarith [hs.1])) (curvatureConstant_nonneg F χ hUV e))

theorem fieldDerivative_continuousAt (j : Fin N × Fin 3) (q : SphereRadiation N) (t : ℝ) :
    ContinuousAt (fun s => fieldDerivative F χ hUV e O C j s q) t := by
  unfold fieldDerivative
  exact SpatialFieldParameterDerivative.spatialField_continuousAt C _
    (derivativeCoefficient F χ hUV e O j) (derivativeCoefficient_measurable F χ hUV e O j)
    (localDerivativeBound (N := N) F χ hUV e) (derivativeCoefficient_bound F χ hUV e O j)
    q t (Real.exp (4-2*t) * curvatureConstant (N := N) F χ hUV e)
    (ae_of_all _ fun θ => (derivativeCoefficient_continuous F χ hUV e O j θ).continuousAt)
    (derivativeCoefficient_local_bound F χ hUV e O j t)

theorem fieldDerivative_local_opNorm_le (j : Fin N × Fin 3) (t : ℝ) :
    ∀ᶠ s in 𝓝 t, ‖fieldDerivative F χ hUV e O C j s‖ ≤
      3 * (Real.exp (4-2*t) * curvatureConstant (N := N) F χ hUV e) := by
  filter_upwards [Ioo_mem_nhds (by linarith : t-1<t) (by linarith : t<t+1)] with s hs
  have hb : ‖fieldDerivative F χ hUV e O C j s‖ ≤
      3 * localDerivativeBound (N := N) F χ hUV e s := by
    unfold fieldDerivative
    exact SpatialFieldParameterDerivative.spatialField_opNorm_le _ C _ _ _
      (mul_nonneg (Real.exp_pos _).le (curvatureConstant_nonneg F χ hUV e)) _
  exact hb.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hs.1]))
      (curvatureConstant_nonneg F χ hUV e)) (by norm_num))

theorem fieldDerivative_moving_continuousAt (j : Fin N × Fin 3)
    {q : ℝ → SphereRadiation N} {t : ℝ} (hq : ContinuousAt q t) :
    ContinuousAt (fun s => fieldDerivative F χ hUV e O C j s (q s)) t := by
  exact L2StrongContinuity.apply_complex
    (fun v => fieldDerivative_continuousAt F χ hUV e O C j v t)
    (fieldDerivative_local_opNorm_le F χ hUV e O C j t) hq

set_option maxHeartbeats 100000 in
theorem formDerivative_core_continuous (u : CoreCurve N) :
    Continuous (fun t => formDerivative F χ hUV e O C
      (u.value t).gradient (u.value t).radiation t) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hq : ContinuousAt (fun s => (u.value s).radiation) t :=
    L2StrongContinuity.of_deriv (E := RadiationGraphSpace)
      (μ := sphereMeasure (Fin N × Fin 3)) (u.radiation_hasDerivAt t)
  have ha (j : Fin N × Fin 3) : ContinuousAt
      (fun s => angularVector F χ hUV e O C (u.value s).gradient (u.value s).radiation j s) t := by
    unfold angularVector
    exact (L2StrongContinuity.of_deriv (E := PhotonFock)
      (μ := sphereMeasure (Fin N × Fin 3)) (u.gradient_hasDerivAt j t)).add
      ((L2StrongContinuity.of_deriv (E := PhotonFock) (μ := sphereMeasure (Fin N × Fin 3))
        (field_moving_hasDerivAt F χ hUV e O C j (u.radiation_hasDerivAt t))).const_smul Complex.I)
  unfold formDerivative
  exact tendsto_finsetSum _ fun j _ => continuousAt_const.mul
    ((ha j).inner ((fieldDerivative_moving_continuousAt F χ hUV e O C j hq).const_smul Complex.I))

end PfHk.CenteredSphereAngularField
