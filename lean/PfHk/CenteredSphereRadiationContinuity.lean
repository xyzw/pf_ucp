import PfHk.CenteredSphereRadiationProduct
import PfHk.SpatialBilinearContinuity
import PfHk.SphereCoreGeometry
import PfHk.L2StrongContinuity

/-! Continuity of the actual logarithmic radiation-form derivative.
Only the existing first ultraviolet moment is used. -/

noncomputable section
namespace PfHk.CenteredSphereRadiationEnergy

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalWeyl
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.CenteredRadialGauge PfHk.PolarCalculus PfHk.SphereCoreGeometry
open PfHk.SphereAngularField (Sphere SpherePhoton SphereRadiation)
open PfHk.RadialGauge (energyComponent)
open scoped ENNReal Topology InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

local instance radiationContinuityAnalysisReal : InnerProductSpace ℝ AnalysisSpace := InnerProductSpace.rclikeToReal ℂ _
local instance radiationContinuityGraphComplex : NormedSpace ℂ RadiationGraphSpace := radiationRoot.graph.normedSpace
local instance radiationContinuityGraphReal : NormedSpace ℝ RadiationGraphSpace :=
  NormedSpace.restrictScalars ℝ ℂ _
attribute [local irreducible] shiftDerivative analysis formDerivative tensorMap

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N)

set_option maxHeartbeats 100000 in
theorem labelDerivative_continuous (θ : Sphere N) :
    Continuous (fun t => labelDerivative F χ hUV e O t θ) := by
  have hr : Continuous (fun t : ℝ => Real.exp (-t)) := Real.continuous_exp.comp continuous_neg
  have he : Continuous (fun t : ℝ => energyComponent true
      (energyRay F χ hUV e O θ.val (Real.exp (-t)))) :=
    (energyComponent true).continuous.comp
      ((energyRay_continuous F χ hUV e O θ.val).comp hr)
  unfold labelDerivative inverseSqrtDerivative
  exact (hr.neg.smul he).const_smul (-Complex.I)

theorem labelDerivative_local_bound (t : ℝ) :
    ∀ᶠ s in 𝓝 t, ∀ᵐ θ ∂sphereMeasure (Fin N × Fin 3),
      ‖labelDerivative F χ hUV e O s θ‖ ≤
        Real.exp (2-t) * radiationConstant (N := N) F χ hUV e := by
  filter_upwards [Ioo_mem_nhds (by linarith : t-1<t) (by linarith : t<t+1)] with s hs
  exact ae_of_all _ fun θ => (labelDerivative_norm_le F χ hUV e O s θ).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hs.1]))
      (radiationConstant_nonneg F χ hUV e))

theorem shiftDerivative_continuousAt (q : SphereRadiation N) (t : ℝ) :
    ContinuousAt (fun s => shiftDerivative F χ hUV e O s q) t := by
  unfold shiftDerivative
  apply SpatialBilinearDerivative.operator_continuousAt _ tensorMap _ _ _ _ q t
    (Real.exp (2-t) * radiationConstant (N := N) F χ hUV e)
  · exact ae_of_all _ fun θ => (labelDerivative_continuous F χ hUV e O θ).continuousAt
  · exact labelDerivative_local_bound F χ hUV e O t

theorem shiftDerivative_local_opNorm_le (t : ℝ) :
    ∀ᶠ s in 𝓝 t, ‖shiftDerivative F χ hUV e O s‖ ≤
      Real.exp (2-t) * radiationConstant (N := N) F χ hUV e := by
  filter_upwards [Ioo_mem_nhds (by linarith : t-1<t) (by linarith : t<t+1)] with s hs
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Real.exp_pos _).le (radiationConstant_nonneg F χ hUV e))
  intro q
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [shiftDerivative_ae F χ hUV e O s q] with θ hθ
  have hinc : ‖radiationGraphInclusion (q θ)‖ ≤ ‖q θ‖ := by
    unfold radiationGraphInclusion
    exact norm_fst_le (q θ).val
  have hy : ‖labelDerivative F χ hUV e O s θ‖ ≤
      Real.exp (2-t) * radiationConstant (N := N) F χ hUV e :=
    (labelDerivative_norm_le F χ hUV e O s θ).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hs.1] : -s ≤ 2-t))
      (radiationConstant_nonneg F χ hUV e))
  calc
    _ = ‖labelDerivative F χ hUV e O s θ‖ * ‖radiationGraphInclusion (q θ)‖ :=
      (congrArg norm hθ).trans (coefficientTensor_norm _ _)
    _ ≤ _ := mul_le_mul hy hinc (norm_nonneg _)
      (mul_nonneg (Real.exp_pos _).le (radiationConstant_nonneg F χ hUV e))

theorem shiftDerivative_moving_continuousAt {q : ℝ → SphereRadiation N}
    {t : ℝ} (hq : ContinuousAt q t) :
    ContinuousAt (fun s => shiftDerivative F χ hUV e O s (q s)) t := by
  exact L2StrongContinuity.apply_complex
    (fun v => shiftDerivative_continuousAt F χ hUV e O v t)
    (shiftDerivative_local_opNorm_le F χ hUV e O t) hq

set_option maxHeartbeats 100000 in
theorem formDerivative_core_continuous (u : CoreCurve N) :
    Continuous (fun t => formDerivative F χ hUV e O (u.value t).radiation t) := by
  have h : Continuous (fun t => 4 * inner ℝ
      (analysis F χ hUV e O t (u.value t).radiation)
      (shiftDerivative F χ hUV e O t (u.value t).radiation)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact continuousAt_const.mul
      ((L2StrongContinuity.of_deriv (E := AnalysisSpace) (μ := sphereMeasure (Fin N × Fin 3))
        (analysis_moving_hasDerivAt F χ hUV e O (u.radiation_hasDerivAt t))).inner
        (shiftDerivative_moving_continuousAt F χ hUV e O
          (L2StrongContinuity.of_deriv (E := RadiationGraphSpace)
            (μ := sphereMeasure (Fin N × Fin 3)) (u.radiation_hasDerivAt t))))
  exact h.congr fun t => (formDerivative_eq_analysis F χ hUV e O t (u.value t).radiation).symm

end PfHk.CenteredSphereRadiationEnergy
