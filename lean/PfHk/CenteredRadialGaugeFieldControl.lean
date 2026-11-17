import PfHk.CenteredRadialGaugeRadiation
import PfHk.CenteredRadialGauge
import GptLean.WeylFormDisplacement

/-! The physical curvature fields are controlled by the conjugated
radiation form, with no extra displacement-energy error. The reason is
the proved real-family Weyl commutation, used here on the closed graph. -/

noncomputable section
namespace PfHk.CenteredRadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalWeyl
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  PfHk.PhysicalFieldRegularity
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 600000
attribute [local irreducible] radiationGraphDerivative radiationGraphInclusion
  weylWeightedGraph kernelField unitary inverseRadiationGraph radiationForm

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ) (O : Configuration N)

/-- Exact commutation on the inverse gauge's closed radiation graph. -/
theorem inverse_real_field_covariance (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (X : Configuration N) (k : WeightedPhotonKernel)
    (hk : F.conjugation k.val.1 = k.val.1) (q : RadiationGraphSpace) :
    kernelField C k (inverseRadiationGraph F χ hUV e O W X q) =
      W.weyl (inverseLabel F χ e O X) (kernelField C k q) := by
  have hi : (⟪k.val.1, (label F χ e O X).val.1⟫_ℂ).im = 0 :=
    realStructure_fixed_inner_im photonMeasure F.realStructure
      ⟨_, (F.realStructure.mem_fixedSpace _).mpr hk⟩
      ⟨_, (F.realStructure.mem_fixedSpace _).mpr (label_fixed F χ e O X)⟩
  have h := kernelField_weylWeightedGraph W (inverseLabel F χ e O X)
    (inverseSqrtLabel F χ hUV e O X) (inverseSqrtLabel_relation F χ hUV e O X) C k q
  have hr : (⟪k.val.1, inverseLabel F χ e O X⟫_ℂ).re = 0 := by
    simp only [inverseLabel, inner_smul_right, Complex.mul_re, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im, neg_zero, zero_mul, hi, mul_zero, sub_zero]
  simpa only [inverseRadiationGraph, hr, mul_zero, Complex.ofReal_zero, zero_smul, add_zero] using h

theorem inverse_real_field_norm (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (X : Configuration N) (k : WeightedPhotonKernel)
    (hk : F.conjugation k.val.1 = k.val.1) (q : RadiationGraphSpace) :
    ‖kernelField C k (inverseRadiationGraph F χ hUV e O W X q)‖ = ‖kernelField C k q‖ := by
  rw [inverse_real_field_covariance F χ hUV e O C W X k hk q]
  exact (W.weyl (inverseLabel F χ e O X)).norm_map _

/-- The field estimate uses the exact radiation form that appears in the
cylinder operator. The bound is uniform in the radial Weyl label. -/
theorem real_field_sq_le_radiationForm (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (X : Configuration N) (k : WeightedPhotonKernel)
    (hk : F.conjugation k.val.1 = k.val.1) (q : RadiationGraphSpace) :
    ‖kernelField C k q‖ ^ 2 ≤ 5 * ‖k‖ ^ 2 *
      (radiationForm F χ hUV e O X q + ‖radiationGraphInclusion q‖ ^ 2) := by
  have h := RadialGauge.fieldEvaluation_sq_le C k (inverseRadiationGraph F χ hUV e O W X q)
  rw [inverse_real_field_norm F χ hUV e O C W X k hk q] at h
  have hrad := radiationForm_eq F χ hUV e O W X q
  have hval : ‖radiationGraphInclusion (inverseRadiationGraph F χ hUV e O W X q)‖ =
      ‖radiationGraphInclusion q‖ := by
    rw [inverseRadiationGraph_inclusion F χ hUV e O W X q]
    exact (unitary F χ e O W X).symm.norm_map _
  rw [hval] at h
  have hpos := mul_nonneg (sq_nonneg ‖k‖)
    (sq_nonneg ‖radiationGraphDerivative (inverseRadiationGraph F χ hUV e O W X q)‖)
  rw [hrad]
  nlinarith only [h, hpos]

end PfHk.CenteredRadialGauge
