import PfHk.RadialGaugeAngular
import PfHk.CenteredRadialGaugeFieldControl

/-! The angular derivative bound with the actual conjugated radiation
energy. Strong real-field commutation removes every radial-displacement
error from this estimate. -/

noncomputable section
namespace PfHk.CenteredRadialGaugeAngular

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalWeyl GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.CenteredRadialGauge PfHk.RadialGaugeAngular
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 600000
attribute [local irreducible] radiationGraphDerivative radiationGraphInclusion
  kernelField energy formDerivative CenteredRadialGauge.radiationForm

variable {ι : Type*} [Fintype ι] {N : ℕ}
  (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ) (O : Configuration N)
  (C : CanonicalSectorCCR photonMeasure) (W : ConcreteWeylLaw photonMeasure)

def physicalLabels (θ : Configuration N) (ζ : ι → Configuration N) (t : ℝ) :
    ι → WeightedPhotonKernel :=
  fun j => angularLabel F χ hUV e O θ (ζ j) (Real.exp (-t))

def physicalLabelDerivatives (θ : Configuration N) (ζ : ι → Configuration N) (t : ℝ) :
    ι → WeightedPhotonKernel :=
  fun j => (-(Real.exp (-t) ^ 2)) •
    curvature F χ hUV e O (Real.exp (-t) • θ) θ (ζ j)

include W

theorem formDerivative_sq_le_gauged (X : Configuration N)
    (a da : ι → WeightedPhotonKernel)
    (hda : ∀ j, F.conjugation (da j).val.1 = (da j).val.1)
    (q : RadiationGraphSpace) (v : ι → PhotonFock) :
    (formDerivative C a da q v) ^ 2 ≤
      20 * (∑ j, ‖da j‖ ^ 2) * energy C a q v *
        (CenteredRadialGauge.radiationForm F χ hUV e O X q + ‖radiationGraphInclusion q‖ ^ 2) := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun j _ => real_field_sq_le_radiationForm F χ hUV e O C W X (da j) (hda j) q)
  have hm := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (energy_nonneg C a q v))
  have h := (formDerivative_sq_le C a da q v).trans hm
  exact h.trans_eq (by rw [← Finset.sum_mul, ← Finset.mul_sum]; ring)

/-- The physical angular error in precisely the form needed by the cylinder
estimate. This uses `T = 2 U H_rad U*`, not the original radiation form. -/
theorem physical_formDerivative_sq_le_gauged (θ : Configuration N)
    (ζ : ι → Configuration N) (t : ℝ) (q : RadiationGraphSpace) (v : ι → PhotonFock) :
    (formDerivative C (physicalLabels F χ hUV e O θ ζ t)
      (physicalLabelDerivatives F χ hUV e O θ ζ t) q v) ^ 2 ≤
    20 * Real.exp (-t) ^ 4 *
      (2 * Fintype.card (Fin N × Fin 3) * |e| * RadialGauge.momentBound F χ hUV) ^ 2 *
      ‖θ‖ ^ 2 * (∑ j, ‖ζ j‖ ^ 2) * energy C (physicalLabels F χ hUV e O θ ζ t) q v *
      (CenteredRadialGauge.radiationForm F χ hUV e O (Real.exp (-t) • θ) q + ‖radiationGraphInclusion q‖ ^ 2) := by
  have hreal (j : ι) : F.conjugation (physicalLabelDerivatives F χ hUV e O θ ζ t j).val.1 =
      (physicalLabelDerivatives F χ hUV e O θ ζ t j).val.1 :=
    real_smul_fixed F _ _ (curvature_fixed F χ hUV e O _ θ (ζ j))
  have h := formDerivative_sq_le_gauged F χ hUV e O C W (Real.exp (-t) • θ)
    (physicalLabels F χ hUV e O θ ζ t) (physicalLabelDerivatives F χ hUV e O θ ζ t) hreal q v
  have hnorm (j : ι) : ‖physicalLabelDerivatives F χ hUV e O θ ζ t j‖ ^ 2 ≤
      Real.exp (-t) ^ 4 *
        (2 * Fintype.card (Fin N × Fin 3) * |e| * RadialGauge.momentBound F χ hUV) ^ 2 *
        ‖θ‖ ^ 2 * ‖ζ j‖ ^ 2 := by
    have h₁ := pow_le_pow_left₀ (norm_nonneg _)
      (curvature_norm_le F χ hUV e O (Real.exp (-t) • θ) θ (ζ j)) 2
    unfold RadialGauge.curvatureConstant at h₁
    unfold physicalLabelDerivatives
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg _), mul_pow]
    exact (mul_le_mul_of_nonneg_left h₁ (sq_nonneg (Real.exp (-t) ^ 2))).trans_eq (by ring)
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun j _ => hnorm j)
  have hT : 0 ≤ CenteredRadialGauge.radiationForm F χ hUV e O (Real.exp (-t) • θ) q := by
    unfold CenteredRadialGauge.radiationForm
    exact RadialGaugeRadiation.energy_nonneg _ q
  have hm := mul_le_mul_of_nonneg_right hs (mul_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) (energy_nonneg C (physicalLabels F χ hUV e O θ ζ t) q v))
      (add_nonneg hT (sq_nonneg ‖radiationGraphInclusion q‖)))
  rw [← Finset.mul_sum] at hm
  nlinarith only [h, hm]

end PfHk.CenteredRadialGaugeAngular
