import PfHk.RadialGaugeRadiationIntegral
import PfHk.RadialGaugeRadiationPhysical
import PfHk.RadialGaugeEnergyContinuity
import PfHk.PhysicalSphereSpace
import PfHk.IntegratedFormBounds

/-! The radiation form and its derivative on the genuine sphere Hilbert
space. All measurability, integrability and parameter-differentiation
conditions are discharged for the physical radial Weyl label. -/

noncomputable section
namespace PfHk.SphereRadiationEnergy

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.RadialGauge PfHk.PolarCalculus PfHk.SphereAngularField
open scoped ENNReal Topology InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 500000
attribute [local irreducible] radiationGraphInclusion radiationGraphDerivative
  inverseSqrtLabel inverseSqrtDerivative RadialGauge.radiationForm
  radiationFormDerivative sqrtLabel energyRay

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)

def label (t : ℝ) (θ : Sphere N) : Lp ℂ 2 photonMeasure :=
  inverseSqrtLabel F χ hUV e (Real.exp (-t) • θ.val)

def labelDerivative (t : ℝ) (θ : Sphere N) : Lp ℂ 2 photonMeasure :=
  inverseSqrtDerivative F χ hUV e θ.val t

theorem radiationConstant_nonneg : 0 ≤ radiationConstant (N := N) F χ hUV e := by
  have h := (norm_nonneg _).trans (omegaKernel_uniform_bound F χ hUV 0 0)
  unfold radiationConstant
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) h

theorem label_measurable (t : ℝ) :
    AEStronglyMeasurable (label (N := N) F χ hUV e t) (sphereMeasure (Fin N × Fin 3)) := by
  have harg : Continuous (fun θ : Sphere N => Real.exp (-t) • θ.val) :=
    (continuous_const : Continuous (fun _ : Sphere N => Real.exp (-t))).smul
      (continuous_subtype_val : Continuous (fun θ : Sphere N => (θ.val : Configuration N)))
  have h := (continuous_const : Continuous (fun _ : Sphere N => -Complex.I)).smul
    ((sqrtLabel_continuous F χ hUV e).comp harg)
  unfold label inverseSqrtLabel
  convert! (h.aestronglyMeasurable (μ := sphereMeasure (Fin N × Fin 3))) using 1

theorem labelDerivative_measurable (t : ℝ) :
    AEStronglyMeasurable (labelDerivative (N := N) F χ hUV e t)
      (sphereMeasure (Fin N × Fin 3)) := by
  have h : Continuous (fun θ : Sphere N => energyComponent true
      (energyRay F χ hUV e θ.val (Real.exp (-t)))) := (energyComponent true).continuous.comp
    ((energyRay_continuous_theta F χ hUV e (Real.exp (-t))).comp continuous_subtype_val)
  have hc := ((continuous_const : Continuous (fun _ : Sphere N => -Complex.I)).smul
    ((continuous_const : Continuous (fun _ : Sphere N => -Real.exp (-t))).smul h))
  unfold labelDerivative inverseSqrtDerivative
  convert! (hc.aestronglyMeasurable (μ := sphereMeasure (Fin N × Fin 3))) using 1

theorem label_norm_le (t : ℝ) (θ : Sphere N) :
    ‖label F χ hUV e t θ‖ ≤ Real.exp (-t) * radiationConstant (N := N) F χ hUV e := by
  have h := sqrtLabel_smul_norm_le F χ hUV e θ.val (Real.exp (-t))
  simp only [unitSphere_norm, mul_one, abs_of_pos (Real.exp_pos _)] at h
  unfold label inverseSqrtLabel
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  exact h

theorem labelDerivative_norm_le (t : ℝ) (θ : Sphere N) :
    ‖labelDerivative F χ hUV e t θ‖ ≤ Real.exp (-t) * radiationConstant (N := N) F χ hUV e := by
  have h := inverseSqrtDerivative_bound F χ hUV e θ.val t
  simpa only [labelDerivative, unitSphere_norm, mul_one, one_mul, mul_comm] using h

def energy (q : SphereRadiation N) (t : ℝ) : ℝ :=
  ∫ θ : Sphere N, RadialGauge.radiationForm F χ hUV e (Real.exp (-t) • θ.val) (q θ)
    ∂sphereMeasure (Fin N × Fin 3)

def formDerivative (q : SphereRadiation N) (t : ℝ) : ℝ :=
  ∫ θ : Sphere N, radiationFormDerivative F χ hUV e θ.val t (q θ)
    ∂sphereMeasure (Fin N × Fin 3)

theorem fiber_energy_integrable (q : SphereRadiation N) (t : ℝ) :
    Integrable (fun θ : Sphere N =>
      RadialGauge.radiationForm F χ hUV e (Real.exp (-t) • θ.val) (q θ))
      (sphereMeasure (Fin N × Fin 3)) := by
  unfold RadialGauge.radiationForm
  exact RadialGaugeRadiation.energy_integrable (label F χ hUV e t) q
    (label_measurable F χ hUV e t) (ae_of_all _ (label_norm_le F χ hUV e t))

theorem energy_nonneg (q : SphereRadiation N) (t : ℝ) : 0 ≤ energy F χ hUV e q t := by
  unfold energy RadialGauge.radiationForm
  exact integral_nonneg fun θ => RadialGaugeRadiation.energy_nonneg _ (q θ)

theorem derivative_and_integrability (q : SphereRadiation N) (t : ℝ) :
    Integrable (fun θ : Sphere N => radiationFormDerivative F χ hUV e θ.val t (q θ))
      (sphereMeasure (Fin N × Fin 3)) ∧
    HasDerivAt (energy F χ hUV e q) (formDerivative F χ hUV e q t) t := by
  have hlocal (s : ℝ) (hs : s ∈ Set.Ioo (t - 1) (t + 1)) :
      Real.exp (-s) * radiationConstant (N := N) F χ hUV e ≤
        Real.exp (1 - t) * radiationConstant (N := N) F χ hUV e :=
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hs.1]))
      (radiationConstant_nonneg F χ hUV e)
  have h := RadialGaugeRadiation.integral_energy_hasDerivAt
    (label F χ hUV e) (labelDerivative F χ hUV e) q
    (label_measurable F χ hUV e) (labelDerivative_measurable F χ hUV e) t
    (Real.exp (1 - t) * radiationConstant (N := N) F χ hUV e)
    (Real.exp (1 - t) * radiationConstant (N := N) F χ hUV e)
    (ae_of_all _ fun θ s hs => (label_norm_le F χ hUV e s θ).trans (hlocal s hs))
    (ae_of_all _ fun θ s hs => (labelDerivative_norm_le F χ hUV e s θ).trans (hlocal s hs))
    (ae_of_all _ fun θ s _ => inverseSqrtLabel_hasDerivAt F χ hUV e θ.val s)
  unfold energy formDerivative RadialGauge.radiationForm radiationFormDerivative
  simpa only [label, labelDerivative] using h

theorem energy_hasDerivAt (q : SphereRadiation N) (t : ℝ) :
    HasDerivAt (energy F χ hUV e q) (formDerivative F χ hUV e q t) t :=
  (derivative_and_integrability F χ hUV e q t).2

theorem formDerivative_sq_le (q : SphereRadiation N) (t : ℝ) :
    (formDerivative F χ hUV e q t) ^ 2 ≤
      (3 * radiationConstant (N := N) F χ hUV e) ^ 2 * Real.exp (-t) ^ 2 *
        energy F χ hUV e q t *
          ∫ θ : Sphere N, ‖radiationGraphInclusion (q θ)‖ ^ 2
            ∂sphereMeasure (Fin N × Fin 3) := by
  have hM : Integrable (fun θ : Sphere N => ‖radiationGraphInclusion (q θ)‖ ^ 2)
      (sphereMeasure (Fin N × Fin 3)) :=
    ((radiationGraphInclusion.comp_memLp q).norm).integrable_sq
  exact IntegratedFormBounds.integrated_radiation_bound
    (C := 3 * radiationConstant (N := N) F χ hUV e) (r := Real.exp (-t))
    (derivative_and_integrability F χ hUV e q t).1
    (fiber_energy_integrable F χ hUV e q t) hM
    (ae_of_all _ fun θ => by
      unfold RadialGauge.radiationForm
      exact RadialGaugeRadiation.energy_nonneg _ (q θ))
    (ae_of_all _ fun _ => sq_nonneg _)
    (ae_of_all _ fun θ => by
      have h := radiationFormDerivative_sq_le F χ hUV e θ.val t (q θ)
      simp only [unitSphere_norm, one_pow, mul_one] at h
      have hT : 0 ≤ RadialGauge.radiationForm F χ hUV e (Real.exp (-t) • θ.val) (q θ) := by
        unfold RadialGauge.radiationForm
        exact RadialGaugeRadiation.energy_nonneg _ (q θ)
      have hp : 0 ≤ radiationConstant (N := N) F χ hUV e ^ 2 * Real.exp (-t) ^ 2 *
          RadialGauge.radiationForm F χ hUV e (Real.exp (-t) • θ.val) (q θ) *
          ‖radiationGraphInclusion (q θ)‖ ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hT) (sq_nonneg _)
      nlinarith only [h, hp])

end PfHk.SphereRadiationEnergy
