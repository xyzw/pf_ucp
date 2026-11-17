import PfHk.CenteredSphereAngularEnergy
import PfHk.CenteredSphereRadiationEnergy
import PfHk.CarlemanWeightDerivatives
import PfHk.CylinderCarleman

/-! Uniform absorption of the actual angular and radiation form
derivatives on a sufficiently small physical cylinder. -/

noncomputable section
namespace PfHk.CenteredPhysicalCylinderBounds

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.CenteredRadialGauge PfHk.PolarCalculus PfHk.CenteredSphereAngularField
open PfHk.SphereAngularField (Sphere SpherePhoton SphereRadiation)
open PfHk.RadialGauge (curvatureConstant curvatureConstant_nonneg)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
local instance : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] CenteredSphereAngularField.energy CenteredSphereAngularField.formDerivative
  CenteredSphereRadiationEnergy.energy CenteredSphereRadiationEnergy.formDerivative radiationGraphInclusion

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)

def angularConstant : ℝ :=
  5 * (Fintype.card (Fin N × Fin 3) + 1) * curvatureConstant (N := N) F χ hUV e

def commonConstant : ℝ :=
  angularConstant (N := N) F χ hUV e + 3 * radiationConstant (N := N) F χ hUV e

def mass (q : SphereRadiation N) : ℝ :=
  ∫ θ : Sphere N, ‖radiationGraphInclusion (q θ)‖ ^ 2 ∂sphereMeasure (Fin N × Fin 3)

theorem mass_nonneg (q : SphereRadiation N) : 0 ≤ mass q :=
  integral_nonneg fun _ => sq_nonneg _

theorem mass_eq_norm_sq (q : SphereRadiation N) :
    mass q = ‖spatialRadiationInclusion (sphereMeasure (Fin N × Fin 3)) q‖ ^ 2 := by
  have hi : spatialRadiationInclusion (sphereMeasure (Fin N × Fin 3)) q =ᵐ[
      sphereMeasure (Fin N × Fin 3)] fun θ => radiationGraphInclusion (q θ) :=
    radiationGraphInclusion.coeFn_compLpL q
  have hn := PhotonKernelLocalization.l2_norm_sq_eq_integral
    (spatialRadiationInclusion (sphereMeasure (Fin N × Fin 3)) q)
  exact (hn.trans (integral_congr_ae (hi.mono fun _ h => congrArg (fun v => ‖v‖ ^ 2) h))).symm

theorem constants_nonneg : 0 ≤ angularConstant (N := N) F χ hUV e ∧
    0 ≤ 3 * radiationConstant (N := N) F χ hUV e := by
  constructor
  · unfold angularConstant
    exact mul_nonneg (by positivity) (curvatureConstant_nonneg F χ hUV e)
  · exact mul_nonneg (by norm_num) (CenteredSphereRadiationEnergy.radiationConstant_nonneg F χ hUV e)

/-- A single half-cylinder absorbs both physical derivative errors at every
configuration-space center, uniformly over all angular and photon vectors. -/
theorem exists_uniform_cylinder (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (α : ℝ) (hα : 0 < α) :
    ∃ t₀ : ℝ, 2 ≤ t₀ ∧ ∀ (τ t : ℝ), 9 ≤ τ → t₀ ≤ t →
      ∀ (O : Configuration N) (p : (Fin N × Fin 3) → SpherePhoton N) (q : SphereRadiation N),
      |CenteredSphereAngularField.formDerivative F χ hUV e O C p q t| ≤
        CarlemanWeights.beta α t / 16 * CenteredSphereAngularField.energy F χ hUV e O C p q t +
        Real.exp (-2 * t) / 16 * CenteredSphereRadiationEnergy.energy F χ hUV e O q t +
        τ ^ 2 * CarlemanWeights.beta α t / 16 * mass q ∧
      Real.exp (-2 * t) * |CenteredSphereRadiationEnergy.formDerivative F χ hUV e O q t| ≤
        Real.exp (-2 * t) / 8 * CenteredSphereRadiationEnergy.energy F χ hUV e O q t +
        τ ^ 2 * CarlemanWeights.beta α t / 16 * mass q := by
  obtain ⟨t₀, ht₀, hsmall⟩ := CarlemanWeights.exists_cylinder_small α
    (commonConstant (N := N) F χ hUV e) hα
  refine ⟨t₀, ht₀, ?_⟩
  intro τ t hτ ht O p q
  obtain ⟨ha, hr⟩ := constants_nonneg (N := N) F χ hUV e
  have hc : 0 ≤ commonConstant (N := N) F χ hUV e := add_nonneg ha hr
  have haC : angularConstant (N := N) F χ hUV e ≤ commonConstant (N := N) F χ hUV e :=
    le_add_of_nonneg_right hr
  have hrC : 3 * radiationConstant (N := N) F χ hUV e ≤ commonConstant (N := N) F χ hUV e :=
    le_add_of_nonneg_left ha
  have hβ := (CarlemanWeights.beta_pos hα (by linarith : 0 < t)).le
  have hK := CenteredSphereAngularField.energy_nonneg F χ hUV e O C p q t
  have hT := CenteredSphereRadiationEnergy.energy_nonneg F χ hUV e O q t
  have hM := mass_nonneg q
  have heq : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have heq₄ : Real.exp (-t) ^ 4 = Real.exp (-2 * t) ^ 2 := by
    rw [← heq]
    ring
  have hk := CenteredSphereAngularField.formDerivative_sq_le F χ hUV e O C W p q t
    (CenteredSphereRadiationEnergy.fiber_energy_integrable F χ hUV e O q t)
  have hq := CenteredSphereRadiationEnergy.formDerivative_sq_le F χ hUV e O q t
  rw [heq₄] at hk
  rw [heq] at hq
  have hka := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha haC 2)
    (show 0 ≤ Real.exp (-2 * t) ^ 2 * CenteredSphereAngularField.energy F χ hUV e O C p q t *
      (CenteredSphereRadiationEnergy.energy F χ hUV e O q t + mass q) by positivity)
  have hqa := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hrC 2)
    (show 0 ≤ Real.exp (-2 * t) * CenteredSphereRadiationEnergy.energy F χ hUV e O q t * mass q by positivity)
  have hk' : (CenteredSphereAngularField.formDerivative F χ hUV e O C p q t) ^ 2 ≤
      commonConstant (N := N) F χ hUV e ^ 2 * Real.exp (-2 * t) ^ 2 *
      CenteredSphereAngularField.energy F χ hUV e O C p q t *
      (CenteredSphereRadiationEnergy.energy F χ hUV e O q t + mass q) := by
    unfold angularConstant at hka
    unfold CenteredSphereRadiationEnergy.energy mass at hka ⊢
    nlinarith only [hk, hka]
  have hq' : (CenteredSphereRadiationEnergy.formDerivative F χ hUV e O q t) ^ 2 ≤
      commonConstant (N := N) F χ hUV e ^ 2 * Real.exp (-2 * t) *
      CenteredSphereRadiationEnergy.energy F χ hUV e O q t * mass q := by
    unfold mass at hqa ⊢
    nlinarith only [hq, hqa]
  obtain ⟨hbsmall, hcsmall⟩ := hsmall t ht
  have hrone : Real.exp (-2 * t) ≤ 1 :=
    (Real.exp_le_one_iff).mpr (by linarith)
  constructor
  · exact CylinderCarleman.angular_error_bound (Real.exp_pos _).le hβ (by linarith)
      hK hT hM hbsmall hcsmall hk'
  · exact CylinderCarleman.radiation_error_bound (Real.exp_pos _).le hrone hβ (by linarith)
      hT hM hcsmall hq'

end PfHk.CenteredPhysicalCylinderBounds
