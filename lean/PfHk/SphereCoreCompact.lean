import PfHk.SphereCoreWeight
import PfHk.CenteredSphereAngularContinuity
import PfHk.CenteredSphereRadiationContinuity
import PfHk.LogarithmicCompactSupport
import GptLean.PhysicalSpatialRadiationLocality

/-! Locality and compact support for genuine sphere core curves and
their scalar weights. -/

noncomputable section
namespace PfHk.SphereCoreGeometry
open MeasureTheory Set GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PolarCalculus PfHk.CarlemanWeights
open PfHk.SphereAngularField (SpherePhoton)
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
local instance coreCompactPhotonReal : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
local instance coreCompactAnalysisReal : InnerProductSpace ℝ CenteredSphereRadiationEnergy.AnalysisSpace :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] CoreVector.ambient CoreVector.scale CoreVector.add
  CoreCurve.ambient CoreCurve.firstAmbient CoreCurve.exponential CoreCurve.scalar

variable {N : ℕ}

theorem CoreVector.radiation_zero_of_ambient (v : CoreVector N) (hv : v.ambient = 0) :
    v.radiation = 0 := by
  unfold CoreVector.ambient at hv
  exact spatialRadiation_injective (sphereMeasure (Fin N × Fin 3))
    (hv.trans ((map_zero (spatialRadiationInclusion (sphereMeasure (Fin N × Fin 3)))).symm))

theorem CoreCurve.derivatives_support (u : CoreCurve N) {a b : ℝ}
    (hs : ∀ t, t ∉ Icc a b → u.ambient t = 0) :
    ∀ t, t ∉ Icc a b → u.firstAmbient t = 0 ∧ u.second t = 0 := by
  have hdu := LogarithmicCompactSupport.derivative_zero_outside u.ambient_hasDerivAt hs
  have hfirst (t : ℝ) : L2OperatorDerivative.HasL2DerivAt u.firstAmbient (u.second t) t := by
    unfold CoreCurve.firstAmbient
    exact u.first_hasDerivAt t
  have hdd := LogarithmicCompactSupport.derivative_zero_outside hfirst hdu
  exact fun t ht => ⟨hdu t ht, hdd t ht⟩

theorem CoreCurve.exponential_support (u : CoreCurve N) (τ α : ℝ) {a b : ℝ}
    (hs : ∀ t, t ∉ Icc a b → u.ambient t = 0) :
    ∀ t, t ∉ Icc a b → (u.exponential τ α).ambient t = 0 := by
  intro t ht
  unfold CoreCurve.ambient at hs ⊢
  rw [u.exponential_value τ α t]
  exact (CoreVector.scale_ambient _ _).trans
    ((congrArg (fun x : SpherePhoton N => smoothExponential τ α t • x) (hs t ht)).trans (smul_zero _))

theorem angular_formDerivative_zero (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
    (e : ℝ) (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
    (v : CoreVector N) (t : ℝ) (hv : v.ambient = 0) :
    CenteredSphereAngularField.formDerivative F χ hUV e O C v.gradient v.radiation t = 0 := by
  have hz := v.radiation_zero_of_ambient hv
  unfold CenteredSphereAngularField.formDerivative
  simp only [hz, map_zero, smul_zero, inner_zero_right, mul_zero, Finset.sum_const_zero]

theorem radiation_formDerivative_zero (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
    (e : ℝ) (O : Configuration N) (v : CoreVector N) (t : ℝ) (hv : v.ambient = 0) :
    CenteredSphereRadiationEnergy.formDerivative F χ hUV e O v.radiation t = 0 := by
  have hz := v.radiation_zero_of_ambient hv
  rw [CenteredSphereRadiationEnergy.formDerivative_eq_analysis]
  simp only [hz, map_zero, inner_zero_right, mul_zero]

end PfHk.SphereCoreGeometry
