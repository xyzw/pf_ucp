import PfHk.PhysicalCylinderRepresentatives
import PfHk.PhysicalPolarTransport
import PfHk.WeightedCylinderDensity

/-! Identification of the actual sphere quadratic densities with the
physical conformal densities. -/

noncomputable section
namespace PfHk.PhysicalCylinderSource

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.SphereCoreGeometry PfHk.CenteredRadialGauge PfHk.CarlemanWeights
  PfHk.CylinderConjugation
open PfHk.SphereAngularField (Sphere SpherePhoton)
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000
local instance cylinderEnergyRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance cylinderEnergyGraphComplex : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace
local instance cylinderEnergyGraphReal : NormedSpace ℝ RadiationGraphSpace :=
  NormedSpace.restrictScalars ℝ ℂ RadiationGraphSpace
attribute [local irreducible] CenteredRadialGauge.radiationForm inverseRadiationGraph
  radiationGraphDerivative graphLift curve CoreCurve.conformal CoreCurve.scalar
  CoreVector.scale CoreVector.ambient angular CenteredSphereAngularField.angularVector
  CenteredSphereAngularField.energy CenteredSphereRadiationEnergy.energy

private theorem quadratic_map_smul {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedSpace ℂ H] [IsScalarTower ℝ ℂ H]
    (T : E →L[ℂ] H) (b : ℝ) (q : E) :
    2*‖T (b • q)‖^2 = b^2*(2*‖T q‖^2) := by
  rw [LinearMapClass.map_smul_of_tower, PhysicalPolarDensity.norm_real_smul_sq]
  ring

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
  (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
  (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
  {s : Set (Configuration N)} (a : SmoothCore s)

include W in
set_option maxHeartbeats 150000 in
theorem radiationForm_real_smul (b : ℝ) (X : Configuration N) (q : RadiationGraphSpace) :
    CenteredRadialGauge.radiationForm F χ hUV e O X (b • q) =
      b^2*CenteredRadialGauge.radiationForm F χ hUV e O X q := by
  calc
    _ = 2*‖radiationGraphDerivative (inverseRadiationGraph F χ hUV e O W X (b • q))‖^2 :=
      radiationForm_eq F χ hUV e O W X (b • q)
    _ = b^2*(2*‖radiationGraphDerivative (inverseRadiationGraph F χ hUV e O W X q)‖^2) :=
      quadratic_map_smul (E := RadiationGraphSpace) (H := PhotonFock)
        (radiationGraphDerivative.comp (inverseRadiationGraph F χ hUV e O W X)) b q
    _ = _ := congrArg (fun z : ℝ => b^2*z) (radiationForm_eq F χ hUV e O W X q).symm

def radiationDensity (c t : ℝ) (θ : Sphere N) : ℝ :=
  Real.exp (-c*t)^2 * CenteredRadialGauge.radiationForm F χ hUV e O (Real.exp (-t) • θ.val)
    (graphLift F χ hUV e O W (Real.exp (-t) • θ.val) (a.rootWave (Real.exp (-t) • θ.val)))

theorem radiationDensity_ae (c t : ℝ) :
    (fun θ : Sphere N => CenteredRadialGauge.radiationForm F χ hUV e O (Real.exp (-t) • θ.val)
      (((curve F χ hUV e O C W B P G a c).value t).radiation θ)) =ᵐ[sphereMeasure (Fin N × Fin 3)]
      radiationDensity F χ hUV e O W a c t := by
  filter_upwards [curve_radiation_ae F χ hUV e O C W B P G a c t] with θ hθ
  exact (congrArg (CenteredRadialGauge.radiationForm F χ hUV e O (Real.exp (-t) • θ.val)) hθ).trans
    (radiationForm_real_smul F χ hUV e O W (Real.exp (-c*t)) _ _)

include C B P G in
theorem radiationDensity_integrable (c t : ℝ) :
    Integrable (radiationDensity F χ hUV e O W a c t) (sphereMeasure (Fin N × Fin 3)) :=
  (CenteredSphereRadiationEnergy.fiber_energy_integrable F χ hUV e O
    ((curve F χ hUV e O C W B P G a c).value t).radiation t).congr
      (radiationDensity_ae F χ hUV e O C W B P G a c t)

theorem radiation_inner_eq_integral (c t : ℝ) :
    inner ℝ ((curve F χ hUV e O C W B P G a c).ambient t) (radiation F χ e O W a c t) =
      ∫ θ : Sphere N, radiationDensity F χ hUV e O W a c t θ ∂sphereMeasure (Fin N × Fin 3) := by
  have hd := (radiation_representative F χ hUV e O C W B P G a c t).diagonal F χ hUV e O
  unfold CenteredSphereRadiationEnergy.energy at hd
  exact hd.trans (integral_congr_ae (radiationDensity_ae F χ hUV e O C W B P G a c t))

theorem weighted_density_eq (τ α t : ℝ) (k : ℝ → SpherePhoton N)
    (hk : IsAngularRepresentative F χ hUV e O C t
      ((curve F χ hUV e O C W B P G a (conformalExponent (Fin N × Fin 3))).value t) (k t)) :
    Real.exp (2*τ*weight α t) * originalDensity τ (conformalExponent (Fin N × Fin 3))
      (beta α) (fun v => Real.exp (-2*v))
      (curve F χ hUV e O C W B P G a (conformalExponent (Fin N × Fin 3))).ambient
      (curve F χ hUV e O C W B P G a (conformalExponent (Fin N × Fin 3))).firstAmbient
      k (radiation F χ e O W a (conformalExponent (Fin N × Fin 3))) t =
      ∫ θ : Sphere N, PhysicalPolarDensity.cylinderDensity F χ hUV e O C W a.rootWave τ α t θ
        ∂sphereMeasure (Fin N × Fin 3) := by
  let c := conformalExponent (Fin N × Fin 3)
  let w := curve F χ hUV e O C W B P G a c
  have hK : inner ℝ (w.ambient t) (k t) = ∑ j, ‖angular F χ hUV e O C W B P G a c t j‖^2 := by
    have h := hk.diagonal F χ hUV e O C
    unfold CenteredSphereAngularField.energy at h
    simpa only [angular, w, c, CoreCurve.ambient] using h
  have hT := radiation_inner_eq_integral F χ hUV e O C W B P G a c t
  have hr : Real.exp (-2*t) = Real.exp (-t)^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hscalar := congrArg₂ (fun K T : ℝ => τ^3*beta α t*‖w.ambient t‖^2 +
    τ*beta α t*(‖w.firstAmbient t+c • w.ambient t‖^2+K) + τ*Real.exp (-t)^2*T) hK hT
  have hd := L2QuadraticForms.combined_density_eq_integral (τ^3*beta α t) (τ*beta α t)
    (τ*Real.exp (-t)^2) (w.ambient t) (w.firstAmbient t+c • w.ambient t)
    (angular F χ hUV e O C W B P G a c t) _ _ _ _
    (curve_ambient_ae F χ hUV e O C W B P G a c t)
    (radial_ae F χ hUV e O C W B P G a c t)
    (curveAngular_ae F χ hUV e O C W B P G a c t)
    (radiationDensity_integrable F χ hUV e O C W B P G a c t)
  have hn := congrArg (fun z : ℝ => Real.exp (2*τ*weight α t)*z) (hscalar.trans hd)
  have hleft : originalDensity τ c (beta α) (fun v => Real.exp (-2*v)) w.ambient
      w.firstAmbient k (radiation F χ e O W a c) t =
      τ^3*beta α t*‖w.ambient t‖^2 + τ*beta α t*(‖w.firstAmbient t+c • w.ambient t‖^2+
        inner ℝ (w.ambient t) (k t)) + τ*Real.exp (-t)^2*inner ℝ (w.ambient t) (radiation F χ e O W a c t) :=
    congrArg (fun r : ℝ => τ^3*beta α t*‖w.ambient t‖^2 +
      τ*beta α t*(‖w.firstAmbient t+c • w.ambient t‖^2+inner ℝ (w.ambient t) (k t)) +
      τ*r*inner ℝ (w.ambient t) (radiation F χ e O W a c t)) hr
  apply (congrArg (fun z : ℝ => Real.exp (2*τ*weight α t)*z) hleft).trans
  apply hn.trans
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun θ => by
    dsimp only
    simp only [norm_neg, PhysicalPolarDensity.cylinderDensity, radiationDensity, c]

end PfHk.PhysicalCylinderSource
