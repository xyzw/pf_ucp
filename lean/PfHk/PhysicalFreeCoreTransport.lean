import PfHk.PhysicalCylinderEnergy
import PfHk.PhysicalCylinderNormTransport
import PfHk.CarlemanAnnularWeights

/-! Combination of the exact physical energy and source transports.
The cylinder inequality and its angular representative are supplied by
their separate proved analytic steps. -/

noncomputable section
namespace PfHk.PhysicalCylinderSource

open MeasureTheory Set GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.SphereCoreGeometry PfHk.CenteredRadialGauge PfHk.CarlemanWeights
  PfHk.CylinderConjugation
open PfHk.SphereAngularField (Sphere SpherePhoton)
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000
local instance coreTransportRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] curve source angularCandidate
  PhysicalPolarDensity.mass PhysicalPolarDensity.kinetic PhysicalPolarDensity.radiation

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
  (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
  (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
  (L : StandardLogPolarCalculus (Fin N × Fin 3))
  (hd : 0 < Fintype.card (Fin N × Fin 3))
  {s : Set (Configuration N)} (a : SmoothCore s)
  {f : PhysicalPFReference.WaveSpace (Fin N × Fin 3)} (g : CompactSource s f)

include g in
theorem compact_source_weighted_integrable (τ α : ℝ) {ρ R : ℝ}
    (hρ : 0 < ρ) (hR : R < 1) (hs : s ⊆ CarlemanSpatialDensity.annulus ρ R) :
    Integrable (CarlemanSpatialDensity.source τ α (fun X => ‖f X‖^2)) := by
  apply CarlemanSpatialDensity.source_integrable τ α hρ hR _ (Lp.memLp f).norm.integrable_sq
  filter_upwards [g.agrees] with X hX houtside
  have hz : g.representative X = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => houtside (hs (g.support h)))
  exact (congrArg (fun v : PhotonFock => ‖v‖^2) (hX.trans hz)).trans (by simp)

include L hd in
theorem spatial_estimate_of_cylinder (τ α t₀ : ℝ)
    (hk : ∀ t, IsAngularRepresentative F χ hUV e O C t
      ((curve F χ hUV e O C W B P G a (conformalExponent (Fin N × Fin 3))).value t)
      (angularCandidate F χ hUV e O C W B P G a g (conformalExponent (Fin N × Fin 3)) t))
    (hI : IntegrableOn (CarlemanSpatialDensity.density τ α
      (PhysicalPolarDensity.mass a.rootWave) (PhysicalPolarDensity.kinetic F χ e O C a.rootWave)
      (PhysicalPolarDensity.radiation a.rootWave)) (Metric.ball 0 (Real.exp (-t₀))))
    (hF : IntegrableOn (CarlemanSpatialDensity.source τ α (fun X => ‖f X‖^2))
      (Metric.ball 0 (Real.exp (-t₀))))
    (hestimate :
      (∫ t in Ioi t₀, Real.exp (2*τ*weight α t)*originalDensity τ (conformalExponent (Fin N × Fin 3))
        (beta α) (fun v => Real.exp (-2*v))
        (curve F χ hUV e O C W B P G a (conformalExponent (Fin N × Fin 3))).ambient
        (curve F χ hUV e O C W B P G a (conformalExponent (Fin N × Fin 3))).firstAmbient
        (angularCandidate F χ hUV e O C W B P G a g (conformalExponent (Fin N × Fin 3)))
        (radiation F χ e O W a (conformalExponent (Fin N × Fin 3))) t) ≤
        16*∫ t in Ioi t₀, Real.exp (2*τ*weight α t)*
          ‖source F χ e O W g (conformalExponent (Fin N × Fin 3)) t‖^2) :
    (∫ X in Metric.ball 0 (Real.exp (-t₀)), CarlemanSpatialDensity.density τ α
      (PhysicalPolarDensity.mass a.rootWave) (PhysicalPolarDensity.kinetic F χ e O C a.rootWave)
      (PhysicalPolarDensity.radiation a.rootWave) X) ≤
      64*∫ X in Metric.ball 0 (Real.exp (-t₀)),
        CarlemanSpatialDensity.source τ α (fun Y => ‖f Y‖^2) X := by
  have hw := gauged_core_contDiff F χ hUV e O W B a
  have hs (t : ℝ) : SphereC1 (radialRestriction (gaugedValue F χ e O W a.rootWave) (Real.exp (-t))) :=
    radialRestriction_sphereC1 _ hw _
  have hu (X : Configuration N) : DifferentiableAt ℝ (coreValue a.rootWave) X :=
    (a.value_smooth.differentiable one_ne_zero).differentiableAt
  have hfinite (X : Configuration N) :
      FiniteNumberSupport photonMeasure a.photonCutoff (coreValue a.rootWave X) :=
    a.photonFinite X
  have htransport := PhysicalPolarDensity.integral_cylinderDensity F χ hUV e O C W P L hd
    a.rootWave hw τ α t₀ hs hu a.photonCutoff hfinite hI
  have hlhs := integral_congr_ae (μ := (volume : Measure ℝ).restrict (Ioi t₀))
    (ae_of_all _ fun t => weighted_density_eq F χ hUV e O C W B P G a τ α t
      (angularCandidate F χ hUV e O C W B P G a g (conformalExponent (Fin N × Fin 3))) (hk t))
  have hright := weighted_source_integral F χ e O W g L hd τ α t₀ hF
  calc
    _ = _ := htransport.symm.trans hlhs.symm
    _ ≤ _ := hestimate
    _ = _ := by rw [hright]; ring

end PfHk.PhysicalCylinderSource
