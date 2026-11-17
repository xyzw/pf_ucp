import PfHk.PhysicalCylinderCoreEstimate
import PfHk.PhysicalCylinderAngularRepresentative
import PfHk.PhysicalFreeCoreTransport
import PfHk.PhysicalCoreSpatialIntegrability
import PfHk.PhysicalComparisonDomain

/-! The free physical Carleman estimate on the actual smooth operator
core. The angular representation, all integration conditions, and both
physical changes of measure are discharged by the preceding theorems. -/

noncomputable section
namespace PfHk.PhysicalFreeCarleman

open MeasureTheory Set GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.SphereCoreGeometry PfHk.CenteredRadialGauge PfHk.CarlemanWeights
  PfHk.PhysicalCylinderSource PfHk.OrdinaryPolarSobolevChart
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
local instance freeCoreCarlemanRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] FreeGraph SmoothCore.reference curve angularCandidate

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (C : CanonicalSectorCCR photonMeasure) (W : ConcreteWeylLaw photonMeasure)
  (B : StandardWeylGraphC1 W)
  (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
  (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
  (S : StandardPolarSobolevCharts N)
  (L : StandardLogPolarCalculus (Fin N × Fin 3)) (hN : 0 < Fintype.card (Fin N × Fin 3))
  (D : WeylCoreReference.StandardWeylFormCoreDensity W B)

include hUV W B P G S L hN D in
theorem exists_uniform_core_estimate (α : ℝ) (hα : 0 < α) :
    ∃ t₀ : ℝ, 2 ≤ t₀ ∧ ∀ τ : ℝ,
      max 9 |conformalExponent (Fin N × Fin 3)| ≤ τ →
      ∀ (O : Configuration N) {s : Set (Configuration N)} {ρ R : ℝ},
      0 < ρ → R < 1 → s ⊆ CarlemanSpatialDensity.annulus ρ R →
      (∀ X ∈ s, 0 < ‖X‖ ∧ ‖X‖ < Real.exp (-t₀)) →
      ∀ (a : SmoothCore s) {f : PhysicalPFReference.WaveSpace (Fin N × Fin 3)},
      CompactSource s f →
      FreeGraph C (CenteredPhysicalReference.profile F χ O)
        (CenteredPhysicalReference.profile_measurable F χ O) (CenteredPhysicalReference.profileBound F χ)
        (CenteredPhysicalReference.profile_bound F χ O) e a.reference f →
      (∫ X, CarlemanSpatialDensity.density τ α (PhysicalPolarDensity.mass a.rootWave)
        (PhysicalPolarDensity.kinetic F χ e O C a.rootWave) (PhysicalPolarDensity.radiation a.rootWave) X) ≤
        64*∫ X, CarlemanSpatialDensity.source τ α (fun Y => ‖f Y‖^2) X := by
  have hex := exists_uniform_source_estimate (N := N) F χ hUV e C W B P G α hα
  let t₀ := Classical.choose hex
  have ht₀ : 2 ≤ t₀ := (Classical.choose_spec hex).1
  refine ⟨t₀, ht₀, ?_⟩
  intro τ hτ O s ρ R hρ hR hsA hs a f g hf
  have hoperator := (freeGraph_iff C (CenteredPhysicalReference.profile F χ O)
    (CenteredPhysicalReference.profile_measurable F χ O) (CenteredPhysicalReference.profileBound F χ)
    (CenteredPhysicalReference.profile_bound F χ O) e a.reference f).mp hf
  have hK := angularCandidate_representative F χ hUV e O C W B P G S L hN D a g hoperator
  have hI := PhysicalPolarDensity.core_weighted_density_integrableOn a F χ e O C τ α hρ hR hsA
    (Metric.ball 0 (Real.exp (-t₀)))
  have hF : IntegrableOn (CarlemanSpatialDensity.source τ α (fun X => ‖f X‖^2))
      (Metric.ball 0 (Real.exp (-t₀))) :=
    (compact_source_weighted_integrable g τ α hρ hR hsA).integrableOn
  have hestimate := (Classical.choose_spec hex).2 τ (conformalExponent (Fin N × Fin 3))
    ((le_max_left _ _).trans hτ) ((le_max_right _ _).trans hτ) O a g hs hK
  have hbound := spatial_estimate_of_cylinder F χ hUV e O C W B P G L hN a g τ α t₀ hK hI hF hestimate
  have hleft := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := (volume : Measure (Configuration N))) (s := Metric.ball 0 (Real.exp (-t₀)))
    (f := CarlemanSpatialDensity.density τ α (PhysicalPolarDensity.mass a.rootWave)
      (PhysicalPolarDensity.kinetic F χ e O C a.rootWave) (PhysicalPolarDensity.radiation a.rootWave))
    (fun X hX => by
      have hout : X ∉ s := fun h => hX (by simpa only [Metric.mem_ball, dist_zero_right] using (hs X h).2)
      have hz := PhysicalPolarDensity.core_densities_zero a F χ e O C hout
      simp only [CarlemanSpatialDensity.density, hz.1, hz.2.1, hz.2.2, mul_zero, add_zero])
  have hright := setIntegral_eq_integral_of_ae_compl_eq_zero
    (μ := (volume : Measure (Configuration N))) (s := Metric.ball 0 (Real.exp (-t₀)))
    (f := CarlemanSpatialDensity.source τ α (fun X => ‖f X‖^2)) (by
      filter_upwards [g.agrees] with X hX hball
      have hout : X ∉ s := fun h => hball (by simpa only [Metric.mem_ball, dist_zero_right] using (hs X h).2)
      have hz := hX.trans (image_eq_zero_of_notMem_tsupport (fun h => hout (g.support h)))
      simp only [CarlemanSpatialDensity.source, hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero])
  exact hleft.symm.trans_le (hbound.trans_eq (congrArg (fun z : ℝ => 64*z) hright))

end PfHk.PhysicalFreeCarleman
