import PfHk.PhysicalLocalExternalCarleman


/-! Finite-component amplification of the proved physical orbital Carleman
estimate. Every component uses the same radius and parameter thresholds.
The resulting source is the sum of the squared physical component sources. -/

noncomputable section
namespace PfHk.PauliCarlemanFinite

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.CenteredPhysicalReference PfHk.PhysicalFieldRegularity
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain PfHk.PhysicalCarlemanInput
  PfHk.PhysicalCutoffCommutator PfHk.PhysicalExternalOperator
  PfHk.KatoRellichBackground PfHk.FriedrichsDivergenceBackground
  PfHk.SmoothCutoffBounds PfHk.SmoothDyadicCutoffs PfHk.PhysicalDyadicEnergy
  PfHk.PhysicalCoefficientLocality PfHk.BufferedCutoffLocality

attribute [local instance] PfHk.PhysicalLocalExternalCarleman.endpointPhotonRealInner

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

attribute [local irreducible] inclusion covariant radiation roughMultiply FreeGraph
  PhysicalPFReference.referenceSubspace IsOperatorPair IsLocalOperatorPair
  GptLean.ElectronicH1Multiplier.DifferentiableMultiplier.multiplier

variable {N : ℕ} {O₀ : Configuration N} {ρ : ℝ}
  (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (a : PhysicalLocalExternalCoefficients.Data O₀ ρ)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))


variable {T : Type*} [Fintype T]

def sourceEnergySum (O : Configuration N) (τ α : ℝ)
    (f : T → WaveSpace (Fin N × Fin 3)) (X : Configuration N) : ℝ :=
  ∑ s, sourceEnergy O τ α (f s) X

def densitySum (O : Configuration N) (τ α : ℝ)
    (u : T → Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ∀ s, ExternalDomain (fun _ => 0) a.vector a.positive a.negative (u s))
    (X : Configuration N) : ℝ :=
  ∑ s, PhysicalExternalEnergy.density F χ C e a.vector a.positive a.negative
    O τ α (u s) (hu s) X

/-- Component mixed estimates and the summed physical weighted estimate. -/
def Estimate {O : Configuration N} (family : BufferedFamily O)
    (R : ℝ) (hR : 0 < R) (τ α C₂ C₂e : ℝ)
    (u : T → Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ∀ s, ExternalDomain (fun _ => 0) a.vector a.positive a.negative (u s))
    (f : T → WaveSpace (Fin N × Fin 3)) : Prop :=
  (∀ s, PhysicalLocalExternalCarleman.Estimate F χ C e a spectral
    family R hR τ α C₂ C₂e (u s) (hu s) (f s)) ∧
  IntegrableOn (sourceEnergySum O τ α f) (Metric.ball O R) ∧
  Integrable (densitySum F χ C e a O τ α u hu) ∧
  (∫ X, densitySum F χ C e a O τ α u hu X) ≤
    520 * ∫ X in Metric.ball O R, sourceEnergySum O τ α f X

theorem of_components {O : Configuration N} {family : BufferedFamily O}
    {R : ℝ} {hR : 0 < R} {τ α C₂ C₂e : ℝ}
    {u : T → Reference (Fin N × Fin 3) (fun _ => 0)}
    {hu : ∀ s, ExternalDomain (fun _ => 0) a.vector a.positive a.negative (u s)}
    {f : T → WaveSpace (Fin N × Fin 3)}
    (he : ∀ s, PhysicalLocalExternalCarleman.Estimate F χ C e a spectral
      family R hR τ α C₂ C₂e (u s) (hu s) (f s)) :
    Estimate F χ C e a spectral family R hR τ α C₂ C₂e u hu f := by
  classical
  have hsource : IntegrableOn (sourceEnergySum O τ α f) (Metric.ball O R) :=
    integrable_finsetSum _ (fun s _ => (he s).1)
  have hdensity : Integrable (densitySum F χ C e a O τ α u hu) :=
    integrable_finsetSum _ (fun s _ => (he s).2.1)
  refine ⟨he, hsource, hdensity, ?_⟩
  simp only [densitySum, sourceEnergySum]
  rw [integral_finsetSum _ (fun s _ => (he s).2.1),
    integral_finsetSum _ (fun s _ => (he s).1), Finset.mul_sum]
  exact Finset.sum_le_sum (fun s _ => (he s).2.2.1)


variable (S : CoordinateSobolev.Data PhotonFock N)
  (joint : CoordinateComparisonSpectral.Data spectral)
  (friedrichs : StandardFriedrichsDivergence) (KR : StandardKatoRellich)
  (hD : HaslerHerbstDomain C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hG : HaslerHerbstGraphNorm C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hSA : SelfAdjointGraph (freeHilbertGraph (fun _ => 0) C (profile (N := N) F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e))

open PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.SphereCoreGeometry
  PfHk.OrdinaryPolarSobolevChart

include S joint friedrichs KR hD hG hSA

theorem exists_uniform_estimate (hρ : 0 < ρ) (hUV : CarlemanUV χ)
    (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
    (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
    (charts : StandardPolarSobolevCharts N) (L : StandardLogPolarCalculus (Fin N × Fin 3))
    (hN : 0 < Fintype.card (Fin N × Fin 3))
    (coreDensity : WeylCoreReference.StandardWeylFormCoreDensity W B)
    (core : ∀ O : Configuration N, AnnularCoreApproximation C (profile F χ O)
      (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e)
    (α : ℝ) (hα : 0 < α) :
    ∃ r₀ τ₀ C₂ C₂e : ℝ, ∃ family : ∀ O : Configuration N, BufferedFamily O,
      0 < r₀ ∧ r₀ ≤ ρ / 16 ∧ r₀ < Real.exp (-2) ∧ 1 ≤ τ₀ ∧ 0 ≤ C₂ ∧ 0 ≤ C₂e ∧
      ∀ O ∈ Metric.ball O₀ r₀, ∀ (R : ℝ) (hR : 0 < R), R ≤ r₀ →
      ∀ τ : ℝ, τ₀ ≤ τ →
      ∀ (u : T → Reference (Fin N × Fin 3) (fun _ => 0))
        (hu : ∀ s, ExternalDomain (fun _ => 0) a.vector a.positive a.negative (u s))
        (f : T → WaveSpace (Fin N × Fin 3)),
        (∀ s, IsLocalOperatorPair (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
          (profileBound F χ) (profile_bound F χ 0) e a.vector a.positive a.negative
          (Metric.ball O₀ (ρ / 2)) (u s) (hu s) (f s)) →
        (∀ s, AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) O R) →
        Estimate F χ C e a spectral (family O) R hR τ α C₂ C₂e u hu f := by
  have hfull := PhysicalLocalExternalCarleman.exists_uniform_estimate F χ C e a spectral S joint
      friedrichs KR hD hG hSA hρ hUV W B P G charts L hN coreDensity core α hα
  obtain ⟨r₀, τ₀, C₂, C₂e, family, hr₀, hrρ, hrsmall, hτ₀, hC₂, hC₂e, hest⟩ := hfull
  refine ⟨r₀, τ₀, C₂, C₂e, family, hr₀, hrρ, hrsmall, hτ₀, hC₂, hC₂e, ?_⟩
  intro O hO R hR hRr τ hτ u hu f hf hsupp
  exact of_components F χ C e a spectral
    (fun s => hest O hO R hR hRr τ hτ (u s) (hu s) (f s) (hf s) (hsupp s))


end PfHk.PauliCarlemanFinite

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
