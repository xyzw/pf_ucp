import PfHk.PhysicalExternalCarlemanSum
import PfHk.PhysicalExternalRealization

/-! Carleman for the full weakly realized Pauli--Fierz Hamiltonian with
external vector and scalar potentials. Physical multiplier estimates,
the operator source identity, and absorption are conclusions of the
preceding proofs. The remaining inputs are the stated ordinary analytic
and operator-theory backgrounds. -/

noncomputable section
namespace PfHk.PhysicalExternalCarleman

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.CenteredPhysicalReference PfHk.PhysicalFieldRegularity
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain PfHk.PhysicalCarlemanInput
  PfHk.PhysicalCutoffCommutator PfHk.PhysicalExternalOperator
  PfHk.KatoRellichBackground PfHk.FriedrichsDivergenceBackground
  PfHk.PhysicalExternalCarlemanSum PfHk.SmoothCutoffBounds

local instance endpointPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PfHk.PhysicalDyadicEnergy.dyadicEnergyPhotonRealInner

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

attribute [local irreducible] inclusion covariant radiation FreeGraph
  PhysicalExternalSource.total PhysicalExternalSource.term
  PhysicalPFReference.referenceSubspace IsOperatorPair

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (a : PhysicalExternalCoefficients.Data N)
  (S : CoordinateSobolev.Data PhotonFock N)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
  (joint : CoordinateComparisonSpectral.Data spectral)
  (friedrichs : StandardFriedrichsDivergence) (KR : StandardKatoRellich)
  (hD : HaslerHerbstDomain C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hG : HaslerHerbstGraphNorm C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hSA : SelfAdjointGraph (freeHilbertGraph (fun _ => 0) C (profile (N := N) F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e))

include S joint friedrichs KR hD hG hSA

theorem exists_uniform_estimate_of_data
    {α : ℝ} (hα : 0 < α)
    (D : PhysicalFreePerturbationData.Data F χ C e spectral α)
    (hcore : AnnularCoreApproximation C (profile (N := N) F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ D.radius ∧ r₀ < Real.exp (-2) ∧
      ∀ (O : Configuration N) (R : ℝ) (hR : 0 < R), R ≤ r₀ →
      ∀ τ : ℝ, D.parameter ≤ τ →
      ∀ (u : Reference (Fin N × Fin 3) (fun _ => 0))
        (hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u)
        (f : WaveSpace (Fin N × Fin 3)),
        IsOperatorPair (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
          (profileBound F χ) (profile_bound F χ 0) e a.vector a.positive a.negative u hu f →
        AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R →
        Estimate F χ C e a spectral (D.family O) R hR τ α D.second D.enlargedSecond u hu f := by
  have hex := exists_uniform_sum_estimate F χ C e a S spectral joint hα D hD hcore
  let r₀ := Classical.choose hex
  have hr := Classical.choose_spec hex
  refine ⟨r₀, hr.1, hr.2.1, hr.2.2.1, ?_⟩
  intro O R hR hRsmall τ hτ u hu f hf hsupp
  have hsum := (operatorPair_iff_free_total a S spectral joint friedrichs KR C
    (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
    e hD hG hSA u f hu).mp hf
  let g := Classical.choose hsum
  let hg := Classical.choose (Classical.choose_spec hsum)
  have hfg := Classical.choose_spec (Classical.choose_spec hsum)
  have hest := hr.2.2.2 O R hR hRsmall τ hτ u hu g hg hsupp
  let P := Classical.choose hest
  have hP := Classical.choose_spec hest
  exact (congrArg (Estimate F χ C e a spectral (D.family O) R hR τ α D.second D.enlargedSecond u hu)
    hfg).mpr hP

open PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.SphereCoreGeometry
  PfHk.OrdinaryPolarSobolevChart

theorem exists_uniform_estimate (hUV : CarlemanUV χ)
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
      0 < r₀ ∧ r₀ < Real.exp (-2) ∧ 1 ≤ τ₀ ∧ 0 ≤ C₂ ∧ 0 ≤ C₂e ∧
      ∀ (O : Configuration N) (R : ℝ) (hR : 0 < R), R ≤ r₀ →
      ∀ τ : ℝ, τ₀ ≤ τ →
      ∀ (u : Reference (Fin N × Fin 3) (fun _ => 0))
        (hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u)
        (f : WaveSpace (Fin N × Fin 3)),
        IsOperatorPair (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
          (profileBound F χ) (profile_bound F χ 0) e a.vector a.positive a.negative u hu f →
        AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R →
        Estimate F χ C e a spectral (family O) R hR τ α C₂ C₂e u hu f := by
  have hex := PhysicalFreePerturbationData.exists_data F χ C e hUV W B P G charts L hN
    coreDensity core spectral hD hG α hα
  let D := Classical.choice hex
  have hfull := exists_uniform_estimate_of_data F χ C e a S spectral joint friedrichs KR
    hD hG hSA hα D (core 0)
  let r₀ := Classical.choose hfull
  have hr := Classical.choose_spec hfull
  exact ⟨r₀, D.parameter, D.second, D.enlargedSecond, D.family,
    hr.1, hr.2.2.1, D.parameter_ge_one, D.second_nonneg, D.enlargedSecond_nonneg, hr.2.2.2⟩

end PfHk.PhysicalExternalCarleman
