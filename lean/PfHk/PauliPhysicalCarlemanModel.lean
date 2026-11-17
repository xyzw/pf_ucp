import PfHk.PauliPhysicalCarleman
import PfHk.PauliPhysicalLocalRegularity

/-! Full Pauli Carleman estimates for the manuscript's admissible
external potentials. The physical common form domain supplies every
multiplier witness. Local Coulomb boundedness is derived off collisions
in the open-set endpoint. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  GptLean.PhysicalPairDuality PfHk.PhysicalCommonFormDomain
  PfHk.CenteredPhysicalReference PfHk.PhysicalFieldRegularity
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain PfHk.PhysicalCarlemanInput
  PfHk.PhysicalCutoffCommutator PfHk.PhysicalExternalOperator
  PfHk.KatoRellichBackground PfHk.FriedrichsDivergenceBackground
  PfHk.SmoothCutoffBounds PfHk.SmoothDyadicCutoffs PfHk.PauliSpin
  PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.SphereCoreGeometry
  PfHk.OrdinaryPolarSobolevChart PfHk.PhysicalDyadicEnergy
  PfHk.PauliCarlemanFinite

attribute [local instance] PhysicalLocalExternalCarleman.endpointPhotonRealInner

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

variable {N : ℕ} {O₀ : Configuration N} {ρ : ℝ}
attribute [local irreducible] referenceSubspace inclusion

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))

namespace PauliPhysicalCarleman

/-- The physical covariant density and both spin-summed mixed series,
with the actual source of the shifted Pauli Hamiltonian. -/
def PhysicalEstimate {O : Configuration N} (family : BufferedFamily O)
    (R : ℝ) (hR : 0 < R) (τ α C₂ C₂e : ℝ)
    (u : PauliReference.Ref N)
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3)) : Prop :=
  IntegrableOn (sourceEnergySum O τ α f) (Metric.ball O R) ∧
    (∀ s, Integrable (PhysicalExternalEnergy.density F χ C e
      (vector A) (positive v c) (negative v c) O τ α (u s)
      (PauliGroundState.physicalDomain A v c hc u s))) ∧
    (∫ X, ∑ s, PhysicalExternalEnergy.density F χ C e
      (vector A) (positive v c) (negative v c) O τ α (u s)
      (PauliGroundState.physicalDomain A v c hc u s) X) ≤
      2080 * ∫ X in Metric.ball O R, sourceEnergySum O τ α f X ∧
    PauliMixedSeries.Bound spectral
      (fun s => PhysicalFractionalCarleman.localized family R hR τ α (u s))
      (dyadicBeta α R) (radius R) τ (16 * 6144) (16 * C₂)
      (∫ X in Metric.ball O R, sourceEnergySum O τ α f X) ∧
    PauliMixedSeries.Bound spectral
      (fun s => PhysicalEnlargedFractionalCarleman.localized family R hR τ α (u s))
      (dyadicBeta α R) (radius R) τ (16 * 40960) (16 * C₂e)
      (∫ X in Metric.ball O R, sourceEnergySum O τ α f X)

private theorem estimate_eq_physical
    (a : PauliLocalDomain.PhysicalRegularity A v c O₀ ρ)
    {O : Configuration N} (family : BufferedFamily O)
    (R : ℝ) (hR : 0 < R) (τ α C₂ C₂e : ℝ)
    (u : PauliReference.Ref N) (f : SpinIndex N → WaveSpace (Fin N × Fin 3)) :
    Estimate F χ C e (PauliLocalDomain.PhysicalRegularity.data A v c O₀ ρ a).orbital
      spectral family R hR τ α C₂ C₂e u (PauliGroundState.physicalDomain A v c hc u) f =
      PhysicalEstimate F χ C e A v c hc spectral family R hR τ α C₂ C₂e u f := rfl

variable (S : CoordinateSobolev.Data PhotonFock N)
  (joint : CoordinateComparisonSpectral.Data spectral)
  (friedrichs : StandardFriedrichsDivergence) (KR : StandardKatoRellich)
  (hD : HaslerHerbstDomain C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hG : HaslerHerbstGraphNorm C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hSA : SelfAdjointGraph (freeHilbertGraph (fun _ => 0) C (profile (N := N) F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e))

include S joint friedrichs KR hD hG hSA in
/-- The actual physical potentials determine a common Carleman radius
and threshold. No multiplier-domain or magnetic smallness premise is
present. The weak source relation is H_P u = f + E u. -/
theorem physical_exists_uniform_estimate
    (a : PauliLocalDomain.PhysicalRegularity A v c O₀ ρ) (hρ : 0 < ρ)
    (hUV : CarlemanUV χ) (W : ConcreteWeylLaw photonMeasure)
    (B : StandardWeylGraphC1 W)
    (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
    (charts : StandardPolarSobolevCharts N) (L : StandardLogPolarCalculus (Fin N × Fin 3))
    (hN : 0 < Fintype.card (Fin N × Fin 3))
    (coreDensity : WeylCoreReference.StandardWeylFormCoreDensity W B)
    (core : ∀ O : Configuration N, AnnularCoreApproximation C (profile F χ O)
      (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e)
    (α : ℝ) (hα : 0 < α) (E : ℝ) :
    ∃ r₀ τ₀ C₂ C₂e : ℝ, ∃ family : ∀ O : Configuration N, BufferedFamily O,
      0 < r₀ ∧ r₀ ≤ ρ / 16 ∧ 2 * r₀ ≤ Real.exp (-2) ∧ r₀ < Real.exp (-2) ∧
      1 ≤ τ₀ ∧ 0 ≤ C₂ ∧ 0 ≤ C₂e ∧
      ∀ O ∈ Metric.ball O₀ r₀, ∀ (R : ℝ) (hR : 0 < R), R ≤ r₀ →
      ∀ τ : ℝ, τ₀ ≤ τ →
      ∀ (u : PauliReference.Ref N) (f : SpinIndex N → WaveSpace (Fin N × Fin 3)),
        PauliLocalOperatorTransfer.IsLocalOperatorPair C F χ e (vector A)
          (positive v c) (negative v c) (Metric.ball O₀ (ρ / 2))
          u (PauliGroundState.physicalDomain A v c hc u)
          (fun s => f s + (E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) →
        (∀ s, AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) O R) →
        PhysicalEstimate F χ C e A v c hc spectral (family O) R hR τ α C₂ C₂e u f := by
  have hex := exists_uniform_estimate F χ C e
    (PauliLocalDomain.PhysicalRegularity.data A v c O₀ ρ a) spectral S joint
    friedrichs KR hD hG hSA hρ hUV W B P G charts L hN coreDensity core α hα E
  let r₀ := Classical.choose hex
  have h₁ := Classical.choose_spec hex
  let τ₀ := Classical.choose h₁
  have h₂ := Classical.choose_spec h₁
  let C₂ := Classical.choose h₂
  have h₃ := Classical.choose_spec h₂
  let C₂e := Classical.choose h₃
  have h₄ := Classical.choose_spec h₃
  let family := Classical.choose h₄
  have hbase := Classical.choose_spec h₄
  refine ⟨r₀, τ₀, C₂, C₂e, family, hbase.1, hbase.2.1, hbase.2.2.1,
    hbase.2.2.2.1, hbase.2.2.2.2.1, hbase.2.2.2.2.2.1, hbase.2.2.2.2.2.2.1, ?_⟩
  intro O hO R hR hRr τ hτ u f hf hsupp
  have he := hbase.2.2.2.2.2.2.2 O hO R hR hRr τ hτ u
    (PauliGroundState.physicalDomain A v c hc u) f hf hsupp
  exact (estimate_eq_physical F χ C e A v c hc spectral a
    (family O) R hR τ α C₂ C₂e u f).mp he

end PauliPhysicalCarleman

namespace PauliPhysicalLocalRegularity

variable {Ω : Set PhysicalSourceCoordinates.Position}
  (S : CoordinateSobolev.Data PhotonFock N)
  (joint : CoordinateComparisonSpectral.Data spectral)
  (friedrichs : StandardFriedrichsDivergence) (KR : StandardKatoRellich)
  (hD : HaslerHerbstDomain C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hG : HaslerHerbstGraphNorm C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hSA : SelfAdjointGraph (freeHilbertGraph (fun _ => 0) C (profile (N := N) F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e))

include S joint friedrichs KR hD hG hSA in
/-- At every configuration in the regular open set away from collisions,
the physical Pauli estimate follows from the paper's one-body coefficient
assumptions. The Coulomb bound and coefficient radius are conclusions. -/
theorem RegularityOn.exists_uniform_estimate (a : RegularityOn A v Ω)
    (hΩ : IsOpen Ω) (hcoords : ∀ n, (PhysicalSourceCoordinates.split n O₀).1 ∈ Ω)
    (hcoll : O₀ ∈ distinctConfigurations N)
    (hUV : CarlemanUV χ) (W : ConcreteWeylLaw photonMeasure)
    (B : StandardWeylGraphC1 W)
    (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
    (charts : StandardPolarSobolevCharts N) (L : StandardLogPolarCalculus (Fin N × Fin 3))
    (hN : 0 < Fintype.card (Fin N × Fin 3))
    (coreDensity : WeylCoreReference.StandardWeylFormCoreDensity W B)
    (core : ∀ O : Configuration N, AnnularCoreApproximation C (profile F χ O)
      (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e)
    (α : ℝ) (hα : 0 < α) (E : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∃ r₀ τ₀ C₂ C₂e : ℝ, ∃ family : ∀ O : Configuration N, BufferedFamily O,
        0 < r₀ ∧ r₀ ≤ ρ / 16 ∧ 2 * r₀ ≤ Real.exp (-2) ∧ r₀ < Real.exp (-2) ∧
        1 ≤ τ₀ ∧ 0 ≤ C₂ ∧ 0 ≤ C₂e ∧
        ∀ O ∈ Metric.ball O₀ r₀, ∀ (R : ℝ) (hR : 0 < R), R ≤ r₀ →
        ∀ τ : ℝ, τ₀ ≤ τ →
        ∀ (u : PauliReference.Ref N) (f : SpinIndex N → WaveSpace (Fin N × Fin 3)),
          PauliLocalOperatorTransfer.IsLocalOperatorPair C F χ e (vector A)
            (positive v c) (negative v c) (Metric.ball O₀ (ρ / 2))
            u (PauliGroundState.physicalDomain A v c hc u)
            (fun s => f s + (E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) →
          (∀ s, AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) O R) →
          PauliPhysicalCarleman.PhysicalEstimate F χ C e A v c hc spectral
            (family O) R hR τ α C₂ C₂e u f := by
  have hex := a.exists_physicalRegularity hΩ hcoords hcoll c
  let ρ := Classical.choose hex
  have hρ := (Classical.choose_spec hex).1
  let areg := Classical.choice (Classical.choose_spec hex).2
  exact ⟨ρ, hρ, PauliPhysicalCarleman.physical_exists_uniform_estimate
    F χ C e A v c hc spectral S joint friedrichs KR hD hG hSA
    areg hρ hUV W B P G charts L hN coreDensity core α hα E⟩

end PauliPhysicalLocalRegularity
end PfHk

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
