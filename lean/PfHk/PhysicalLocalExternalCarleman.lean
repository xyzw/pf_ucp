import PfHk.PhysicalExternalCarleman
import PfHk.PhysicalLocalExternalCoefficients
import PfHk.PhysicalLocalTruncation
import PfHk.BufferedCutoffLocality
import PfHk.PhysicalExternalDensityLocality

/-! The full Hamiltonian Carleman estimate under the paper's local
coefficient hypotheses. One truncated realization works for every nearby
center and every smaller ball. The local weak equation is transferred to
that realization by an actual cutoff with zero commutator on the state. -/

noncomputable section
namespace PfHk.PhysicalLocalExternalCarleman

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.CenteredPhysicalReference PfHk.PhysicalFieldRegularity
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain PfHk.PhysicalCarlemanInput
  PfHk.PhysicalCutoffCommutator PfHk.PhysicalExternalOperator
  PfHk.KatoRellichBackground PfHk.FriedrichsDivergenceBackground
  PfHk.SmoothCutoffBounds PfHk.SmoothDyadicCutoffs PfHk.PhysicalDyadicEnergy
  PfHk.PhysicalCoefficientLocality PfHk.BufferedCutoffLocality

local instance endpointPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PfHk.PhysicalDyadicEnergy.dyadicEnergyPhotonRealInner

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [local irreducible] inclusion covariant radiation roughMultiply FreeGraph
  PhysicalPFReference.referenceSubspace IsOperatorPair IsLocalOperatorPair
  GptLean.ElectronicH1Multiplier.DifferentiableMultiplier.multiplier

variable {N : ℕ} {O₀ : Configuration N} {ρ : ℝ}
  (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (a : PhysicalLocalExternalCoefficients.Data O₀ ρ)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))

def Estimate {O : Configuration N} (family : BufferedFamily O)
    (R : ℝ) (hR : 0 < R) (τ α C₂ C₂e : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u)
    (f : WaveSpace (Fin N × Fin 3)) : Prop :=
  IntegrableOn (sourceEnergy O τ α f) (Metric.ball O R) ∧
    Integrable (PhysicalExternalEnergy.density F χ C e a.vector a.positive a.negative O τ α u hu) ∧
    (∫ X, PhysicalExternalEnergy.density F χ C e a.vector a.positive a.negative O τ α u hu X) ≤
      520 * ∫ X in Metric.ball O R, sourceEnergy O τ α f X ∧
    PhysicalMixedSeries.Bound spectral (PhysicalFractionalCarleman.localized family R hR τ α u)
      (dyadicBeta α R) (radius R) τ (4 * 6144) (4 * C₂)
      (∫ X in Metric.ball O R, sourceEnergy O τ α f X) ∧
    PhysicalMixedSeries.Bound spectral (PhysicalEnlargedFractionalCarleman.localized family R hR τ α u)
      (dyadicBeta α R) (radius R) τ (4 * 40960) (4 * C₂e)
      (∫ X in Metric.ball O R, sourceEnergy O τ α f X)

theorem Estimate.paper_density {O : Configuration N} {family : BufferedFamily O}
    {R : ℝ} {hR : 0 < R} {τ α C₂ C₂e : ℝ}
    {u : Reference (Fin N × Fin 3) (fun _ => 0)}
    {hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u}
    {f : WaveSpace (Fin N × Fin 3)}
    (he : Estimate F χ C e a spectral family R hR τ α C₂ C₂e u hu f)
    (hτ : 0 ≤ τ) (hα : 0 < α) (hRone : R < 1)
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R) :
    IntegrableOn (PhysicalExternalDensityLocality.untruncatedDensity F χ C e
      a.vector a.positive a.negative O τ α u hu) (Metric.ball O R) ∧
      (∫ X in Metric.ball O R, PhysicalExternalDensityLocality.untruncatedDensity F χ C e
        a.vector a.positive a.negative O τ α u hu X) ≤
        520 * ∫ X in Metric.ball O R, sourceEnergy O τ α f X :=
  PhysicalExternalDensityLocality.paper_density_bound F χ C e a.vector a.positive a.negative
    hτ hα hRone u hu hsupp he.2.1 he.2.2.1

variable (S : CoordinateSobolev.Data PhotonFock N)
  (joint : CoordinateComparisonSpectral.Data spectral)
  (friedrichs : StandardFriedrichsDivergence) (KR : StandardKatoRellich)
  (hD : HaslerHerbstDomain C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hG : HaslerHerbstGraphNorm C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hSA : SelfAdjointGraph (freeHilbertGraph (fun _ => 0) C (profile (N := N) F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e))

include S joint friedrichs KR hD hG hSA

theorem exists_uniform_estimate_of_data (hρ : 0 < ρ)
    {α : ℝ} (hα : 0 < α)
    (D : PhysicalFreePerturbationData.Data F χ C e spectral α)
    (hcore : AnnularCoreApproximation C (profile (N := N) F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ ρ / 16 ∧ r₀ < Real.exp (-2) ∧
      ∀ O ∈ Metric.ball O₀ r₀, ∀ (R : ℝ) (hR : 0 < R), R ≤ r₀ →
      ∀ τ : ℝ, D.parameter ≤ τ →
      ∀ (u : Reference (Fin N × Fin 3) (fun _ => 0))
        (hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u)
        (f : WaveSpace (Fin N × Fin 3)),
        IsLocalOperatorPair (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
          (profileBound F χ) (profile_bound F χ 0) e a.vector a.positive a.negative
          (Metric.ball O₀ (ρ / 2)) u hu f →
        AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R →
        Estimate F χ C e a spectral (D.family O) R hR τ α D.second D.enlargedSecond u hu f := by
  let b := a.truncated hρ
  have hex := PhysicalExternalCarleman.exists_uniform_estimate_of_data F χ C e b S spectral joint
    friedrichs KR hD hG hSA hα D hcore
  let rG := Classical.choose hex
  have hrG := Classical.choose_spec hex
  let r₀ := min rG (ρ / 16)
  have hr₀ : 0 < r₀ := lt_min hrG.1 (by positivity)
  have hrρ : r₀ ≤ ρ / 16 := min_le_right _ _
  let t := ρ / 8
  have ht : 0 < t := by dsimp [t]; positivity
  let η := (D.family O₀).cutoff t
  have hηs : ∀ x : Configuration N, x ∉ Metric.ball O₀ (ρ / 2) → η.scalar.weight x = 0 := by
    intro x hx
    apply cutoff_supported (D.family O₀) ht x
    have hh : ρ / 2 ≤ dist x O₀ := not_lt.mp hx
    change ¬dist x O₀ < 2 * t
    dsimp [t]
    linarith only [hh, hρ]
  have hηmem (x : Configuration N) (hx : η.scalar.weight x ≠ 0) : x ∈ Metric.ball O₀ (ρ / 2) :=
    Classical.byContradiction fun hnot => hx (hηs x hnot)
  refine ⟨r₀, hr₀, hrρ, (min_le_left _ _).trans_lt hrG.2.2.1, ?_⟩
  intro O hO R hR hRr₀ τ hτ u hu f hf hsupp
  have hball : Metric.ball O R ⊆ Metric.ball O₀ t := by
    intro x hx
    have hdist := dist_triangle x O O₀
    change dist x O₀ < t
    have hOx : dist O O₀ < r₀ := hO
    have hxO : dist x O < R := hx
    dsimp [t]
    linarith only [hdist, hOx, hxO, hRr₀, hrρ]
  have hballBig : Metric.ball O₀ t ⊆ Metric.ball O₀ (ρ / 2) := by
    intro x hx
    change dist x O₀ < ρ / 2
    have hh : dist x O₀ < t := hx
    dsimp [t] at hh
    linarith only [hh, hρ]
  have hs := PhysicalExternalSource.annularSupport_supported_ball _ hsupp
  have hsInner : ∀ᵐ x ∂volume, x ∉ Metric.ball O₀ t → inclusion (Fin N × Fin 3) (fun _ => 0) u x = 0 :=
    hs.mono fun x hx hn => hx (fun h => hn (hball h))
  have hsBig : ∀ᵐ x ∂volume, x ∉ Metric.ball O₀ (ρ / 2) → inclusion (Fin N × Fin 3) (fun _ => 0) u x = 0 :=
    hsInner.mono fun x hx hn => hx (fun h => hn (hballBig h))
  have hU := a.agreement hρ (inclusion (Fin N × Fin 3) (fun _ => 0) u) hsBig
  have hu' : ExternalDomain (fun _ => 0) b.vector b.positive b.negative u :=
    domain_congr (fun _ => 0) a.vector b.vector a.positive a.negative b.positive b.negative u hu hU
  have hη := cutoff_action (D.family O₀) ht (inclusion (Fin N × Fin 3) (fun _ => 0) u) hsInner
  have hop := PhysicalLocalTruncation.operatorPair_of_local (fun _ => 0) C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
    a.vector b.vector a.positive a.negative b.positive b.negative η hηs
    (fun i x hx => (a.truncated_vector_eq hρ i (hηmem x hx)).symm)
    (fun x hx => (a.truncated_positive_eq hρ (hηmem x hx)).symm)
    (fun x hx => (a.truncated_negative_eq hρ (hηmem x hx)).symm)
    u hu hu' hU hη.1 hη.2.1 hη.2.2 f hf
  have he := hrG.2.2.2 O R hR (hRr₀.trans (min_le_left _ _)) τ hτ u hu'
    (η.scalar.multiplier f) hop hsupp
  have hηone : ∀ x ∈ Metric.ball O R, η.scalar.weight x = 1 := by
    intro x hx
    have hh : dist x O₀ < t := hball hx
    exact (congrArg (fun w : Configuration N → ℝ => w x) ((D.family O₀).weight t ht)).trans
      (buffered_scaled_one ht (by linarith only [hh, ht]))
  have hsource := weighted_integral_on_eq η.scalar f (centeredSourceWeight O τ α) measurableSet_ball
    hηone he.2.2.2.2.2 he.1
  have hdensity := PhysicalExternalDensityLocality.density_congr F χ C e
    a.vector b.vector a.positive a.negative b.positive b.negative O τ α u hu hu' hU
  have hI : Integrable (PhysicalExternalEnergy.density F χ C e a.vector a.positive a.negative O τ α u hu) :=
    he.2.1.congr (Filter.EventuallyEq.of_eq hdensity.symm)
  have hdensityIntegral := congrArg (fun z : Configuration N → ℝ => ∫ X, z X) hdensity
  have hbound := hdensityIntegral.le.trans
    (he.2.2.1.trans_eq (congrArg (fun z : ℝ => 520 * z) hsource.2))
  have hstandard := (congrArg (fun z : ℝ => PhysicalMixedSeries.Bound spectral
    (PhysicalFractionalCarleman.localized (D.family O) R hR τ α u) (dyadicBeta α R) (radius R)
    τ (4 * 6144) (4 * D.second) z) hsource.2).mp he.2.2.2.1
  have henlarged := (congrArg (fun z : ℝ => PhysicalMixedSeries.Bound spectral
    (PhysicalEnlargedFractionalCarleman.localized (D.family O) R hR τ α u) (dyadicBeta α R) (radius R)
    τ (4 * 40960) (4 * D.enlargedSecond) z) hsource.2).mp he.2.2.2.2.1
  exact ⟨hsource.1, hI, hbound, hstandard, henlarged⟩

open PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.SphereCoreGeometry
  PfHk.OrdinaryPolarSobolevChart

/-- The public local endpoint has no physical multiplier, weighted-error,
operator-domain identification for external coefficients, or free Carleman
estimate among its hypotheses. -/
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
      ∀ (u : Reference (Fin N × Fin 3) (fun _ => 0))
        (hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u)
        (f : WaveSpace (Fin N × Fin 3)),
        IsLocalOperatorPair (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
          (profileBound F χ) (profile_bound F χ 0) e a.vector a.positive a.negative
          (Metric.ball O₀ (ρ / 2)) u hu f →
        AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R →
        Estimate F χ C e a spectral (family O) R hR τ α C₂ C₂e u hu f := by
  have hex := PhysicalFreePerturbationData.exists_data F χ C e hUV W B P G charts L hN
    coreDensity core spectral hD hG α hα
  let D := Classical.choice hex
  have hfull := exists_uniform_estimate_of_data F χ C e a spectral S joint friedrichs KR
    hD hG hSA hρ hα D (core 0)
  let r₀ := Classical.choose hfull
  have hr := Classical.choose_spec hfull
  exact ⟨r₀, D.parameter, D.second, D.enlargedSecond, D.family,
    hr.1, hr.2.1, hr.2.2.1, D.parameter_ge_one, D.second_nonneg, D.enlargedSecond_nonneg, hr.2.2.2⟩

end PfHk.PhysicalLocalExternalCarleman
