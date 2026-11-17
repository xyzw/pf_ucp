import PfHk.PhysicalShiftedOperatorCarleman
import PfHk.PhysicalOpenUCPCoefficients
import PfHk.PhysicalUCPBackgrounds

/-! The physical uniform operator Carleman hypothesis used by continuation
is derived from the local full Hamiltonian theorem. Radius choices include
the open-region geometry and energy-shift absorption. -/

noncomputable section
namespace PfHk.PhysicalOpenUCP

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.CenteredPhysicalReference PfHk.PhysicalFieldRegularity PfHk.PhysicalLocalEnergy
  PfHk.PhysicalOperatorDomain PfHk.PhysicalCarlemanInput PfHk.PhysicalCutoffCommutator
  PfHk.PhysicalExternalOperator PfHk.KatoRellichBackground
  PfHk.FriedrichsDivergenceBackground

local instance ucpPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PfHk.PhysicalDyadicEnergy.dyadicEnergyPhotonRealInner

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

attribute [local irreducible] inclusion covariant radiation roughMultiply FreeGraph
  PhysicalPFReference.referenceSubspace IsOperatorPair IsLocalOperatorPair

private theorem subradius {X : Type*} [MetricSpace X] {U : Set X}
    (hU : IsOpen U) {O : X} (hO : O ∈ U) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ∃ R : ℝ, 0 < R ∧ R ≤ r ∧ R ≤ s ∧ Metric.ball O (4 * R) ⊆ U := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU O hO
  let R := min r (min s (δ / 4))
  have hR : 0 < R := lt_min hr (lt_min hs (by positivity))
  have hRδ : R ≤ δ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨R, hR, min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (Metric.ball_subset_ball (by linarith only [hRδ])).trans hball⟩

variable {N : ℕ} {U : Set (Configuration N)}
  (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (a : PhysicalOpenUCPCoefficients.Data N U)
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

include S spectral joint friedrichs KR hD hG hSA

theorem uniform_operatorCarleman_of_data (hU : IsOpen U)
    {α : ℝ} (hα : 0 < α)
    (D : PhysicalFreePerturbationData.Data F χ C e spectral α)
    (hcore : AnnularCoreApproximation C (profile (N := N) F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e) (E : ℝ) :
    UniformLocalOperatorCarleman (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e a.vector a.positive a.negative E α U := by
  have hexRatio := EnergyShiftAbsorption.exists_radius_ratio α
  let Rc := Classical.choose hexRatio
  have hRc := Classical.choose_spec hexRatio
  intro O₀ hO₀
  have hexB := a.local_coefficients O₀ hO₀
  let ρ := Classical.choose hexB
  have hρ := Classical.choose_spec hexB
  let b := a.localData O₀ ρ hρ.2
  have hexLocal := PhysicalLocalExternalCarleman.exists_uniform_estimate_of_data
    F χ C e b spectral S joint friedrichs KR hD hG hSA hρ.1 hα D hcore
  let rG := Classical.choose hexLocal
  have hrG := Classical.choose_spec hexLocal
  have hexR := subradius hU hO₀ hrG.1 hRc.1
  let R₀ := Classical.choose hexR
  have hR₀ := Classical.choose_spec hexR
  let τ₀ := max D.parameter (max 1 (2080 * E ^ 2))
  have hτ₀ : 1 ≤ τ₀ := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨R₀, τ₀, 2080, hR₀.1, (hR₀.2.1.trans_lt hrG.2.2.1).le,
    hτ₀, by norm_num, hR₀.2.2.2, ?_⟩
  intro O hO R hR hRR₀ u hu f hf hsupp τ hτ
  have hOG : O ∈ Metric.ball O₀ rG := Metric.ball_subset_ball hR₀.2.1 hO
  have hRG : R ≤ rG := hRR₀.trans hR₀.2.1
  have hτD : D.parameter ≤ τ := (le_max_left _ _).trans hτ
  have hpair : IsLocalOperatorPair (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e b.vector b.positive b.negative
      (Metric.ball O₀ (ρ / 2)) u hu f := by
    unfold IsOperatorPair at hf
    unfold IsLocalOperatorPair
    exact fun v hv _ => hf v hv
  have he := hrG.2.2.2 O hOG R hR hRG τ hτD u hu f hpair hsupp
  have hτcube := EnergyShiftAbsorption.parameter_cube_bound E ((le_max_right _ _).trans hτ)
  have hRone : R < 1 := (hRG.trans_lt hrG.2.2.1).trans
    (Real.exp_lt_one_iff.mpr (by norm_num : (-2 : ℝ) < 0))
  exact (PhysicalOperatorCarlemanBridge.shifted_mass_estimate F χ C e b spectral he
    hτcube.1 hα hRone hsupp hτcube.2
    (fun r hr hrR => hRc.2.2 r hr (hrR.trans (hRR₀.trans hR₀.2.2.1)))).2.2

open PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.SphereCoreGeometry
  PfHk.OrdinaryPolarSobolevChart

/-- No physical Carleman premise occurs in this uniform continuation input. -/
theorem uniform_operatorCarleman (hU : IsOpen U) (hUV : CarlemanUV χ)
    (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
    (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
    (charts : StandardPolarSobolevCharts N) (L : StandardLogPolarCalculus (Fin N × Fin 3))
    (hN : 0 < Fintype.card (Fin N × Fin 3))
    (coreDensity : WeylCoreReference.StandardWeylFormCoreDensity W B)
    (core : ∀ O : Configuration N, AnnularCoreApproximation C (profile F χ O)
      (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e)
    (α : ℝ) (hα : 0 < α) (E : ℝ) :
    UniformLocalOperatorCarleman (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e a.vector a.positive a.negative E α U := by
  have hex := PhysicalFreePerturbationData.exists_data F χ C e hUV W B P G charts L hN
    coreDensity core spectral hD hG α hα
  exact uniform_operatorCarleman_of_data F χ C e a S spectral joint friedrichs KR hD hG hSA
    hU hα (Classical.choice hex) (core 0) E

omit S spectral joint friedrichs KR hD hG hSA in
/-- The same ordinary analytic backgrounds produce the local Carleman input
when coefficients are regular only on the specified open region. -/
theorem from_backgrounds
    (B : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e)
    (hN : 0 < N) (hU : IsOpen U) (E : ℝ) :
    UniformLocalOperatorCarleman (fun _ => 0) C (profile (N := N) F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
      e a.vector a.positive a.negative E (1 / 2) U := by
  have hd : 0 < Fintype.card (Fin N × Fin 3) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  exact uniform_operatorCarleman F χ C e a B.coordinateSobolev B.spectral B.joint
    B.friedrichs B.katoRellich B.domain B.graphNorm B.selfAdjoint hU B.ultraviolet
    B.weyl B.weylGraph B.polar B.sphereGradient B.charts B.logPolar
    hd B.coreDensity B.annularCore (1 / 2) (by norm_num) E

end PfHk.PhysicalOpenUCP
