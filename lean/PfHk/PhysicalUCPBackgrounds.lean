import PfHk.PhysicalUniformOperatorCarleman

/-! Ordinary background inputs of the public physical continuation theorem.
The record is transparent and introduces no Carleman, form-smallness,
scalar recurrence Sobolev, or unique-continuation hypothesis. -/

noncomputable section
namespace PfHk.PhysicalUCPConsequences

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.CenteredPhysicalReference PfHk.PhysicalFieldRegularity PfHk.PhysicalLocalEnergy
  PfHk.PhysicalOperatorDomain PfHk.PhysicalCarlemanInput PfHk.PhysicalCutoffCommutator
  PfHk.PhysicalExternalOperator PfHk.KatoRellichBackground PfHk.FriedrichsDivergenceBackground
  PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.SphereCoreGeometry
  PfHk.OrdinaryPolarSobolevChart
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

local instance consequencesPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PfHk.PhysicalDyadicEnergy.dyadicEnergyPhotonRealInner

attribute [local irreducible] inclusion PhysicalPFReference.covariant radiation roughMultiply externalCovariant
  PhysicalPFReference.referenceSubspace FreeGraph IsOperatorPair IsLocalOperatorPair IsExternalWeakEigenstate

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)

set_option maxHeartbeats 200000 in
/-- A transparent collection of the ordinary spectral, operator, UV and
core inputs already used by `PhysicalUCP.uniform_operatorCarleman`.
No continuation conclusion or physical weighted estimate is a field. -/
structure Backgrounds where
  coordinateSobolev : CoordinateSobolev.Data PhotonFock N
  spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3)
  joint : CoordinateComparisonSpectral.Data (N := N) spectral
  friedrichs : StandardFriedrichsDivergence
  katoRellich : StandardKatoRellich
  domain : HaslerHerbstDomain C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e
  graphNorm : HaslerHerbstGraphNorm C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e
  selfAdjoint : SelfAdjointGraph (freeHilbertGraph (fun _ => 0) C (profile (N := N) F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e)
  ultraviolet : CarlemanUV χ
  weyl : ConcreteWeylLaw photonMeasure
  weylGraph : StandardWeylGraphC1 weyl
  polar : StandardPolarCalculus (Fin N × Fin 3) PhotonFock
  sphereGradient : StandardSphereGradient (Fin N × Fin 3) PhotonFock
  charts : StandardPolarSobolevCharts N
  logPolar : StandardLogPolarCalculus (Fin N × Fin 3)
  coreDensity : WeylCoreReference.StandardWeylFormCoreDensity weyl weylGraph
  annularCore : ∀ O : Configuration N,
    AnnularCoreApproximation C (profile (N := N) F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e

variable {F χ C e}

private theorem dimension_gt_two (hN : 0 < N) : 2 < Fintype.card (Fin N × Fin 3) := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  omega

private theorem physical_nonempty (hN : 0 < N) : Nonempty (Fin N × Fin 3) :=
  ⟨(⟨0, hN⟩, 0)⟩

theorem Backgrounds.uniform_operatorCarleman (B : Backgrounds (N := N) F χ C e)
    {U : Set (Configuration N)} (a : PhysicalUCPCoefficients.Data N U)
    (hN : 0 < N) (hU : IsOpen U) (E : ℝ) :
    UniformLocalOperatorCarleman (fun _ => 0) C (profile (N := N) F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
      e a.vector a.positive a.negative E (1 / 2) U :=
  PhysicalUCP.uniform_operatorCarleman F χ C e a B.coordinateSobolev B.spectral B.joint
    B.friedrichs B.katoRellich B.domain B.graphNorm B.selfAdjoint hU B.ultraviolet
    B.weyl B.weylGraph B.polar B.sphereGradient B.charts B.logPolar
    (by have hd := dimension_gt_two hN; omega) B.coreDensity B.annularCore
    (1 / 2) (by norm_num) E

end PfHk.PhysicalUCPConsequences
