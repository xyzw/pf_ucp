import PfHk.PhysicalCoreApproximation
import PfHk.PhysicalUCPBackgrounds

/-! The public background record with supported core approximation derived.

`CoreBackgrounds` lists the same ordinary inputs as `Backgrounds`, except
that the supported approximation field is replaced by the plain
operator-core property of the smooth finite-photon core.
`CoreBackgrounds.toBackgrounds` derives supported approximation at every
electronic center by the cutoff argument of `ucp-core-lemma`. Every
continuation and Hohenberg–Kohn endpoint stated for `Backgrounds`
therefore holds under `CoreBackgrounds`. -/

noncomputable section
namespace PfHk.PhysicalUCPConsequences

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.CenteredPhysicalReference PfHk.PhysicalFieldRegularity PfHk.PhysicalLocalEnergy
  PfHk.PhysicalOperatorDomain PfHk.PhysicalCarlemanInput PfHk.PhysicalCutoffCommutator
  PfHk.PhysicalExternalOperator PfHk.KatoRellichBackground PfHk.FriedrichsDivergenceBackground
  PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.SphereCoreGeometry
  PfHk.OrdinaryPolarSobolevChart PfHk.PhysicalCoreApproximation
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

local instance coreBackgroundsPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PfHk.PhysicalDyadicEnergy.dyadicEnergyPhotonRealInner

attribute [local irreducible] inclusion PhysicalPFReference.covariant radiation roughMultiply externalCovariant
  PhysicalPFReference.referenceSubspace FreeGraph IsOperatorPair IsLocalOperatorPair IsExternalWeakEigenstate

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)

/-- The free self-adjoint graph has a dense domain inside the range of
the form-domain inclusion. -/
theorem referenceInclusion_denseRange
    (hSA : SelfAdjointGraph (freeHilbertGraph (fun _ => 0) C (profile (N := N) F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e)) :
    DenseRange (inclusion (Fin N × Fin 3) (fun _ => 0)) := by
  apply hSA.dense.mono
  intro x hx
  have hgraph := Classical.choose_spec hx
  let u := Classical.choose hgraph
  have hu := Classical.choose_spec hgraph
  exact ⟨u, hu.1⟩

/-- Supported core approximation at every electronic center, from the
operator-core property. The actual form factors are continuous. -/
theorem annularCore_of_globalCore
    (hSA : SelfAdjointGraph (freeHilbertGraph (fun _ => 0) C (profile (N := N) F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e))
    (hglobal : ∀ O : Configuration N,
      GlobalCoreApproximation C (profile (N := N) F χ O) (profile_measurable F χ O)
        (profileBound F χ) (profile_bound F χ O) e)
    (O : Configuration N) :
    AnnularCoreApproximation C (profile (N := N) F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e :=
  annular_of_global C (profile (N := N) F χ O) (profile_measurable F χ O)
    (profileBound F χ) (profile_bound F χ O) e (profile_continuous F χ O)
    (referenceInclusion_denseRange F χ C e hSA) (hglobal O)

set_option maxHeartbeats 200000 in
/-- The ordinary inputs of the public continuation theorems, with the
operator-core property in place of supported core approximation. No
continuation conclusion or physical weighted estimate is a field. -/
structure CoreBackgrounds where
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
  globalCore : ∀ O : Configuration N,
    GlobalCoreApproximation C (profile (N := N) F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e

variable {F χ C e}

set_option maxHeartbeats 200000 in
/-- The background record used by the public endpoints. Its supported
approximation field is proved, not assumed. -/
def CoreBackgrounds.toBackgrounds (B : CoreBackgrounds (N := N) F χ C e) :
    Backgrounds (N := N) F χ C e where
  coordinateSobolev := B.coordinateSobolev
  spectral := B.spectral
  joint := B.joint
  friedrichs := B.friedrichs
  katoRellich := B.katoRellich
  domain := B.domain
  graphNorm := B.graphNorm
  selfAdjoint := B.selfAdjoint
  ultraviolet := B.ultraviolet
  weyl := B.weyl
  weylGraph := B.weylGraph
  polar := B.polar
  sphereGradient := B.sphereGradient
  charts := B.charts
  logPolar := B.logPolar
  coreDensity := B.coreDensity
  annularCore := annularCore_of_globalCore F χ C e B.selfAdjoint B.globalCore

end PfHk.PhysicalUCPConsequences
