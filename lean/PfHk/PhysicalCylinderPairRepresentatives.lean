import PfHk.PhysicalCylinderRepresentatives
import PfHk.PhysicalChartCore
import PfHk.PhysicalSlabTestEvaluation

/-! Sphere representatives used to evaluate the bilinear slab form. -/

noncomputable section
namespace PfHk.PhysicalSlabCoreForm

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.SphereCoreGeometry PfHk.CenteredRadialGauge
open PfHk.SphereAngularField (Sphere SpherePhoton)
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000
local instance cylinderPairRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance cylinderPairAnalysisRealInner : InnerProductSpace ℝ CenteredSphereRadiationEnergy.AnalysisSpace :=
  InnerProductSpace.rclikeToReal ℂ _
local instance cylinderPairRadiationRealNormed : NormedSpace ℝ RadiationGraphSpace :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance cylinderPairPhotonModule : Module ℝ PhotonFock := cylinderPairRealInner.toNormedSpace.toModule
local instance cylinderPairPhotonSMul : SMul ℝ PhotonFock := cylinderPairPhotonModule.toSMul
local instance cylinderPairRadiationModule : Module ℝ RadiationGraphSpace :=
  (NormedSpace.restrictScalars ℝ ℂ RadiationGraphSpace).toModule
local instance cylinderPairRadiationSMul : SMul ℝ RadiationGraphSpace := cylinderPairRadiationModule.toSMul
local instance cylinderPairAnalysisModule : Module ℝ CenteredSphereRadiationEnergy.AnalysisSpace :=
  cylinderPairAnalysisRealInner.toNormedSpace.toModule
local instance cylinderPairAnalysisSMul : SMul ℝ CenteredSphereRadiationEnergy.AnalysisSpace := cylinderPairAnalysisModule.toSMul
attribute [local irreducible] PhysicalCylinderSource.curve rawCore
  CoreCurve.conformal CoreVector.scale kernelField RadialGaugeRadiation.displacedAnalysis
  PhysicalChartCore.analysisValue graphLift SmoothCore.rootWave

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
  (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
  (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
  {s : Set (Configuration N)} (a : SmoothCore s)

theorem curve_analysis_ae (c t : ℝ) :
    CenteredSphereRadiationEnergy.analysis F χ hUV e O t
      ((PhysicalCylinderSource.curve F χ hUV e O C W B P G a c).value t).radiation =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => PhysicalChartCore.analysisValue F χ hUV e O W a c (t, θ) := by
  filter_upwards [CenteredSphereRadiationEnergy.analysis_ae F χ hUV e O t
    ((PhysicalCylinderSource.curve F χ hUV e O C W B P G a c).value t).radiation,
    PhysicalCylinderSource.curve_radiation_ae F χ hUV e O C W B P G a c t] with θ hp hq
  apply hp.trans
  unfold PhysicalChartCore.analysisValue
  have hm := SlabFormAlgebra.clm_of_smul_rep (PhysicalSlabForm.analysisFamily F χ hUV e O (t, θ))
    (Real.exp (-c*t)) hq
  have hleft := PhysicalSlabForm.analysisFamily_apply F χ hUV e O (t, θ)
    (((PhysicalCylinderSource.curve F χ hUV e O C W B P G a c).value t).radiation θ)
  have hright := PhysicalSlabForm.analysisFamily_apply F χ hUV e O (t, θ)
    (graphLift F χ hUV e O W (Real.exp (-t) • θ.val) (a.rootWave (Real.exp (-t) • θ.val)))
  exact hleft.symm.trans (hm.trans (SlabFormAlgebra.real_smul_congr (Real.exp (-c*t)) hright))

theorem test_angular_ae (v : CoreVector N) (j : Fin N × Fin 3) (t : ℝ) :
    CenteredSphereAngularField.angularVector F χ hUV e O C v.gradient v.radiation j t =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => PhysicalSlabTestEvaluation.angularFiber F χ hUV e O C v j (t, θ) :=
  CenteredSphereAngularField.angularVector_ae F χ hUV e O C v.gradient v.radiation j t

theorem test_analysis_ae (v : CoreVector N) (t : ℝ) :
    CenteredSphereRadiationEnergy.analysis F χ hUV e O t v.radiation =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => PhysicalSlabTestEvaluation.analysisFiber F χ hUV e O v (t, θ) :=
  CenteredSphereRadiationEnergy.analysis_ae F χ hUV e O t v.radiation

end PfHk.PhysicalSlabCoreForm
