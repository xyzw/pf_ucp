import PfHk.PhysicalSlabFormEvaluation
import PfHk.SlabFormAlgebra

/-! Actual bounded slab maps on a separated ordinary sphere test. -/

noncomputable section
namespace PfHk.PhysicalSlabTestEvaluation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PolarCalculus PfHk.SphereCoreGeometry PfHk.OrdinaryPolarSobolevChart
open scoped InnerProductSpace ENNReal
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000
local instance slabTestPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance slabTestAnalysisRealInner : InnerProductSpace ℝ CenteredSphereRadiationEnergy.AnalysisSpace :=
  InnerProductSpace.rclikeToReal ℂ _
local instance slabTestPhotonModule : Module ℝ PhotonFock := slabTestPhotonRealInner.toNormedSpace.toModule
local instance slabTestPhotonSMul : SMul ℝ PhotonFock := slabTestPhotonModule.toSMul
local instance slabTestRadiationModule : Module ℝ RadiationGraphSpace :=
  (NormedSpace.restrictScalars ℝ ℂ RadiationGraphSpace).toModule
local instance slabTestRadiationSMul : SMul ℝ RadiationGraphSpace := slabTestRadiationModule.toSMul
local instance slabTestAnalysisModule : Module ℝ CenteredSphereRadiationEnergy.AnalysisSpace :=
  slabTestAnalysisRealInner.toNormedSpace.toModule
local instance slabTestAnalysisSMul : SMul ℝ CenteredSphereRadiationEnergy.AnalysisSpace := slabTestAnalysisModule.toSMul
attribute [local irreducible] PhysicalPFReference.referenceSubspace kernelField
  RadialGaugeRadiation.displacedAnalysis

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  {c l r : ℝ} (P : SobolevChart N c l r)
  (u : PhysicalPFReference.Reference (Fin N × Fin 3) (fun _ => 0))
  (v : CoreVector N) (η : ℝ → ℝ)

def angularFiber (j : Fin N × Fin 3) (p : Slab N) : PhotonFock :=
  v.gradient j p.2 + Complex.I • kernelField C (PhysicalSlabForm.coefficient F χ hUV e O j p)
    (v.radiation p.2)

def analysisFiber (p : Slab N) : CenteredSphereRadiationEnergy.AnalysisSpace :=
  RadialGaugeRadiation.displacedAnalysis (PhysicalSlabForm.energyLabel F χ hUV e O p) (v.radiation p.2)

attribute [local irreducible] angularFiber analysisFiber

theorem radial_ae
    (hv : LpRepresents (slabMeasure N l r) (P.value u) (fun p => η p.1 • v.ambient p.2))
    (ht : LpRepresents (slabMeasure N l r) (P.time u) (fun p => deriv η p.1 • v.ambient p.2)) :
    LpRepresents (slabMeasure N l r) (PhysicalSlabForm.radialMap (N := N) P u)
      (fun p => (deriv η p.1 + c*η p.1) • v.ambient p.2) := by
  unfold LpRepresents
  have ha := L2QuadraticForms.add_smul_ae (c : ℂ) (P.time u) (P.value u) hv.ae
  filter_upwards [ha, ht.ae] with p hp hd
  exact hp.trans (SlabFormAlgebra.radial_test_of_rep _ _ _ hd)

theorem angular_ae (j : Fin N × Fin 3)
    (hg : LpRepresents (slabMeasure N l r) (P.gradient j u) (fun p => η p.1 • v.gradient j p.2))
    (hq : LpRepresents (slabMeasure N l r) (P.radiation u)
      (fun p => SlabFormAlgebra.realScale (η p.1) (v.radiation p.2))) :
    LpRepresents (slabMeasure N l r) (PhysicalSlabForm.angularMap F χ hUV e O C P j u)
      (fun p => SlabFormAlgebra.realScale (η p.1) (angularFiber F χ hUV e O C v j p)) := by
  unfold LpRepresents
  have hf := PhysicalSlabForm.field_ae F χ hUV e O C j (P.radiation u)
  have ha := L2QuadraticForms.add_smul_ae Complex.I (P.gradient j u)
    (PhysicalSlabForm.field F χ hUV e O C l r j (P.radiation u)) hf
  filter_upwards [ha, hg.ae, hq.ae] with p hp hd hrad
  dsimp only [SlabFormAlgebra.realScale] at hrad ⊢
  apply hp.trans
  unfold angularFiber
  exact SlabFormAlgebra.angular_of_reps (kernelField C
    (PhysicalSlabForm.coefficient F χ hUV e O j p)).toLinearMap _ hd hrad

theorem analysis_ae
    (hq : LpRepresents (slabMeasure N l r) (P.radiation u)
      (fun p => SlabFormAlgebra.realScale (η p.1) (v.radiation p.2))) :
    LpRepresents (slabMeasure N l r) (PhysicalSlabForm.analysisMap F χ hUV e O P u)
      (fun p => SlabFormAlgebra.realScale (η p.1) (analysisFiber F χ hUV e O v p)) := by
  unfold LpRepresents
  have hf := CompactSlabOperators.lift_ae l r (PhysicalSlabForm.analysisFamily F χ hUV e O)
    (PhysicalSlabForm.analysisFamily_continuous F χ hUV e O) (P.radiation u)
  filter_upwards [hf, hq.ae] with p hp hrad
  dsimp only [SlabFormAlgebra.realScale] at hrad ⊢
  apply hp.trans
  unfold analysisFiber
  exact (SlabFormAlgebra.clm_of_smul_rep (PhysicalSlabForm.analysisFamily F χ hUV e O p)
    (η p.1) hrad).trans (SlabFormAlgebra.real_smul_congr _
      (PhysicalSlabForm.analysisFamily_apply F χ hUV e O p _))

end PfHk.PhysicalSlabTestEvaluation
