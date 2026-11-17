import PfHk.PhysicalSlabForm
import PfHk.PolarInnerCalculus
import PfHk.L2QuadraticForms

/-! Representative formulas for the actual bounded slab form. These
identities connect the Sobolev chart to pointwise physical polar algebra. -/

noncomputable section
namespace PfHk.PhysicalSlabForm

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalWeyl
  GptLean.PhysicalPFReference GptLean.PhysicalPolarization GptLean.Representability
  GptLean.SymmetricLift PfHk.PhysicalFieldRegularity PfHk.PolarCalculus
  PfHk.OrdinaryPolarSobolevChart
open scoped InnerProductSpace ENNReal
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 250000
local instance slabEvalPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance slabEvalAnalysisRealInner : InnerProductSpace ℝ CenteredSphereRadiationEnergy.AnalysisSpace :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] kernelField radiationAnalysis coefficientTensor
  radiationGraphInclusion PhysicalPFReference.referenceSubspace

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  {c a b : ℝ} (P : SobolevChart N c a b)

def radialFunction (u : Reference (Fin N × Fin 3) (fun _ => 0)) (p : Slab N) : PhotonFock :=
  timeFunction N c u p + (c : ℂ) • valueFunction N c u p

def angularFunction (j : Fin N × Fin 3) (u : Reference (Fin N × Fin 3) (fun _ => 0)) (p : Slab N) : PhotonFock :=
  gradientFunction N c j u p + Complex.I • kernelField C (coefficient F χ hUV e O j p)
    (radiationFunction N c u p)

def analysisFunction (u : Reference (Fin N × Fin 3) (fun _ => 0)) (p : Slab N) :
    CenteredSphereRadiationEnergy.AnalysisSpace :=
  RadialGaugeRadiation.displacedAnalysis (energyLabel F χ hUV e O p) (radiationFunction N c u p)

def radialAt (u : Reference (Fin N × Fin 3) (fun _ => 0)) : PhotonSlab N a b :=
  radialMap (N := N) P u
def angularAt (j : Fin N × Fin 3) (u : Reference (Fin N × Fin 3) (fun _ => 0)) : PhotonSlab N a b :=
  angularMap F χ hUV e O C P j u
def analysisAt (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    Lp CenteredSphereRadiationEnergy.AnalysisSpace 2 (slabMeasure N a b) :=
  analysisMap F χ hUV e O P u

theorem radialMap_ae (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    radialMap (N := N) P u =ᵐ[slabMeasure N a b] radialFunction (c := c) u := by
  have h := L2QuadraticForms.add_smul_ae (c : ℂ) (P.time u) (P.value u) (P.value_ae u).ae
  filter_upwards [h, (P.time_ae u).ae] with p hp ht
  exact hp.trans (congrArg (fun v : PhotonFock => v + (c : ℂ) • valueFunction N c u p) ht)

theorem field_ae (j : Fin N × Fin 3) (q : RadiationSlab N a b) :
    field F χ hUV e O C a b j q =ᵐ[slabMeasure N a b]
      fun p => kernelField C (coefficient F χ hUV e O j p) (q p) :=
  CompactSlabOperators.lift_ae a b (fieldFamily F χ hUV e O C j)
    (fieldFamily_continuous F χ hUV e O C j) q

theorem angularMap_ae (j : Fin N × Fin 3) (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    angularMap F χ hUV e O C P j u =ᵐ[slabMeasure N a b]
      angularFunction F χ hUV e O C (c := c) j u := by
  have hfield := field_ae F χ hUV e O C (a := a) (b := b) j (P.radiation u)
  have h := L2QuadraticForms.add_smul_ae Complex.I (P.gradient j u)
    (field F χ hUV e O C a b j (P.radiation u)) hfield
  filter_upwards [h, (P.gradient_ae j u).ae, (P.radiation_ae u).ae] with p hp hg hq
  exact hp.trans (congrArg₂ (fun v : PhotonFock => fun q : RadiationGraphSpace =>
    v + Complex.I • kernelField C (coefficient F χ hUV e O j p) q) hg hq)

theorem analysisFamily_apply (p : Slab N) (q : RadiationGraphSpace) :
    analysisFamily F χ hUV e O p q = RadialGaugeRadiation.displacedAnalysis (energyLabel F χ hUV e O p) q := by
  have he : analysisFamily F χ hUV e O p q = radiationAnalysis q +
      CenteredSphereRadiationEnergy.tensorMap (energyLabel F χ hUV e O p) q := rfl
  exact he.trans (congrArg (fun z : CenteredSphereRadiationEnergy.AnalysisSpace => radiationAnalysis q + z)
    (CenteredSphereRadiationEnergy.tensorMap_apply (energyLabel F χ hUV e O p) q))

theorem analysisMap_ae (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    analysisMap F χ hUV e O P u =ᵐ[slabMeasure N a b] analysisFunction F χ hUV e O (c := c) u := by
  have h := CompactSlabOperators.lift_ae a b (analysisFamily F χ hUV e O)
    (analysisFamily_continuous F χ hUV e O) (P.radiation u)
  filter_upwards [h, (P.radiation_ae u).ae] with p hp hq
  exact hp.trans ((congrArg (analysisFamily F χ hUV e O p) hq).trans
    (analysisFamily_apply F χ hUV e O p (radiationFunction N c u p)))

theorem radiusWeight_ae {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (u : Lp H 2 (slabMeasure N a b)) :
    radiusWeight a b u =ᵐ[slabMeasure N a b] fun p => ((Real.exp (-p.1)^2 : ℝ) : ℂ) • u p := by
  convert! CompactSlabOperators.lift_ae a b
    (fun p : Slab N => ((Real.exp (-p.1)^2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H) _ u using 1

theorem radiusWeight_real_ae {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]
    (u : Lp H 2 (slabMeasure N a b)) {f : Slab N → H}
    (hu : u =ᵐ[slabMeasure N a b] f) :
    radiusWeight a b u =ᵐ[slabMeasure N a b] fun p => Real.exp (-p.1)^2 • f p := by
  filter_upwards [radiusWeight_ae u, hu] with p hp hq
  exact hp.trans ((congrArg (fun z : H => ((Real.exp (-p.1)^2 : ℝ) : ℂ) • z) hq).trans
    (IsScalarTower.algebraMap_smul ℂ (Real.exp (-p.1)^2) (f p)))

theorem radialAt_ae (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    LpRepresents (slabMeasure N a b) (radialAt P u) (radialFunction (c := c) u) := radialMap_ae P u

theorem angularAt_ae (j : Fin N × Fin 3) (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    LpRepresents (slabMeasure N a b) (angularAt F χ hUV e O C P j u)
      (angularFunction F χ hUV e O C (c := c) j u) := angularMap_ae F χ hUV e O C P j u

theorem analysisAt_ae (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    LpRepresents (slabMeasure N a b) (analysisAt F χ hUV e O P u)
      (analysisFunction F χ hUV e O (c := c) u) := analysisMap_ae F χ hUV e O P u

end PfHk.PhysicalSlabForm
