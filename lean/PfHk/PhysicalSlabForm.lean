import PfHk.CompactSlabOperators
import PfHk.SlabFormAlgebra
import PfHk.CenteredSphereAngularField
import PfHk.CenteredSphereRadiationProduct

/-! The actual gauged kinetic and radiation form on a finite cylinder
slab, acting on the ordinary Sobolev chart. Its continuity is proved from
bounded multiplication by the constructed physical coefficients. -/

noncomputable section
namespace PfHk.PhysicalSlabForm

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalWeyl
  GptLean.PhysicalPFReference GptLean.PhysicalPolarization GptLean.Representability
  GptLean.SymmetricLift PfHk.PhysicalFieldRegularity PfHk.PolarCalculus
  PfHk.OrdinaryPolarSobolevChart
open scoped InnerProductSpace ENNReal
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 250000
local instance slabFormPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance slabFormAnalysisRealInner : InnerProductSpace ℝ CenteredSphereRadiationEnergy.AnalysisSpace :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] kernelField radiationAnalysis coefficientTensor
  radiationGraphInclusion CenteredSphereRadiationEnergy.tensorMap
  PhysicalPFReference.referenceSubspace

private theorem continuous_real_pair {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedSpace ℂ H]
    (L : E →L[ℂ] H) (z : H) : Continuous (fun v => inner ℝ (L v) z) :=
  L.continuous.inner continuous_const

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)

def coefficient (j : Fin N × Fin 3) (p : Slab N) : WeightedPhotonKernel :=
  CenteredSphereAngularField.coefficient F χ hUV e O j p.1 p.2

theorem coefficient_continuous (j : Fin N × Fin 3) : Continuous (coefficient F χ hUV e O j) := by
  have hθ : Continuous (fun p : Slab N => p.2.val) := continuous_subtype_val.comp continuous_snd
  have hr : Continuous (fun p : Slab N => Real.exp (-p.1)) := Real.continuous_exp.comp continuous_fst.neg
  have hζ : Continuous (fun _ : Slab N => EuclideanSpace.single j (1 : ℝ)) := continuous_const
  have h := (CenteredRadialGauge.angularLabel_joint_continuous F χ hUV e O).comp
    (hθ.prodMk (hζ.prodMk hr))
  convert! h using 1

def fieldFamily (j : Fin N × Fin 3) (p : Slab N) : RadiationGraphSpace →L[ℂ] PhotonFock :=
  kernelField C (coefficient F χ hUV e O j p)

theorem fieldFamily_continuous (j : Fin N × Fin 3) : Continuous (fieldFamily F χ hUV e O C j) := by
  convert! (kernelFieldMap C).continuous.comp (coefficient_continuous F χ hUV e O j) using 1

def field (a b : ℝ) (j : Fin N × Fin 3) : RadiationSlab N a b →L[ℂ] PhotonSlab N a b :=
  CompactSlabOperators.lift a b (fieldFamily F χ hUV e O C j) (fieldFamily_continuous F χ hUV e O C j)

def energyLabel (p : Slab N) : Lp ℂ 2 photonMeasure :=
  CenteredRadialGauge.inverseSqrtLabel F χ hUV e O (chartPoint N p)

theorem energyLabel_continuous : Continuous (energyLabel F χ hUV e O) := by
  have hx : Continuous (chartPoint N) :=
    (Real.continuous_exp.comp continuous_fst.neg).smul (continuous_subtype_val.comp continuous_snd)
  exact ((CenteredRadialGauge.sqrtLabel_continuous F χ hUV e O).comp hx).const_smul (-Complex.I)

def analysisFamily (p : Slab N) : RadiationGraphSpace →L[ℂ] CenteredSphereRadiationEnergy.AnalysisSpace :=
  radiationAnalysis + CenteredSphereRadiationEnergy.tensorMap (energyLabel F χ hUV e O p)

theorem analysisFamily_continuous : Continuous (analysisFamily F χ hUV e O) := by
  convert! SlabFormAlgebra.continuous_affine_clm radiationAnalysis
    CenteredSphereRadiationEnergy.tensorMap (energyLabel_continuous F χ hUV e O) using 1

def analysis (a b : ℝ) : RadiationSlab N a b →L[ℂ]
    Lp CenteredSphereRadiationEnergy.AnalysisSpace 2 (slabMeasure N a b) :=
  CompactSlabOperators.lift a b (analysisFamily F χ hUV e O) (analysisFamily_continuous F χ hUV e O)

def radiusWeight {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (a b : ℝ) :
    Lp H 2 (slabMeasure N a b) →L[ℂ] Lp H 2 (slabMeasure N a b) :=
  CompactSlabOperators.lift a b
    (fun p : Slab N => ((Real.exp (-p.1)^2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H)
    (((Complex.continuous_ofReal.comp ((Real.continuous_exp.comp continuous_fst.neg).pow 2))).smul continuous_const)

variable {c a b : ℝ} (P : SobolevChart N c a b)

def radialMap : Reference (Fin N × Fin 3) (fun _ => 0) →L[ℂ] PhotonSlab N a b :=
  P.time + (c : ℂ) • P.value

def angularMap (j : Fin N × Fin 3) :
    Reference (Fin N × Fin 3) (fun _ => 0) →L[ℂ] PhotonSlab N a b :=
  P.gradient j + Complex.I • (field F χ hUV e O C a b j).comp P.radiation

def analysisMap : Reference (Fin N × Fin 3) (fun _ => 0) →L[ℂ]
    Lp CenteredSphereRadiationEnergy.AnalysisSpace 2 (slabMeasure N a b) :=
  (analysis F χ hUV e O a b).comp P.radiation

def form (v u : Reference (Fin N × Fin 3) (fun _ => 0)) : ℝ :=
  inner ℝ (radialMap (N := N) P v) (radialMap (N := N) P u) +
    (∑ j, inner ℝ (angularMap F χ hUV e O C P j v) (angularMap F χ hUV e O C P j u)) +
    2 * inner ℝ (analysisMap F χ hUV e O P v)
      (radiusWeight a b (analysisMap F χ hUV e O P u))

theorem form_continuous_left (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    Continuous (fun v => form F χ hUV e O C P v u) := by
  convert! SlabFormAlgebra.continuous_form_left (radialMap (N := N) P)
    (angularMap F χ hUV e O C P) (analysisMap F χ hUV e O P) (radiusWeight a b) u using 1


end PfHk.PhysicalSlabForm
