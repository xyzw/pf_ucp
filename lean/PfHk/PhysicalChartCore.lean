import PfHk.CenteredRadialGaugeFormCore
import PfHk.PhysicalSlabFormEvaluation
import PfHk.PolarChartAlgebra
import PfHk.PolarChartEvaluation

/-! Actual representative identities for the ordinary Sobolev chart of
the physical Weyl-transformed core. AE transport is solely the ordinary
polar quasi-measure-preserving map. -/

noncomputable section
namespace PfHk.PhysicalChartCore

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain
  PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.CenteredRadialGauge
  PfHk.OrdinaryPolarSobolevChart
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
local instance chartCorePhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance chartCoreAnalysisRealInner : InnerProductSpace ℝ CenteredSphereRadiationEnergy.AnalysisSpace :=
  InnerProductSpace.rclikeToReal ℂ _
local instance chartCorePhotonModule : Module ℝ PhotonFock :=
  chartCorePhotonRealInner.toNormedSpace.toModule
local instance chartCorePhotonSMul : SMul ℝ PhotonFock := chartCorePhotonModule.toSMul
local instance chartCoreRadiationModule : Module ℝ RadiationGraphSpace :=
  (NormedSpace.restrictScalars ℝ ℂ RadiationGraphSpace).toModule
local instance chartCoreRadiationSMul : SMul ℝ RadiationGraphSpace := chartCoreRadiationModule.toSMul
local instance chartCoreAnalysisModule : Module ℝ CenteredSphereRadiationEnergy.AnalysisSpace :=
  chartCoreAnalysisRealInner.toNormedSpace.toModule
local instance chartCoreAnalysisSMul : SMul ℝ CenteredSphereRadiationEnergy.AnalysisSpace := chartCoreAnalysisModule.toSMul
attribute [local irreducible] gaugedValue coreValue graphLift
  angularCore RadialGaugeRadiation.displacedAnalysis kernelField
  gaugedReference SlabFormAlgebra.realScale LpRepresents valueAt radiationAt gradientAt
  PhysicalSlabForm.radialAt PhysicalSlabForm.angularAt PhysicalSlabForm.analysisAt
  PhysicalPFReference.inclusion PhysicalPFReference.ordinary PhysicalPFReference.radiationSource
  PhysicalPFReference.referenceSubspace

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
  (S : StandardPolarSobolevCharts N) {c l r : ℝ}
  {s : Set (Configuration N)} (u : SmoothCore s)

set_option maxHeartbeats 100000 in
def radiationValue (c : ℝ) (p : Slab N) : RadiationGraphSpace :=
  Real.exp (-c*p.1) • graphLift F χ hUV e O W (chartPoint N p) (u.rootWave (chartPoint N p))

def radialValue (c : ℝ) (p : Slab N) : PhotonFock :=
  (-(Real.exp (-c*p.1) * Real.exp (-p.1))) •
    radialFirst (gaugedValue F χ e O W u.rootWave) (Real.exp (-p.1)) p.2

def gradientValue (c : ℝ) (j : Fin N × Fin 3) (p : Slab N) : PhotonFock :=
  Real.exp (-c*p.1) • sphereGradient
    (radialRestriction (gaugedValue F χ e O W u.rootWave) (Real.exp (-p.1))) j p.2

attribute [local irreducible] radiationValue radialValue gradientValue

theorem value_ae :
    LpRepresents (H := PhotonFock) (slabMeasure N l r) (valueAt (N := N) (c := c) (l := l) (r := r) (S.chart c l r) (gaugedReference (N := N) F χ hUV e O W B u))
      (fun p => Real.exp (-c*p.1) • gaugedValue F χ e O W u.rootWave (chartPoint N p)) := by
  unfold LpRepresents
  have h := (S.quasiMeasurePreserving l r).ae (gaugedReference_value_ae (N := N) F χ hUV e O W B u)
  filter_upwards [(valueAt_ae (N := N) (c := c) (l := l) (r := r) (S.chart c l r) (gaugedReference (N := N) F χ hUV e O W B u)).ae, h] with p hp hx
  exact hp.trans (congrArg (fun z : PhotonFock => Real.exp (-c*p.1) • z) hx)

theorem radiation_ae :
    LpRepresents (H := RadiationGraphSpace) (slabMeasure N l r) (radiationAt (N := N) (c := c) (l := l) (r := r) (S.chart c l r) (gaugedReference (N := N) F χ hUV e O W B u))
      (radiationValue (N := N) F χ hUV e O W u c) := by
  unfold LpRepresents
  have h := (S.quasiMeasurePreserving l r).ae (gaugedReference_graph_ae (N := N) F χ hUV e O W B u)
  filter_upwards [(radiationAt_ae (N := N) (c := c) (l := l) (r := r) (S.chart c l r) (gaugedReference (N := N) F χ hUV e O W B u)).ae, h] with p hp hx
  unfold radiationValue
  exact hp.trans (SlabFormAlgebra.real_smul_congr (Real.exp (-c*p.1)) hx)

include S in
theorem radialOrdinary_ae :
    (fun p : Slab N => radialOrdinary N (gaugedReference (N := N) F χ hUV e O W B u) p) =ᵐ[slabMeasure N l r]
      fun p => radialFirst (gaugedValue F χ e O W u.rootWave) (Real.exp (-p.1)) p.2 := by
  have h : ∀ᵐ p ∂slabMeasure N l r, ∀ j : Fin N × Fin 3,
      PhysicalPFReference.ordinary (Fin N × Fin 3) (fun _ => 0) j
        (gaugedReference (N := N) F χ hUV e O W B u) (chartPoint N p) =
        fderiv ℝ (gaugedValue F χ e O W u.rootWave) (chartPoint N p) (EuclideanSpace.single j 1) :=
    ae_all_iff.mpr fun j => (S.quasiMeasurePreserving l r).ae
      (gaugedReference_ordinary_ae (N := N) F χ hUV e O W B u j)
  filter_upwards [h] with p hp
  unfold radialOrdinary
  simp only [hp]
  exact fderiv_sum_coordinates _ _ _

theorem radial_ae :
    LpRepresents (H := PhotonFock) (slabMeasure N l r)
      (PhysicalSlabForm.radialAt (N := N) (c := c) (a := l) (b := r) (S.chart c l r) (gaugedReference (N := N) F χ hUV e O W B u))
      (radialValue (N := N) F χ e O W u c) := by
  unfold LpRepresents
  filter_upwards [(PhysicalSlabForm.radialAt_ae (N := N) (c := c) (a := l) (b := r) (S.chart c l r) (gaugedReference (N := N) F χ hUV e O W B u)).ae,
    radialOrdinary_ae F χ hUV e O W B S (l := l) (r := r) u] with p hp hd
  apply hp.trans
  unfold PhysicalSlabForm.radialFunction timeFunction valueFunction radialValue
  exact (radial_chart_cancellation _ _ _ _ _).trans
    (SlabFormAlgebra.real_smul_congr _ hd)

theorem gradient_ae (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock) (j : Fin N × Fin 3) :
    LpRepresents (H := PhotonFock) (slabMeasure N l r) (gradientAt (N := N) (c := c) (l := l) (r := r) (S.chart c l r) j (gaugedReference (N := N) F χ hUV e O W B u))
      (gradientValue (N := N) F χ e O W u c j) := by
  unfold LpRepresents
  have hj := (S.quasiMeasurePreserving l r).ae (gaugedReference_ordinary_ae (N := N) F χ hUV e O W B u j)
  filter_upwards [(gradientAt_ae (N := N) (c := c) (l := l) (r := r) (S.chart c l r) j (gaugedReference (N := N) F χ hUV e O W B u)).ae,
    hj, radialOrdinary_ae F χ hUV e O W B S (l := l) (r := r) u] with p hp hx hd
  apply hp.trans
  unfold gradientFunction gradientValue
  exact (SlabFormAlgebra.scaled_sub_congr _ _ hx hd).trans
    (scaled_gradient_coordinates P _ (gauged_core_contDiff F χ hUV e O W B u) _
      (Real.exp_pos _) j p.2)

def angularValue (C : CanonicalSectorCCR photonMeasure) (c : ℝ) (j : Fin N × Fin 3)
    (p : Slab N) : PhotonFock :=
  Real.exp (-c*p.1) • angularCore F χ hUV e O C W u.rootWave (Real.exp (-p.1)) p.2 j

def analysisValue (c : ℝ) (p : Slab N) : CenteredSphereRadiationEnergy.AnalysisSpace :=
  Real.exp (-c*p.1) • RadialGaugeRadiation.displacedAnalysis
    (PhysicalSlabForm.energyLabel F χ hUV e O p)
    (graphLift F χ hUV e O W (chartPoint N p) (u.rootWave (chartPoint N p)))

attribute [local irreducible] angularValue analysisValue

theorem angular_ae (C : CanonicalSectorCCR photonMeasure)
    (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock) (j : Fin N × Fin 3) :
    LpRepresents (H := PhotonFock) (slabMeasure N l r) (PhysicalSlabForm.angularAt (N := N) (c := c) (a := l) (b := r) F χ hUV e O C (S.chart c l r) j
      (gaugedReference (N := N) F χ hUV e O W B u))
      (angularValue (N := N) F χ hUV e O W u C c j) := by
  unfold LpRepresents PhysicalSlabForm.angularAt
  let v := gaugedReference (N := N) F χ hUV e O W B u
  have hf := PhysicalSlabForm.field_ae F χ hUV e O C (a := l) (b := r) j ((S.chart c l r).radiation v)
  have hv := L2QuadraticForms.add_smul_ae Complex.I ((S.chart c l r).gradient j v)
    (PhysicalSlabForm.field F χ hUV e O C l r j ((S.chart c l r).radiation v)) hf
  filter_upwards [hv, (gradient_ae F χ hUV e O W B S (c := c) (l := l) (r := r) u P j).ae,
    (radiation_ae F χ hUV e O W B S (c := c) (l := l) (r := r) u).ae] with p hp hg hq
  unfold gradientValue gradientAt at hg
  unfold radiationValue radiationAt at hq
  apply hp.trans
  unfold angularValue angularCore
  exact SlabFormAlgebra.angular_of_reps (kernelField C (PhysicalSlabForm.coefficient F χ hUV e O j p)).toLinearMap
    (Real.exp (-c*p.1)) hg hq

set_option maxHeartbeats 60000 in
theorem analysis_ae :
    LpRepresents (H := CenteredSphereRadiationEnergy.AnalysisSpace) (slabMeasure N l r) (PhysicalSlabForm.analysisAt (N := N) (c := c) (a := l) (b := r) F χ hUV e O (S.chart c l r)
      (gaugedReference (N := N) F χ hUV e O W B u))
      (analysisValue (N := N) F χ hUV e O W u c) := by
  unfold LpRepresents PhysicalSlabForm.analysisAt
  have hf := CompactSlabOperators.lift_ae l r (PhysicalSlabForm.analysisFamily F χ hUV e O)
    (PhysicalSlabForm.analysisFamily_continuous F χ hUV e O)
    ((S.chart c l r).radiation (gaugedReference (N := N) F χ hUV e O W B u))
  filter_upwards [hf, (radiation_ae F χ hUV e O W B S (c := c) (l := l) (r := r) u).ae] with p hp hq
  unfold radiationValue radiationAt at hq
  apply hp.trans
  unfold analysisValue
  have hl := SlabFormAlgebra.clm_of_smul_rep (PhysicalSlabForm.analysisFamily F χ hUV e O p)
    (Real.exp (-c*p.1)) hq
  have he := PhysicalSlabForm.analysisFamily_apply F χ hUV e O p
    (graphLift F χ hUV e O W (chartPoint N p) (u.rootWave (chartPoint N p)))
  exact hl.trans (SlabFormAlgebra.real_smul_congr (Real.exp (-c*p.1)) he)

end PfHk.PhysicalChartCore
