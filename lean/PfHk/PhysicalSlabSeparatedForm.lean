import PfHk.PhysicalCylinderPairRepresentatives
import PfHk.SeparatedSlabIntegration

/-! Evaluation of the physical slab form on a separated ordinary sphere
test, in terms of the actual conformal core curve and its sphere forms. -/

noncomputable section
namespace PfHk.PhysicalSlabCoreForm

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.SphereCoreGeometry PfHk.CenteredRadialGauge PfHk.OrdinaryPolarSobolevChart
open PfHk.SphereAngularField (Sphere SpherePhoton)
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

private theorem native_photon_smul (a : ℝ) (q : PhotonFock) :
    a • q = (a : ℂ) • q :=
  RCLike.real_smul_eq_coe_smul (K := ℂ) a q

private theorem chart_photon_smul (a : ℝ) (q : PhotonFock) :
    @SMul.smul ℝ PhotonFock PhysicalChartCore.chartCorePhotonSMul a q = (a : ℂ) • q := rfl

private theorem native_to_chart_smul (a : ℝ) (q : PhotonFock) :
    a • q = @SMul.smul ℝ PhotonFock PhysicalChartCore.chartCorePhotonSMul a q :=
  (native_photon_smul a q).trans (chart_photon_smul a q).symm

private theorem native_to_chart_ae {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {q : X → PhotonFock} (a : ℝ) (f : X → PhotonFock)
    (h : q =ᵐ[μ] fun x => a • f x) :
    q =ᵐ[μ] fun x => @SMul.smul ℝ PhotonFock PhysicalChartCore.chartCorePhotonSMul a (f x) :=
  h.trans (ae_of_all _ fun x => native_to_chart_smul a (f x))

private theorem native_neg_to_chart_ae {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {q : X → PhotonFock} (a : ℝ) (f : X → PhotonFock)
    (h : q =ᵐ[μ] fun x => -(a • f x)) :
    q =ᵐ[μ] fun x => @SMul.smul ℝ PhotonFock PhysicalChartCore.chartCorePhotonSMul (-a) (f x) :=
  h.trans (ae_of_all _ fun x =>
    (neg_smul a (f x)).symm.trans (native_to_chart_smul (-a) (f x)))

local instance separatedFormRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance separatedFormAnalysisRealInner : InnerProductSpace ℝ CenteredSphereRadiationEnergy.AnalysisSpace :=
  InnerProductSpace.rclikeToReal ℂ _
local instance separatedFormPhotonModule : Module ℝ PhotonFock := separatedFormRealInner.toNormedSpace.toModule
local instance separatedFormPhotonSMul : SMul ℝ PhotonFock := separatedFormPhotonModule.toSMul
local instance separatedFormRadiationModule : Module ℝ RadiationGraphSpace :=
  (NormedSpace.restrictScalars ℝ ℂ RadiationGraphSpace).toModule
local instance separatedFormRadiationSMul : SMul ℝ RadiationGraphSpace := separatedFormRadiationModule.toSMul
local instance separatedFormAnalysisModule : Module ℝ CenteredSphereRadiationEnergy.AnalysisSpace :=
  separatedFormAnalysisRealInner.toNormedSpace.toModule
local instance separatedFormAnalysisSMul : SMul ℝ CenteredSphereRadiationEnergy.AnalysisSpace := separatedFormAnalysisModule.toSMul
attribute [local irreducible] PhysicalCylinderSource.curve rawCore
  CoreCurve.conformal CoreVector.scale kernelField RadialGaugeRadiation.displacedAnalysis
  PhysicalChartCore.analysisValue PhysicalChartCore.angularValue graphLift
  gaugedReference PhysicalPFReference.referenceSubspace CoreCurve.ambient CoreCurve.firstAmbient
  radialFirst gaugedValue SmoothCore.rootWave
  CenteredSphereRadiationEnergy.analysis CenteredSphereAngularField.angularVector
  PhysicalCylinderSource.angular CoreVector.ambient
  PhysicalSlabTestEvaluation.angularFiber PhysicalSlabTestEvaluation.analysisFiber
  PhysicalChartCore.radialValue

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
  (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
  (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
  (S : StandardPolarSobolevCharts N)
  {s : Set (Configuration N)} (b : SmoothCore s) {c l r : ℝ}
  (u : PhysicalPFReference.Reference (Fin N × Fin 3) (fun _ => 0))
  (v : CoreVector N) (η : ℝ → ℝ)

private theorem radial_chart_ae (t : ℝ) :
    (PhysicalCylinderSource.curve F χ hUV e O C W B P G b c).firstAmbient t +
      c • (PhysicalCylinderSource.curve F χ hUV e O C W B P G b c).ambient t =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => PhysicalChartCore.radialValue F χ e O W b c (t, θ) := by
  unfold PhysicalChartCore.radialValue
  exact native_neg_to_chart_ae (μ := sphereMeasure (Fin N × Fin 3))
    (Real.exp (-c*t)*Real.exp (-t))
    (fun θ => radialFirst (gaugedValue F χ e O W b.rootWave) (Real.exp (-t)) θ)
    (PhysicalCylinderSource.radial_ae (N := N) F χ hUV e O C W B P G b c t)

private theorem angular_chart_ae (j : Fin N × Fin 3) (t : ℝ) :
    PhysicalCylinderSource.angular F χ hUV e O C W B P G b c t j =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => PhysicalChartCore.angularValue F χ hUV e O W b C c j (t, θ) := by
  unfold PhysicalChartCore.angularValue
  exact native_to_chart_ae (μ := sphereMeasure (Fin N × Fin 3)) (Real.exp (-c*t))
    (fun θ => angularCore F χ hUV e O C W b.rootWave (Real.exp (-t)) θ j)
    (PhysicalCylinderSource.curveAngular_ae (N := N) F χ hUV e O C W B P G b c t j)

set_option maxHeartbeats 200000 in
theorem form_test_eq
    (hv : LpRepresents (slabMeasure N l r) (valueAt (S.chart c l r) u) (fun p => η p.1 • v.ambient p.2))
    (ht : LpRepresents (slabMeasure N l r) (timeAt (S.chart c l r) u) (fun p => deriv η p.1 • v.ambient p.2))
    (hg : ∀ j, LpRepresents (slabMeasure N l r) (gradientAt (S.chart c l r) j u)
      (fun p => η p.1 • v.gradient j p.2))
    (hq : LpRepresents (slabMeasure N l r) (radiationAt (S.chart c l r) u)
      (fun p => η p.1 • v.radiation p.2)) :
    PhysicalSlabForm.form F χ hUV e O C (S.chart c l r) u
      (gaugedReference F χ hUV e O W B b) =
      ∫ t in Set.Icc l r,
        (deriv η t+c*η t) * inner ℝ v.ambient
          ((PhysicalCylinderSource.curve F χ hUV e O C W B P G b c).firstAmbient t +
            c • (PhysicalCylinderSource.curve F χ hUV e O C W B P G b c).ambient t) +
        η t * angularPair F χ hUV e O C t v
          ((PhysicalCylinderSource.curve F χ hUV e O C W B P G b c).value t) +
        (Real.exp (-t)^2*η t) * radiationPair F χ hUV e O t v
          ((PhysicalCylinderSource.curve F χ hUV e O C W B P G b c).value t) := by
  let V := gaugedReference F χ hUV e O W B b
  let w := PhysicalCylinderSource.curve F χ hUV e O C W B P G b c
  have hleftR := (PhysicalSlabTestEvaluation.radial_ae (S.chart c l r) u v η hv ht).ae
  have hleftA (j : Fin N × Fin 3) :=
    (PhysicalSlabTestEvaluation.angular_ae F χ hUV e O C (S.chart c l r) u v η j (hg j) hq).ae
  have hleftQ := (PhysicalSlabTestEvaluation.analysis_ae F χ hUV e O (S.chart c l r) u v η hq).ae
  have hrightR := (PhysicalChartCore.radial_ae F χ hUV e O W B S (c := c) (l := l) (r := r) b).ae
  have hrightA (j : Fin N × Fin 3) :=
    (PhysicalChartCore.angular_ae F χ hUV e O W B S (c := c) (l := l) (r := r) b C P j).ae
  have hrightQ := (PhysicalChartCore.analysis_ae F χ hUV e O W B S (c := c) (l := l) (r := r) b).ae
  have hweighted := PhysicalSlabForm.radiusWeight_real_ae
    (PhysicalSlabForm.analysisMap F χ hUV e O (S.chart c l r) V) hrightQ
  have hi := SlabBilinearIntegration.form_integrable
    (H := PhotonFock) (K := CenteredSphereRadiationEnergy.AnalysisSpace) (J := Fin N × Fin 3)
    (PhysicalSlabForm.radialMap (N := N) (S.chart c l r) u)
    (PhysicalSlabForm.radialMap (N := N) (S.chart c l r) V)
    (PhysicalSlabForm.angularMap F χ hUV e O C (S.chart c l r) · u)
    (PhysicalSlabForm.angularMap F χ hUV e O C (S.chart c l r) · V)
    (PhysicalSlabForm.analysisMap F χ hUV e O (S.chart c l r) u)
    (PhysicalSlabForm.radiusWeight l r (PhysicalSlabForm.analysisMap F χ hUV e O (S.chart c l r) V))
    hleftR hrightR hleftA hrightA hleftQ hweighted
  have he := SlabBilinearIntegration.form_eq_integral
    (H := PhotonFock) (K := CenteredSphereRadiationEnergy.AnalysisSpace) (J := Fin N × Fin 3)
    (PhysicalSlabForm.radialMap (N := N) (S.chart c l r) u)
    (PhysicalSlabForm.radialMap (N := N) (S.chart c l r) V)
    (PhysicalSlabForm.angularMap F χ hUV e O C (S.chart c l r) · u)
    (PhysicalSlabForm.angularMap F χ hUV e O C (S.chart c l r) · V)
    (PhysicalSlabForm.analysisMap F χ hUV e O (S.chart c l r) u)
    (PhysicalSlabForm.radiusWeight l r (PhysicalSlabForm.analysisMap F χ hUV e O (S.chart c l r) V))
    hleftR hrightR hleftA hrightA hleftQ hweighted
  have hRad := radial_chart_ae F χ hUV e O C W B P G b (c := c)
  have hAng := angular_chart_ae F χ hUV e O C W B P G b (c := c)
  have hSepData0 := SeparatedSlabIntegration.form_integral
    (X := Sphere N)
    (H := PhotonFock) (K := CenteredSphereRadiationEnergy.AnalysisSpace) (J := Fin N × Fin 3)
    (μ := (volume : Measure ℝ).restrict (Set.Icc l r)) (ν := sphereMeasure (Fin N × Fin 3))
    c η (deriv η) (fun t => Real.exp (-t)^2)
    (vf := fun θ => v.ambient θ)
    (Rf := fun t θ => PhysicalChartCore.radialValue F χ e O W b c (t, θ))
    (Af := fun j t θ => PhysicalSlabTestEvaluation.angularFiber F χ hUV e O C v j (t, θ))
    (Bf := fun j t θ => PhysicalChartCore.angularValue F χ hUV e O W b C c j (t, θ))
    (qf := fun t θ => PhysicalSlabTestEvaluation.analysisFiber F χ hUV e O v (t, θ))
    (pf := fun t θ => PhysicalChartCore.analysisValue F χ hUV e O W b c (t, θ))
  have hSepData1 := hSepData0 v.ambient (fun t => w.firstAmbient t + c • w.ambient t)
  have hSepData2 := hSepData1
    (fun j t => CenteredSphereAngularField.angularVector F χ hUV e O C v.gradient v.radiation j t)
    (fun j t => PhysicalCylinderSource.angular F χ hUV e O C W B P G b c t j)
  have hSep0 := hSepData2
    (fun t => CenteredSphereRadiationEnergy.analysis F χ hUV e O t v.radiation)
    (fun t => CenteredSphereRadiationEnergy.analysis F χ hUV e O t (w.value t).radiation)
  have hSep1 := hSep0 Filter.EventuallyEq.rfl hRad
  have hSep2 := hSep1 (fun j t => test_angular_ae F χ hUV e O C v j t) hAng
  have hSep3 := hSep2 (test_analysis_ae F χ hUV e O v)
    (curve_analysis_ae F χ hUV e O C W B P G b c)
  have hSep := hSep3 hi
  apply he.trans
  apply hSep.trans
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    have hr := CenteredSphereRadiationEnergy.analysis_pair_eq_integral F χ hUV e O t
      v.radiation (w.value t).radiation
    simpa only [PhysicalCylinderSource.angular, angularPair, radiationPair, w] using
      congrArg (fun x : ℝ => (deriv η t+c*η t) * inner ℝ v.ambient
      (w.firstAmbient t+c • w.ambient t) + η t * angularPair F χ hUV e O C t v (w.value t) +
      (Real.exp (-t)^2*η t)*x) hr

end PfHk.PhysicalSlabCoreForm
