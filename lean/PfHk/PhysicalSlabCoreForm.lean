import PfHk.PhysicalChartCore
import PfHk.SlabBilinearIntegration
import PfHk.AnnularPolarMeasure
import PfHk.CenteredPhysicalCoreSupport

/-! The bounded cylinder-slab form equals the original physical weak
form on the actual Weyl image of the smooth core. -/

noncomputable section
namespace PfHk.PhysicalSlabCoreForm

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain
  PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.CenteredRadialGauge
  PfHk.OrdinaryPolarSobolevChart
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000
local instance slabCorePhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance slabCoreAnalysisRealInner : InnerProductSpace ℝ CenteredSphereRadiationEnergy.AnalysisSpace :=
  InnerProductSpace.rclikeToReal ℂ _
local instance slabCorePhotonModule : Module ℝ PhotonFock := slabCorePhotonRealInner.toNormedSpace.toModule
local instance slabCorePhotonSMul : SMul ℝ PhotonFock := slabCorePhotonModule.toSMul
local instance slabCoreRadiationModule : Module ℝ RadiationGraphSpace :=
  (NormedSpace.restrictScalars ℝ ℂ RadiationGraphSpace).toModule
local instance slabCoreRadiationSMul : SMul ℝ RadiationGraphSpace := slabCoreRadiationModule.toSMul
local instance slabCoreAnalysisModule : Module ℝ CenteredSphereRadiationEnergy.AnalysisSpace :=
  slabCoreAnalysisRealInner.toNormedSpace.toModule
local instance slabCoreAnalysisSMul : SMul ℝ CenteredSphereRadiationEnergy.AnalysisSpace := slabCoreAnalysisModule.toSMul
attribute [local irreducible] gaugedValue coreValue graphLift angularCore
  PhysicalPFReference.referenceSubspace

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
  (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
  (S : StandardPolarSobolevCharts N) (l r : ℝ)
  {s u : Set (Configuration N)} (a : SmoothCore s) (b : SmoothCore u)

include P in
theorem form_eq_cylinder_integral :
    PhysicalSlabForm.form F χ hUV e O C (S.chart (conformalExponent (Fin N × Fin 3)) l r)
      (gaugedReference F χ hUV e O W B a) (gaugedReference F χ hUV e O W B b) =
      ∫ p : Slab N, CenteredPhysicalReference.cylinderBilinearDensity
        F χ hUV e O C W a.rootWave b.rootWave p.1 p.2 ∂slabMeasure N l r := by
  let c := conformalExponent (Fin N × Fin 3)
  let U := gaugedReference F χ hUV e O W B a
  let V := gaugedReference F χ hUV e O W B b
  have hw := PhysicalSlabForm.radiusWeight_real_ae
    (PhysicalSlabForm.analysisMap F χ hUV e O (S.chart c l r) V)
    (PhysicalChartCore.analysis_ae F χ hUV e O W B S (c := c) (l := l) (r := r) b).ae
  have he := SlabBilinearIntegration.form_eq_integral
    (PhysicalSlabForm.radialMap (N := N) (S.chart c l r) U)
    (PhysicalSlabForm.radialMap (N := N) (S.chart c l r) V)
    (PhysicalSlabForm.angularMap F χ hUV e O C (S.chart c l r) · U)
    (PhysicalSlabForm.angularMap F χ hUV e O C (S.chart c l r) · V)
    (PhysicalSlabForm.analysisMap F χ hUV e O (S.chart c l r) U)
    (PhysicalSlabForm.radiusWeight l r (PhysicalSlabForm.analysisMap F χ hUV e O (S.chart c l r) V))
    (PhysicalChartCore.radial_ae F χ hUV e O W B S a).ae
    (PhysicalChartCore.radial_ae F χ hUV e O W B S b).ae
    (fun j => (PhysicalChartCore.angular_ae F χ hUV e O W B S a C P j).ae)
    (fun j => (PhysicalChartCore.angular_ae F χ hUV e O W B S b C P j).ae)
    (PhysicalChartCore.analysis_ae F χ hUV e O W B S a).ae hw
  apply he.trans
  apply integral_congr_ae
  exact ae_of_all _ fun p => by
    unfold CenteredPhysicalReference.cylinderBilinearDensity
      PhysicalChartCore.angularValue PhysicalChartCore.analysisValue PhysicalChartCore.radialValue
    exact SlabBilinearIntegration.conformal_density (Real.exp (-c*p.1)) (Real.exp (-p.1)) _ _ _ _ _ _

include P in
theorem form_eq_original
    (L : StandardLogPolarCalculus (Fin N × Fin 3)) (hN : 0 < Fintype.card (Fin N × Fin 3))
    (a : SmoothCore (annulus N l r)) :
    PhysicalSlabForm.form F χ hUV e O C (S.chart (conformalExponent (Fin N × Fin 3)) l r)
      (gaugedReference F χ hUV e O W B a) (gaugedReference F χ hUV e O W B b) =
      2 * (PhysicalLocalEnergy.form (fun _ => 0) C (CenteredPhysicalReference.profile F χ O)
        (CenteredPhysicalReference.profile_measurable F χ O) (CenteredPhysicalReference.profileBound F χ)
        (CenteredPhysicalReference.profile_bound F χ O) e a.reference b.reference).re := by
  have hi := CenteredPhysicalReference.physicalFormDensity_integrable F χ e O C a.rootWave b.rootWave
    a.rootWave_memLp b.rootWave_memLp a.value_smooth b.value_smooth a.value_compact b.value_compact
  have hp := integral_annular_slab L hN l r
    (fun X => 2 * CenteredPhysicalReference.physicalFormDensity F χ O C e a.rootWave b.rootWave X)
    (hi.const_mul 2) (fun X hX => by
      rw [CenteredPhysicalReference.physicalFormDensity_zero_left a F χ e O C b.rootWave hX, mul_zero])
  have he := CenteredPhysicalReference.form_eq_integral F χ O C e a.rootWave b.rootWave
    a.rootWave_memLp b.rootWave_memLp a.value_smooth b.value_smooth a.value_compact b.value_compact
  calc
    _ = ∫ p : Slab N, CenteredPhysicalReference.cylinderBilinearDensity
        F χ hUV e O C W a.rootWave b.rootWave p.1 p.2 ∂slabMeasure N l r :=
      form_eq_cylinder_integral F χ hUV e O C W B P S l r a b
    _ = ∫ p : Slab N, logarithmicJacobian (Fin N × Fin 3) p.1 *
        (2 * CenteredPhysicalReference.physicalFormDensity F χ O C e a.rootWave b.rootWave
          (chartPoint N p)) ∂slabMeasure N l r :=
      integral_congr_ae (ae_of_all _ fun p =>
        (CenteredPhysicalReference.density_logarithmic F χ hUV e O C W P B a b p.1 p.2).symm)
    _ = ∫ X, 2 * CenteredPhysicalReference.physicalFormDensity F χ O C e a.rootWave b.rootWave X := hp.symm
    _ = _ := by rw [integral_const_mul, ← he]; rfl

end PfHk.PhysicalSlabCoreForm
