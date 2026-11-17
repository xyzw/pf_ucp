import PfHk.CenteredPhysicalReference
import PfHk.CenteredRadialGaugePolarInner
import PfHk.CenteredRadialGaugeCoreRegularity
import PfHk.SphereRestrictionCalculus
import PfHk.CarlemanPolarMeasure

/-! Actual weak-form polar substitution on the original physical smooth
core. The proof combines the proved bilinear gauge calculation with
ordinary change of measure. Only first angular derivatives occur. -/

noncomputable section
namespace PfHk.CenteredPhysicalReference

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability GptLean.PhysicalWeyl PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.CenteredRadialGauge
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
local instance polarFormPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance polarFormAnalysisRealInner : InnerProductSpace ℝ (lp (fun _ : ℕ => PhotonFock) 2) :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] coreValue gaugedValue coreCovariant angularCore
  graphLift RadialGaugeRadiation.displacedAnalysis radiationGraphDerivative

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure)

def cylinderBilinearDensity (q p : Configuration N → RadiationGraphSpace)
    (t : ℝ) (θ : UnitSphere (Fin N × Fin 3)) : ℝ :=
  Real.exp (-conformalExponent (Fin N × Fin 3)*t)^2 *
    (Real.exp (-t)^2 * inner ℝ (radialFirst (gaugedValue F χ e O W q) (Real.exp (-t)) θ)
        (radialFirst (gaugedValue F χ e O W p) (Real.exp (-t)) θ) +
      (∑ j, inner ℝ (angularCore F χ hUV e O C W q (Real.exp (-t)) θ j)
        (angularCore F χ hUV e O C W p (Real.exp (-t)) θ j)) +
      Real.exp (-t)^2 * (2 * inner ℝ
        (RadialGaugeRadiation.displacedAnalysis (inverseSqrtLabel F χ hUV e O (Real.exp (-t) • θ.val))
          (graphLift F χ hUV e O W (Real.exp (-t) • θ.val) (q (Real.exp (-t) • θ.val))))
        (RadialGaugeRadiation.displacedAnalysis (inverseSqrtLabel F χ hUV e O (Real.exp (-t) • θ.val))
          (graphLift F χ hUV e O W (Real.exp (-t) • θ.val) (p (Real.exp (-t) • θ.val))))))

theorem physicalFormDensity_integrable (q p : Configuration N → RadiationGraphSpace)
    (hq : MemLp q 2 volume) (hp : MemLp p 2 volume)
    (hfq : ContDiff ℝ (1 : ℕ∞) (C1ReferenceCore.valueFunction q))
    (hfp : ContDiff ℝ (1 : ℕ∞) (C1ReferenceCore.valueFunction p))
    (hsq : HasCompactSupport (C1ReferenceCore.valueFunction q))
    (hsp : HasCompactSupport (C1ReferenceCore.valueFunction p)) :
    Integrable (physicalFormDensity F χ O C e q p) := by
  have h := C1ReferenceCore.formDensity_integrable C (profile F χ O)
    (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e q p hq hp hfq hfp hsq hsp
  convert! h using 1
  funext X
  simp only [C1ReferenceCore.formDensity, physicalFormDensity, covariantFunction_eq]

theorem density_logarithmic
    (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (B : StandardWeylGraphC1 W) {s u : Set (Configuration N)} (a : SmoothCore s) (b : SmoothCore u)
    (t : ℝ) (θ : UnitSphere (Fin N × Fin 3)) :
    logarithmicJacobian (Fin N × Fin 3) t * (2 * physicalFormDensity F χ O C e a.rootWave b.rootWave
      (Real.exp (-t) • θ.val)) = cylinderBilinearDensity F χ hUV e O C W a.rootWave b.rootWave t θ := by
  have ha := gauged_core_contDiff F χ hUV e O W B a
  have hb := gauged_core_contDiff F χ hUV e O W B b
  have hua : ContDiff ℝ (1 : ℕ∞) (coreValue a.rootWave) := by
    unfold coreValue
    convert! a.value_smooth using 1
  have hub : ContDiff ℝ (1 : ℕ∞) (coreValue b.rootWave) := by
    unfold coreValue
    convert! b.value_smooth using 1
  have hfa : FiniteNumberSupport photonMeasure a.photonCutoff (coreValue a.rootWave (Real.exp (-t) • θ.val)) := by
    convert! a.photonFinite (Real.exp (-t) • θ.val) using 1
    unfold coreValue SmoothCore.rootWave fullRadiationInclusion
    rfl
  have hfb : FiniteNumberSupport photonMeasure b.photonCutoff (coreValue b.rootWave (Real.exp (-t) • θ.val)) := by
    convert! b.photonFinite (Real.exp (-t) • θ.val) using 1
    unfold coreValue SmoothCore.rootWave fullRadiationInclusion
    rfl
  have hk := physical_polar_kinetic_inner F χ hUV e O P C W a.rootWave b.rootWave ha hb
    (Real.exp_pos (-t)) θ (radialRestriction_sphereC1 _ ha _)
    (radialRestriction_sphereC1 _ hb _)
    ((hua.differentiable one_ne_zero).differentiableAt)
    ((hub.differentiable one_ne_zero).differentiableAt)
    a.photonCutoff b.photonCutoff hfa hfb
  have hr := radiationPair_graphLift F χ hUV e O W (Real.exp (-t) • θ.val)
    (a.rootWave (Real.exp (-t) • θ.val)) (b.rootWave (Real.exp (-t) • θ.val))
  unfold cylinderBilinearDensity physicalFormDensity
  rw [hr, ← hk, logarithmicJacobian_eq_conformal]
  ring

theorem form_eq_cylinder_integral
    (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (L : StandardLogPolarCalculus (Fin N × Fin 3)) (hN : 0 < Fintype.card (Fin N × Fin 3))
    (B : StandardWeylGraphC1 W) {s u : Set (Configuration N)} (a : SmoothCore s) (b : SmoothCore u) :
    2 * (PhysicalLocalEnergy.form (fun _ => 0) C (profile F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e a.reference b.reference).re =
      ∫ t : ℝ, ∫ θ : UnitSphere (Fin N × Fin 3),
        cylinderBilinearDensity F χ hUV e O C W a.rootWave b.rootWave t θ
        ∂sphereMeasure (Fin N × Fin 3) := by
  have hf := form_eq_integral F χ O C e a.rootWave b.rootWave a.rootWave_memLp b.rootWave_memLp
    a.value_smooth b.value_smooth a.value_compact b.value_compact
  have hi := physicalFormDensity_integrable F χ e O C a.rootWave b.rootWave
    a.rootWave_memLp b.rootWave_memLp a.value_smooth b.value_smooth a.value_compact b.value_compact
  have hp := integral_logPolar (Fin N × Fin 3) L hN
    (fun X => 2 * physicalFormDensity F χ O C e a.rootWave b.rootWave X) (hi.const_mul 2)
  have he : (∫ X, 2 * physicalFormDensity F χ O C e a.rootWave b.rootWave X) =
      2 * (PhysicalLocalEnergy.form (fun _ => 0) C (profile F χ O) (profile_measurable F χ O)
        (profileBound F χ) (profile_bound F χ O) e a.reference b.reference).re := by
    rw [integral_const_mul, ← hf]
    rfl
  apply he.symm.trans
  apply hp.trans
  apply integral_congr_ae
  exact ae_of_all _ fun t => integral_congr_ae (ae_of_all _ fun θ =>
    density_logarithmic F χ hUV e O C W P B a b t θ)

end PfHk.CenteredPhysicalReference
