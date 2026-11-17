import PfHk.PhysicalSlabWeakForm
import PfHk.PhysicalSlabSeparatedForm
import PfHk.PhysicalSlabSeparatedSource

/-! The actual physical free operator equation tested against arbitrary
separated compact cylinder tests. -/

noncomputable section
namespace PfHk.PhysicalCylinderSource

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.SphereCoreGeometry PfHk.CenteredRadialGauge PfHk.OrdinaryPolarSobolevChart
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000
local instance weakTestsRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance weakTestsPhotonModule : Module ℝ PhotonFock :=
  weakTestsRealInner.toNormedSpace.toModule
local instance weakTestsPhotonSMul : SMul ℝ PhotonFock := weakTestsPhotonModule.toSMul
attribute [local irreducible] curve angularCandidate gaugedReference fullRadiationInclusion
  fullRootProjection fullRadiationSubmodule PhysicalPFReference.referenceSubspace
  PhysicalPFReference.inclusion

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
  (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
  (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
  (S : StandardPolarSobolevCharts N)
  (L : StandardLogPolarCalculus (Fin N × Fin 3)) (hN : 0 < Fintype.card (Fin N × Fin 3))
  (D : WeylCoreReference.StandardWeylFormCoreDensity W B)
  {s : Set (Configuration N)} (a : SmoothCore s)
  {f : PhysicalPFReference.WaveSpace (Fin N × Fin 3)} (g : CompactSource s f)

include S L hN D in
theorem weak_separated
    (hoperator : ∀ v : PhysicalPFReference.Reference (Fin N × Fin 3) (fun _ => 0),
      PhysicalLocalEnergy.form (fun _ => 0) C (CenteredPhysicalReference.profile F χ O)
        (CenteredPhysicalReference.profile_measurable F χ O) (CenteredPhysicalReference.profileBound F χ)
        (CenteredPhysicalReference.profile_bound F χ O) e v a.reference =
          inner ℂ (PhysicalPFReference.inclusion (Fin N × Fin 3) (fun _ => 0) v) f)
    (l r : ℝ) (v : CoreVector N) (η : ℝ → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hs : HasCompactSupport η) (hsupport : tsupport η ⊆ Set.Ioo l r) :
    let c := conformalExponent (Fin N × Fin 3)
    let w := curve F χ hUV e O C W B P G a c
    (∫ t in Set.Icc l r, (deriv η t+c*η t) * inner ℝ v.ambient (w.firstAmbient t+c • w.ambient t) +
      η t * angularPair F χ hUV e O C t v (w.value t) +
      (Real.exp (-t)^2*η t) * radiationPair F χ hUV e O t v (w.value t)) =
      ∫ t in Set.Icc l r, η t * inner ℝ v.ambient (source F χ e O W g c t) := by
  let c := conformalExponent (Fin N × Fin 3)
  let hex := (S.chart c l r).lift_core v η hη hs hsupport
  let u := Classical.choose hex
  have hspec := Classical.choose_spec hex
  have hu := hspec.1
  have hv := hspec.2.1
  have ht := hspec.2.2.1
  have hg := hspec.2.2.2.1
  have hq := hspec.2.2.2.2
  have he := PhysicalSlabCoreForm.weak_form F χ hUV e O C W B P S L hN D a g
    hoperator l r u hu
  exact (PhysicalSlabCoreForm.form_test_eq F χ hUV e O C W B P G S a
    (c := c) (l := l) (r := r) u v η hv ht hg hq).symm.trans
    (he.trans (PhysicalSlabCoreForm.source_test_eq F χ e O W g (S.chart c l r) u v η hv))

end PfHk.PhysicalCylinderSource
