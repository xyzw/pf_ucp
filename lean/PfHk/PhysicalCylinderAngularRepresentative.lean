import PfHk.PhysicalCylinderWeakTests
import PfHk.PhysicalCylinderContinuity
import PfHk.SphereCorePairContinuity
import PfHk.WeakRadialEquation

/-! The actual angular operator representative recovered from the free
physical weak equation. Its proof uses the proved physical gauge/form
substitution, ordinary dense tests, and radial integration by parts. -/

noncomputable section
namespace PfHk.PhysicalCylinderSource

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.SphereCoreGeometry PfHk.CenteredRadialGauge PfHk.OrdinaryPolarSobolevChart
open PfHk.SphereAngularField (SpherePhoton)
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000
local instance angularRepRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance angularRepPhotonModule : Module ℝ PhotonFock :=
  angularRepRealInner.toNormedSpace.toModule
local instance angularRepPhotonSMul : SMul ℝ PhotonFock := angularRepPhotonModule.toSMul
attribute [local irreducible] curve angularCandidate source radiation gaugedReference fullRadiationInclusion
  fullRootProjection fullRadiationSubmodule PhysicalPFReference.referenceSubspace
  PhysicalPFReference.inclusion

private theorem inner_sub_scaled {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v x y : H) (a : ℝ) : inner ℝ v (x - a • y) = inner ℝ v x - a * inner ℝ v y := by
  rw [inner_sub_right, real_inner_smul_right]

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
theorem angularCandidate_representative
    (hoperator : ∀ v : PhysicalPFReference.Reference (Fin N × Fin 3) (fun _ => 0),
      PhysicalLocalEnergy.form (fun _ => 0) C (CenteredPhysicalReference.profile F χ O)
        (CenteredPhysicalReference.profile_measurable F χ O) (CenteredPhysicalReference.profileBound F χ)
        (CenteredPhysicalReference.profile_bound F χ O) e v a.reference =
          inner ℂ (PhysicalPFReference.inclusion (Fin N × Fin 3) (fun _ => 0) v) f)
    (t : ℝ) :
    IsAngularRepresentative F χ hUV e O C t
      ((curve F χ hUV e O C W B P G a (conformalExponent (Fin N × Fin 3))).value t)
      (angularCandidate F χ hUV e O C W B P G a g (conformalExponent (Fin N × Fin 3)) t) := by
  intro v
  let c := conformalExponent (Fin N × Fin 3)
  let w := curve F χ hUV e O C W B P G a c
  have h := WeakRadialEquation.angular_pairing_eq_of_tests (H := SpherePhoton N) v.ambient c (t-1) (t+1)
    w.ambient w.firstAmbient w.second (source F χ e O W g c)
    (fun s => angularPair F χ hUV e O C s v (w.value s))
    (fun s => radiationPair F χ hUV e O s v (w.value s)) (fun s => Real.exp (-s)^2)
    w.ambient_hasDerivAt w.first_hasDerivAt
    (curve_second_continuous F χ hUV e O C W B P G a c)
    (angularPair_continuous F χ hUV e O C v w)
    (radiationPair_continuous F χ hUV e O v w)
    (source_continuous F χ e O W g c)
    ((Real.continuous_exp.comp continuous_neg).pow 2)
    (fun η hη hs hsupport => weak_separated F χ hUV e O C W B P G S L hN D a g
      hoperator (t-1) (t+1) v η hη hs hsupport)
    (t := t) ⟨by linarith, by linarith⟩
  have hr := radiation_representative F χ hUV e O C W B P G a c t v
  calc
    inner ℝ v.ambient (angularCandidate F χ hUV e O C W B P G a g c t) =
        inner ℝ v.ambient (source F χ e O W g c t + w.second t - c^2 • w.ambient t) -
          Real.exp (-t)^2 * inner ℝ v.ambient (radiation F χ e O W a c t) := by
      unfold angularCandidate
      exact inner_sub_scaled v.ambient
        (source F χ e O W g c t + w.second t - c^2 • w.ambient t)
        (radiation F χ e O W a c t) (Real.exp (-t)^2)
    _ = inner ℝ v.ambient (source F χ e O W g c t + w.second t - c^2 • w.ambient t) -
        Real.exp (-t)^2 * radiationPair F χ hUV e O t v (w.value t) :=
      congrArg (fun x : ℝ => inner ℝ v.ambient
        (source F χ e O W g c t + w.second t - c^2 • w.ambient t) - Real.exp (-t)^2*x) hr
    _ = angularPair F χ hUV e O C t v (w.value t) := h.symm

end PfHk.PhysicalCylinderSource
