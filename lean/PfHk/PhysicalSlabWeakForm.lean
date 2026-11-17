import PfHk.PhysicalSlabCoreForm
import PfHk.PhysicalSlabSourcePair
import PfHk.PhysicalFreeOperator

/-! Extension of the proved physical weak polar identity from actual
gauged smooth-core tests to every compactly supported Sobolev test.
The extension uses the actual reference graph norm and the constructed
bounded slab form. -/

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
local instance slabWeakPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance slabWeakPhotonModule : Module ℝ PhotonFock := slabWeakPhotonRealInner.toNormedSpace.toModule
local instance slabWeakPhotonSMul : SMul ℝ PhotonFock := slabWeakPhotonModule.toSMul
attribute [local irreducible] gaugedReference fullRadiationInclusion fullRootProjection
  fullRadiationSubmodule PhysicalPFReference.referenceSubspace PhysicalPFReference.inclusion

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
  (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
  (S : StandardPolarSobolevCharts N)
  (L : StandardLogPolarCalculus (Fin N × Fin 3)) (hN : 0 < Fintype.card (Fin N × Fin 3))
  (D : WeylCoreReference.StandardWeylFormCoreDensity W B)
  {s : Set (Configuration N)} (b : SmoothCore s)
  {f : PhysicalPFReference.WaveSpace (Fin N × Fin 3)} (g : CompactSource s f)

include P L hN D in
theorem weak_form (hoperator : ∀ v : PhysicalPFReference.Reference (Fin N × Fin 3) (fun _ => 0),
      PhysicalLocalEnergy.form (fun _ => 0) C (CenteredPhysicalReference.profile F χ O)
        (CenteredPhysicalReference.profile_measurable F χ O) (CenteredPhysicalReference.profileBound F χ)
        (CenteredPhysicalReference.profile_bound F χ O) e v b.reference =
          inner ℂ (PhysicalPFReference.inclusion (Fin N × Fin 3) (fun _ => 0) v) f)
    (l r : ℝ) (v : PhysicalPFReference.Reference (Fin N × Fin 3) (fun _ => 0))
    (hv : compactlySupported N l r v) :
    PhysicalSlabForm.form F χ hUV e O C (S.chart (conformalExponent (Fin N × Fin 3)) l r)
      v (gaugedReference F χ hUV e O W B b) =
      inner ℝ ((S.chart (conformalExponent (Fin N × Fin 3)) l r).value v)
        (PhysicalCylinderSource.slabSource F χ e O W g (conformalExponent (Fin N × Fin 3)) l r) := by
  have hv' : WeylCoreReference.CompactlySupportedIn (annulus N l r) v := by
    simpa only [compactlySupported, WeylCoreReference.CompactlySupportedIn] using hv
  have happ : ∃ a : ℕ → SmoothCore (annulus N l r),
      Filter.Tendsto (fun n => gaugedReference F χ hUV e O W B (a n)) Filter.atTop (nhds v) :=
    form_core_approximation (N := N) F χ hUV e O W B D (annulus N l r)
      (isOpen_annulus l r) v hv'
  obtain ⟨a, ha⟩ := happ
  apply SlabFormAlgebra.eq_of_sequence
    (PhysicalSlabForm.form_continuous_left F χ hUV e O C (S.chart (conformalExponent (Fin N × Fin 3)) l r)
      (gaugedReference F χ hUV e O W B b))
    (SlabFormAlgebra.continuous_pair_clm (S.chart (conformalExponent (Fin N × Fin 3)) l r).value _) ha
  intro n
  exact (form_eq_original F χ hUV e O C W B P S l r b L hN (a n)).trans
    ((congrArg (fun z : ℂ => 2 * z.re) (hoperator (a n).reference)).trans
      (source_pair_eq_original F χ hUV e O W B S L hN l r (a n) g).symm)

end PfHk.PhysicalSlabCoreForm
