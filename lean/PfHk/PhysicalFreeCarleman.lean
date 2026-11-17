import PfHk.PhysicalFreeOperatorCarleman
import PfHk.PhysicalFreeCenterTransport

/-! Uniform physical free Pauli–Fierz Carleman estimate on the full
operator domain, at every electronic center. The retained inputs are
the explicit standard geometric and operator-theory facts. -/

noncomputable section
namespace PfHk.PhysicalFreeCarleman

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability GptLean.PhysicalPFReference
  GptLean.TransformationsTranslation PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.SphereCoreGeometry PfHk.CenteredPhysicalReference PfHk.OrdinaryPolarSobolevChart
  PfHk.PhysicalCarlemanInput PfHk.PhysicalElectronicShift PfHk.CarlemanSpatialDensity

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
local instance finalFreeCarlemanRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] FreeGraph PhysicalPFReference.inclusion
  PhysicalPFReference.referenceSubspace shiftReference centeredOperatorDensity

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (C : CanonicalSectorCCR photonMeasure) (W : ConcreteWeylLaw photonMeasure)
  (B : StandardWeylGraphC1 W)
  (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
  (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
  (S : StandardPolarSobolevCharts N)
  (L : StandardLogPolarCalculus (Fin N × Fin 3)) (hN : 0 < Fintype.card (Fin N × Fin 3))
  (D : WeylCoreReference.StandardWeylFormCoreDensity W B)
  (A : ∀ O : Configuration N, AnnularCoreApproximation C (profile F χ O)
    (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e)

include hUV W B P G S L hN D A in
/-- A single pair of radius and parameter thresholds works for every
electronic center and every smaller ball in the original free operator. -/
theorem exists_uniform_estimate (α : ℝ) (hα : 0 < α) :
    ∃ r₀ τ₀ : ℝ, 0 < r₀ ∧ r₀ < Real.exp (-2) ∧ 1 ≤ τ₀ ∧
      ∀ τ : ℝ, τ₀ ≤ τ → ∀ (O : Configuration N) (R : ℝ), 0 < R → R ≤ r₀ →
      ∀ (u : Reference (Fin N × Fin 3) (fun _ => 0))
        (f : WaveSpace (Fin N × Fin 3)),
      FreeGraph C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e u f →
      AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R →
      (∫ X in Metric.ball O R, centeredOperatorDensity F χ C e O τ α u X) ≤
        64*∫ X in Metric.ball O R, centeredSource O τ α (fun Y => ‖f Y‖ ^ 2) X := by
  have hex := exists_uniform_centered_profile_estimate
    F χ hUV e C W B P G S L hN D A α hα
  let r₀ := Classical.choose hex
  let τ₀ := Classical.choose (Classical.choose_spec hex)
  have h := Classical.choose_spec (Classical.choose_spec hex)
  refine ⟨r₀, τ₀, h.1, h.2.1, h.2.2.1, ?_⟩
  intro τ hτ O R hRpos hR u f hu hsupp
  have hest := h.2.2.2 τ hτ O R hRpos hR (shiftReference O u) (shiftL2 O f)
    (freeGraph_centered F χ O C e hu) (centered_annularSupport O hsupp)
  exact (shifted_operatorDensity_integral F χ C e O R τ α u).symm.trans_le
    (hest.trans_eq (congrArg (fun z : ℝ => 64*z) (shifted_source_integral O R τ α f)))

end PfHk.PhysicalFreeCarleman
