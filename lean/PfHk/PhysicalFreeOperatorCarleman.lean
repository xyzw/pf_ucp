import PfHk.PhysicalFreeCoreCarleman
import PfHk.PhysicalAnnularGraphTransfer

/-! Uniform free Pauli–Fierz Carleman estimate on the full operator
domain, for the actual family of centered field profiles. -/

noncomputable section
namespace PfHk.PhysicalFreeCarleman

open MeasureTheory Set GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.SphereCoreGeometry PfHk.CenteredPhysicalReference PfHk.OrdinaryPolarSobolevChart
  PfHk.PhysicalAnnularGraphTransfer PfHk.PhysicalCarlemanInput
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
local instance freeOperatorCarlemanRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] FreeGraph SmoothCore.reference PhysicalPFReference.inclusion
  PhysicalPFReference.referenceSubspace operatorDensity

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
theorem exists_uniform_centered_profile_estimate (α : ℝ) (hα : 0 < α) :
    ∃ r₀ τ₀ : ℝ, 0 < r₀ ∧ r₀ < Real.exp (-2) ∧ 1 ≤ τ₀ ∧
      ∀ τ : ℝ, τ₀ ≤ τ → ∀ (O : Configuration N) (R : ℝ), 0 < R → R ≤ r₀ →
      ∀ (u : PhysicalPFReference.Reference (Fin N × Fin 3) (fun _ => 0))
        (f : PhysicalPFReference.WaveSpace (Fin N × Fin 3)),
      FreeGraph C (profile F χ O) (profile_measurable F χ O)
        (profileBound F χ) (profile_bound F χ O) e u f →
      AnnularSupport (PhysicalPFReference.inclusion (Fin N × Fin 3) (fun _ => 0) u) 0 R →
      (∫ X in Metric.ball 0 R, operatorDensity F χ O C e τ α u X) ≤
        64*∫ X in Metric.ball 0 R, CarlemanSpatialDensity.source τ α (fun Y => ‖f Y‖^2) X := by
  have hex := exists_uniform_core_estimate F χ hUV e C W B P G S L hN D α hα
  let t₀ := Classical.choose hex
  have ht₀ : 2 ≤ t₀ := (Classical.choose_spec hex).1
  let r₀ := Real.exp (-(t₀+1))
  let τ₀ := max 9 |conformalExponent (Fin N × Fin 3)|
  have hr₀ : 0 < r₀ := Real.exp_pos _
  have hsmall : r₀ < Real.exp (-2) := Real.exp_lt_exp.mpr (by linarith)
  have hone : r₀ < 1 := by
    have h : -(t₀+1) < 0 := by linarith
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr h
  have hless : r₀ < Real.exp (-t₀) := Real.exp_lt_exp.mpr (by linarith)
  have hτ₀ : 1 ≤ τ₀ := (by norm_num : (1 : ℝ) ≤ 9).trans (le_max_left _ _)
  refine ⟨r₀, τ₀, hr₀, hsmall, hτ₀, ?_⟩
  intro τ hτ O R hRpos hR u f hu hsupp
  apply annular_estimate F χ O C e (A O)
    (show 0 ≤ τ by have h9 : (9 : ℝ) ≤ τ := (le_max_left _ _).trans hτ; linarith)
    hα hone hR ?_ hu hsupp
  intro s hs ρ R' hρ hR' hsA a g hg hgraph
  have hgeo (X : Configuration N) (hX : X ∈ s) : 0 < ‖X‖ ∧ ‖X‖ < Real.exp (-t₀) := by
    have hn := CarlemanSpatialDensity.annulus_norm (hsA hX)
    exact ⟨hρ.trans_le hn.1, (hn.2.trans_lt hR').trans hless⟩
  have hcore := (Classical.choose_spec hex).2 τ hτ O hρ (hR'.trans hone) hsA hgeo a hg hgraph
  exact (integral_congr_ae (core_density_ae F χ O C e a τ α)).trans_le hcore

end PfHk.PhysicalFreeCarleman
