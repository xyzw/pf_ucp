import PfHk.PhysicalCylinderSupport
import PfHk.PhysicalCylinderIntegration

/-! The uniform cylinder estimate on the actual compact physical core.
All integration conditions are proved here. The angular representative
is the exact weak polar operator identity supplied by the separate
physical transport theorem. -/

noncomputable section
namespace PfHk.PhysicalCylinderSource

open MeasureTheory Set GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.SphereCoreGeometry PfHk.CenteredRadialGauge PfHk.CarlemanWeights
  PfHk.CylinderConjugation PfHk.PhysicalWeightedCylinder
open PfHk.SphereAngularField (SpherePhoton)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
local instance cylinderCoreEstimatePhotonReal : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] curve source radiation angularCandidate
  CoreCurve.ambient CoreCurve.firstAmbient originalDensity

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (C : CanonicalSectorCCR photonMeasure) (W : ConcreteWeylLaw photonMeasure)
  (B : StandardWeylGraphC1 W)
  (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
  (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)

theorem exists_uniform_source_estimate (α : ℝ) (hα : 0 < α) :
    ∃ t₀ : ℝ, 2 ≤ t₀ ∧ ∀ (τ c : ℝ), 9 ≤ τ → |c| ≤ τ →
      ∀ (O : Configuration N) {s : Set (Configuration N)} (a : SmoothCore s)
        {f : PhysicalPFReference.WaveSpace (Fin N × Fin 3)} (g : CompactSource s f),
      (∀ X ∈ s, 0 < ‖X‖ ∧ ‖X‖ < Real.exp (-t₀)) →
      (∀ t, IsAngularRepresentative F χ hUV e O C t
        ((curve F χ hUV e O C W B P G a c).value t)
        (angularCandidate F χ hUV e O C W B P G a g c t)) →
      (∫ t in Ioi t₀, Real.exp (2*τ*weight α t) *
        originalDensity τ c (beta α) (fun s => Real.exp (-2*s))
          (curve F χ hUV e O C W B P G a c).ambient
          (curve F χ hUV e O C W B P G a c).firstAmbient
          (angularCandidate F χ hUV e O C W B P G a g c)
          (radiation F χ e O W a c) t) ≤
      16 * ∫ t in Ioi t₀, Real.exp (2*τ*weight α t) * ‖source F χ e O W g c t‖^2 := by
  have hex := PhysicalWeightedCylinder.exists_uniform_estimate (N := N) F χ hUV e C W α hα
  let t₀ := Classical.choose hex
  have ht₀ : 2 ≤ t₀ := (Classical.choose_spec hex).1
  refine ⟨t₀, ht₀, ?_⟩
  intro τ c hτ hc O s a f g hs hK
  let hexSupport := exists_support_interval F χ hUV e O C W B P G a g t₀ c hs
  let l := Classical.choose hexSupport
  let r := Classical.choose (Classical.choose_spec hexSupport)
  have hl : t₀ < l := (Classical.choose_spec (Classical.choose_spec hexSupport)).1
  have hsupport := (Classical.choose_spec (Classical.choose_spec hexSupport)).2
  let u := curve F χ hUV e O C W B P G a c
  let k := angularCandidate F χ hUV e O C W B P G a g c
  let q := radiation F χ e O W a c
  have hq (t : ℝ) : IsRadiationRepresentative F χ hUV e O t (u.value t) (q t) :=
    radiation_representative F χ hUV e O C W B P G a c t
  have hi := integration_of_compact F χ hUV e O C τ c α t₀ l r ht₀ hl u k q
    (curve_second_continuous F χ hUV e O C W B P G a c)
    (angularCandidate_continuous F χ hUV e O C W B P G a g c)
    (radiation_continuous F χ e O W a c)
    (fun t ht => ⟨(hsupport t ht).1, (hsupport t ht).2.2.2.2.2,
      (hsupport t ht).2.2.2.2.1⟩)
  have hI := compact_density_integrable F χ hUV e C τ c α t₀ l r ht₀ hl O u k q hK hq
    (fun t ht => ⟨(hsupport t ht).1, (hsupport t ht).2.1⟩)
  have h := (Classical.choose_spec hex).2 τ c hτ hc O u k q hK hq hi hI
  have he (t : ℝ) : -u.second t + k t + c^2 • u.ambient t + Real.exp (-2*t) • q t =
      source F χ e O W g c t := by
    have hr : Real.exp (-2*t) = Real.exp (-t)^2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [hr] using operator_eq_source F χ hUV e O C W B P G a g c t
  exact h.trans_eq (congrArg (fun x : ℝ => 16*x)
    (integral_congr_ae (ae_of_all _ fun t =>
      congrArg (fun v : SpherePhoton N => Real.exp (2*τ*weight α t) * ‖v‖^2) (he t))))

end PfHk.PhysicalCylinderSource
