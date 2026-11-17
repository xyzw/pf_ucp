import PfHk.PhysicalCylinderContinuity
import PfHk.LogarithmicCompactSupport
import PfHk.CarlemanSpatialDensity

/-! Actual compact logarithmic support of a smooth physical core vector
and its compact source, including the two radial derivatives. -/

noncomputable section
namespace PfHk.PhysicalCylinderSource

open MeasureTheory Set GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.SphereCoreGeometry PfHk.CenteredRadialGauge
open PfHk.SphereAngularField (Sphere SpherePhoton)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
local instance cylinderSupportPhotonReal : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] CoreCurve.ambient CoreCurve.firstAmbient
  curve source radiation angularCandidate CenteredRadialGauge.unitary rawCore rawRadiation
  radiationGraphInclusion fullRootProjection fullRadiationOutput

private theorem lp_zero_of_ae {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] {μ : Measure X} (u : Lp H 2 μ) {v : X → H}
    (hv : u =ᵐ[μ] v) (hz : ∀ x, v x = 0) : u = 0 := by
  apply Lp.ext
  filter_upwards [hv, Lp.coeFn_zero H 2 μ] with x hx hzero
  exact hx.trans ((hz x).trans hzero.symm)

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
  (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
  (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
  {s : Set (Configuration N)} (a : SmoothCore s)
  {f : PhysicalPFReference.WaveSpace (Fin N × Fin 3)} (g : CompactSource s f)

theorem curve_ambient_zero (c t : ℝ)
    (hz : ∀ θ : Sphere N, a.representative (Real.exp (-t) • θ.val) = 0) :
    (curve F χ hUV e O C W B P G a c).ambient t = 0 := by
  have hh : (rawCore F χ hUV e O C W B a P G).ambient t = 0 :=
    lp_zero_of_ae _ (rawCore_value_ae F χ hUV e O C W B a P G t) (fun θ => by
      simp only [gaugedValue, coreValue, SmoothCore.rootWave, hz θ, map_zero])
  unfold curve
  exact ((rawCore F χ hUV e O C W B a P G).conformal_ambient c t).trans
    ((congrArg (fun x : SpherePhoton N => Real.exp (-c*t) • x) hh).trans (smul_zero _))

theorem radiation_zero (c t : ℝ)
    (hz : ∀ θ : Sphere N, a.representative (Real.exp (-t) • θ.val) = 0) :
    radiation F χ e O W a c t = 0 := by
  have hh : rawRadiation F χ e O W a t = 0 :=
    lp_zero_of_ae _ (rawRadiation_ae F χ e O W a t) (fun θ => by
      simp only [rawRadiationValue, logarithmicPoint, hz θ, map_zero, smul_zero])
  unfold radiation
  exact (congrArg (fun x : SpherePhoton N => Real.exp (-c*t) • x) hh).trans (smul_zero _)

theorem source_zero (c t : ℝ)
    (hz : ∀ θ : Sphere N, g.representative (Real.exp (-t) • θ.val) = 0) :
    source F χ e O W g c t = 0 :=
  lp_zero_of_ae _ (source_ae F χ e O W g c t)
    (fun θ => by simp only [hz θ, map_zero, smul_zero])

theorem support_of_interval (c l r : ℝ)
    (hI : ∀ X ∈ tsupport a.representative ∪ tsupport g.representative,
      -Real.log ‖X‖ ∈ Icc l r) :
    ∀ t, t ∉ Icc l r →
      (curve F χ hUV e O C W B P G a c).ambient t = 0 ∧
      (curve F χ hUV e O C W B P G a c).firstAmbient t = 0 ∧
      (curve F χ hUV e O C W B P G a c).second t = 0 ∧
      source F χ e O W g c t = 0 ∧ radiation F χ e O W a c t = 0 ∧
      angularCandidate F χ hUV e O C W B P G a g c t = 0 := by
  have hz (t : ℝ) (ht : t ∉ Icc l r) (θ : Sphere N) :
      Real.exp (-t) • θ.val ∉ tsupport a.representative ∪ tsupport g.representative := by
    intro hx
    have hh := hI _ hx
    rw [CarlemanSpatialDensity.logarithmic_coordinate] at hh
    exact ht hh
  have hu (t : ℝ) (ht : t ∉ Icc l r) :
      (curve F χ hUV e O C W B P G a c).ambient t = 0 :=
    curve_ambient_zero F χ hUV e O C W B P G a c t (fun θ =>
      image_eq_zero_of_notMem_tsupport (fun hx => hz t ht θ (Or.inl hx)))
  have hdu := LogarithmicCompactSupport.derivative_zero_outside
    (curve F χ hUV e O C W B P G a c).ambient_hasDerivAt hu
  have hfirst (t : ℝ) : L2OperatorDerivative.HasL2DerivAt
      (curve F χ hUV e O C W B P G a c).firstAmbient
      ((curve F χ hUV e O C W B P G a c).second t) t := by
    unfold CoreCurve.firstAmbient
    exact (curve F χ hUV e O C W B P G a c).first_hasDerivAt t
  have hddu := LogarithmicCompactSupport.derivative_zero_outside hfirst hdu
  intro t ht
  have hf : source F χ e O W g c t = 0 := source_zero F χ e O W g c t (fun θ =>
    image_eq_zero_of_notMem_tsupport (fun hx => hz t ht θ (Or.inr hx)))
  have hq : radiation F χ e O W a c t = 0 := radiation_zero F χ e O W a c t (fun θ =>
    image_eq_zero_of_notMem_tsupport (fun hx => hz t ht θ (Or.inl hx)))
  refine ⟨hu t ht, hdu t ht, hddu t ht, hf, hq, ?_⟩
  unfold angularCandidate
  simp only [hf, hddu t ht, hu t ht, hq, smul_zero, add_zero, sub_zero]

theorem exists_support_interval (t₀ c : ℝ)
    (hs : ∀ X ∈ s, 0 < ‖X‖ ∧ ‖X‖ < Real.exp (-t₀)) :
    ∃ l r : ℝ, t₀ < l ∧ ∀ t, t ∉ Icc l r →
      (curve F χ hUV e O C W B P G a c).ambient t = 0 ∧
      (curve F χ hUV e O C W B P G a c).firstAmbient t = 0 ∧
      (curve F χ hUV e O C W B P G a c).second t = 0 ∧
      source F χ e O W g c t = 0 ∧ radiation F χ e O W a c t = 0 ∧
      angularCandidate F χ hUV e O C W B P G a g c t = 0 := by
  have hsub : tsupport a.representative ∪ tsupport g.representative ⊆ s :=
    union_subset a.support g.support
  let hex := LogarithmicCompactSupport.exists_interval
    (a.compact.union g.compact) t₀ (fun X hX => (hs X (hsub hX)).1)
    (fun X hX => (hs X (hsub hX)).2)
  let l := Classical.choose hex
  let r := Classical.choose (Classical.choose_spec hex)
  have hspec := Classical.choose_spec (Classical.choose_spec hex)
  exact ⟨l, r, hspec.1, support_of_interval F χ hUV e O C W B P G a g c l r hspec.2⟩

end PfHk.PhysicalCylinderSource
