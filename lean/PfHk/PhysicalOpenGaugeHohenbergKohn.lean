import PfHk.PhysicalWeakGaugeStates
import PfHk.GaugeClasses
import PfHk.PhysicalOpenHohenbergKohn

/-! Hohenberg--Kohn uniqueness for the full weak spatial gauge class.
The pair with additional UCP regularity is left unchanged. The other state
and vector potential are gauged to align the actual density-current pairs.
The result uses actual quotients and retains the exact scalar constant. -/

noncomputable section
namespace PfHk.PhysicalHohenbergKohn

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalGroundState GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms GptLean.Representability
  GptLean.TransformationsGauge PfHk.PhysicalDiamagneticPotential
  PfHk.PhysicalOpenUCPCoefficients PfHk.PhysicalWeakGauge

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000

attribute [local irreducible] inclusion PhysicalPFReference.referenceSubspace
  PhysicalLocalEnergy.IsExternalWeakEigenstate PhysicalGroundStateWeak.stateReference
  PfHk.PhysicalWeakGauge.gaugeState

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (e : ℝ) (i : Fin N)
  {Ω : Set GptLean.PhysicalSourceCoordinates.Position}
  (hΩ : IsOpen Ω) (hconnected : IsConnected Ω)
  (hfull : ∀ᵐ x ∂volume, x ∈ Ω)

include hΩ hconnected hfull

/-- For every admissible weak gauge relating the actual data, the vector
potentials differ by its negative gradient and the scalar difference is
exactly the ground-state energy difference divided by particle number. -/
theorem hohenberg_kohn_gauge_on_open
    (U : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e)
    (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential)
    (p₁ p₂ : State F χ C B S e (N := N))
    (h₁ : IsGroundState i F χ C B S e (shifted v₁ A₁) p₁)
    (h₂ : IsGroundState i F χ C B S e (shifted v₂ A₂) p₂)
    (G : WeakSpatialGauge)
    (hd : G.shiftPair ((model i F χ C B S e).density p₁) =
      (model i F χ C B S e).density p₂)
    (he : e ≠ 0) (hχ : ¬ (χ.value =ᵐ[volume] 0))
    (hcutoff : (∀ᵐ k ∂volume, χ.value k ≠ 0) ∨
      ∃ α : ℝ, 0 < α ∧ Integrable (fun x => Real.exp (α * ‖x‖) *
        PhysicalPairSpace.densityL1 ((model i F χ C B S e).density p₁) x) volume)
    (hreg : Nonempty (RegularityOn A₁ v₁ Ω) ∨ Nonempty (RegularityOn A₂ v₂ Ω)) :
    (A₂.val : PhysicalPairSpace.Position → PhysicalPairSpace.Vector) =ᵐ[volume]
        (fun x => A₁.val x - G.gradientVector x) ∧
      ∀ᵐ x ∂volume, v₁.val x = v₂.val x +
        (shiftedEnergy i F χ C B S e (shifted v₁ A₁) p₁ -
          shiftedEnergy i F χ C B S e (shifted v₂ A₂) p₂) / N := by
  rcases hreg with hleft | hright
  · let q₂ := gaugeState F χ C B S e G.neg p₂
    have hg₂ := groundState_gauge F χ C B S e i G.neg v₂ A₂ p₂ h₂
    have hd' : (model i F χ C B S e).density p₁ =
        (model i F χ C B S e).density q₂ := by
      change (model i F χ C B S e).density p₁ =
        (model i F χ C B S e).density (gaugeState F χ C B S e G.neg p₂)
      rw [density_gaugeState, ← hd, G.neg_shiftPair]
    have h := hohenberg_kohn_on_open F χ C B S e i hΩ hconnected hfull U
      A₁ (G.neg.gaugeVector A₂) v₁ v₂ p₁ q₂ h₁ hg₂ hd' he hχ hcutoff (Or.inl hleft)
    have hE₂ := energy_gaugeState F χ C B S e i G.neg v₂ A₂ p₂
    refine ⟨?_, ?_⟩
    · filter_upwards [h.1, G.neg.coeFn_gaugeVector A₂] with x hx hg
      rw [G.neg_gradientVector, sub_neg_eq_add] at hg
      exact (eq_sub_iff_add_eq).mpr (hx.trans hg).symm
    · filter_upwards [h.2] with x hx
      exact hx.trans (congrArg (fun z : ℝ => v₂.val x +
        (shiftedEnergy i F χ C B S e (shifted v₁ A₁) p₁ - z) / N) hE₂)
  · let q₁ := gaugeState F χ C B S e G p₁
    have hg₁ := groundState_gauge F χ C B S e i G v₁ A₁ p₁ h₁
    have hd' : (model i F χ C B S e).density q₁ =
        (model i F χ C B S e).density p₂ :=
      (density_gaugeState F χ C B S e i G p₁).trans hd
    have hρ : PhysicalPairSpace.densityL1 ((model i F χ C B S e).density q₁) =
        PhysicalPairSpace.densityL1 ((model i F χ C B S e).density p₁) :=
      (congrArg PhysicalPairSpace.densityL1
        (density_gaugeState F χ C B S e i G p₁)).trans
          (G.densityL1_shiftPair ((model i F χ C B S e).density p₁))
    have hcutoff' : (∀ᵐ k ∂volume, χ.value k ≠ 0) ∨
        ∃ α : ℝ, 0 < α ∧ Integrable (fun x => Real.exp (α * ‖x‖) *
          PhysicalPairSpace.densityL1 ((model i F χ C B S e).density q₁) x) volume := by
      simpa only [hρ] using hcutoff
    have h := hohenberg_kohn_on_open F χ C B S e i hΩ hconnected hfull U
      (G.gaugeVector A₁) A₂ v₁ v₂ q₁ p₂ hg₁ h₂ hd' he hχ hcutoff' (Or.inr hright)
    have hE₁ := energy_gaugeState F χ C B S e i G v₁ A₁ p₁
    refine ⟨?_, ?_⟩
    · filter_upwards [G.coeFn_gaugeVector A₁, h.1] with x hx hy
      exact hy.symm.trans hx
    · filter_upwards [h.2] with x hx
      exact hx.trans (congrArg (fun z : ℝ => v₂.val x +
        (z - shiftedEnergy i F χ C B S e (shifted v₂ A₂) p₂) / N) hE₁)

/-- The exceptional-set version of Theorem 3.3 on actual gauge quotients. Additive
scalar constants are included in the potential equivalence relation. -/
theorem hohenberg_kohn_gauge_classes_on_open
    (U : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e)
    (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential)
    (p₁ p₂ : State F χ C B S e (N := N))
    (h₁ : IsGroundState i F χ C B S e (shifted v₁ A₁) p₁)
    (h₂ : IsGroundState i F χ C B S e (shifted v₂ A₂) p₂)
    (hd : GaugeClasses.dataClass ((model i F χ C B S e).density p₁) =
      GaugeClasses.dataClass ((model i F χ C B S e).density p₂))
    (he : e ≠ 0) (hχ : ¬ (χ.value =ᵐ[volume] 0))
    (hcutoff : (∀ᵐ k ∂volume, χ.value k ≠ 0) ∨
      ∃ α : ℝ, 0 < α ∧ Integrable (fun x => Real.exp (α * ‖x‖) *
        PhysicalPairSpace.densityL1 ((model i F χ C B S e).density p₁) x) volume)
    (hreg : Nonempty (RegularityOn A₁ v₁ Ω) ∨ Nonempty (RegularityOn A₂ v₂ Ω)) :
    GaugeClasses.potentialClass (v₁, A₁) = GaugeClasses.potentialClass (v₂, A₂) := by
  obtain ⟨G, hG⟩ := (GaugeClasses.dataClass_eq_iff _ _).mp hd
  have h := hohenberg_kohn_gauge_on_open F χ C B S e i hΩ hconnected hfull U
    A₁ A₂ v₁ v₂ p₁ p₂ h₁ h₂ G hG he hχ hcutoff hreg
  apply (GaugeClasses.potentialClass_eq_iff _ _).mpr
  exact ⟨G, (shiftedEnergy i F χ C B S e (shifted v₁ A₁) p₁ -
    shiftedEnergy i F χ C B S e (shifted v₂ A₂) p₂) / N, h.1, h.2⟩

end PfHk.PhysicalHohenbergKohn
