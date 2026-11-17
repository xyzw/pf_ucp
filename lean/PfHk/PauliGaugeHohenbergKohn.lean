import PfHk.PauliHohenbergKohn
import PfHk.PauliWeakGaugeEnergy
import PfHk.PauliWeakGaugeData
import PfHk.GaugeClasses

/-! The physical spinful Hohenberg--Kohn theorem on the actual gauge
quotients. The locally regular pair is preserved while the other state is
transported to align the density-current data. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliHohenbergKohn

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPairSpace GptLean.PhysicalPolarization
  GptLean.TransformationsGauge PfHk.PauliGroundState PfHk.PauliPhysicalLocalRegularity
  PfHk.PauliWeakGauge

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [local irreducible] referenceSubspace inclusion PauliReference.wave
  PauliGroundState.energy PauliGroundState.data PauliWeakGauge.gaugeState densityL1

variable {N : ℕ} (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (F : Frame) (χ : ArticleCutoff) (hN : 0 < N)
  (U : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e)
  (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
  (p₁ p₂ : State N)
  (h₁ : IsGroundState C e F χ A₁ v₁ c hc p₁)
  (h₂ : IsGroundState C e F χ A₂ v₂ c hc p₂)
  (he : e ≠ 0) (hχ : ¬ (χ.value =ᵐ[volume] 0))
  (hcutoff : (∀ᵐ k ∂volume, χ.value k ≠ 0) ∨
    ∃ α : ℝ, 0 < α ∧ Integrable (fun x => Real.exp (α * ‖x‖) *
      densityL1 (data C e F χ p₁.vector) x) volume)

include hN U h₁ h₂ he hχ hcutoff

theorem hohenberg_kohn_gauge_on_open
    (G : WeakSpatialGauge) (hd : G.shiftPair (data C e F χ p₁.vector) = data C e F χ p₂.vector)
    {Ω : Set PhysicalSourceCoordinates.Position} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hfull : ∀ᵐ x ∂volume, x ∈ Ω)
    (hreg : Nonempty (RegularityOn A₁ v₁ Ω) ∨ Nonempty (RegularityOn A₂ v₂ Ω)) :
    (A₂.val : Position → Vector) =ᵐ[volume] (fun x => A₁.val x - G.gradientVector x) ∧
      ∀ᵐ x ∂volume, v₁.val x = v₂.val x +
        (energy C e F χ A₁ v₁ c hc p₁.vector - energy C e F χ A₂ v₂ c hc p₂.vector) / N := by
  rcases hreg with hleft | hright
  · let q₂ := gaugeState G.neg p₂
    have hg₂ := groundState_gauge C e F χ A₂ v₂ c hc G.neg p₂ h₂
    have hd' : data C e F χ p₁.vector = data C e F χ q₂.vector :=
      ((data_gaugeState C e F χ G.neg p₂).trans
        ((congrArg G.neg.shiftPair hd.symm).trans (G.neg_shiftPair _))).symm
    have h := hohenberg_kohn_on_open C e F χ hN U A₁ (G.neg.gaugeVector A₂)
      v₁ v₂ c hc p₁ q₂ h₁ hg₂ hd' he hχ hcutoff hΩ hconn hfull (Or.inl hleft)
    have hE₂ := energy_gaugeState C e F χ A₂ v₂ c hc G.neg p₂
    refine ⟨?_, ?_⟩
    · filter_upwards [h.1, G.neg.coeFn_gaugeVector A₂] with x hx hg
      rw [G.neg_gradientVector, sub_neg_eq_add] at hg
      exact (eq_sub_iff_add_eq).mpr (hx.trans hg).symm
    · filter_upwards [h.2] with x hx
      exact hx.trans (congrArg (fun E : ℝ => v₂.val x +
        (energy C e F χ A₁ v₁ c hc p₁.vector - E) / N) hE₂)
  · let q₁ := gaugeState G p₁
    have hg₁ := groundState_gauge C e F χ A₁ v₁ c hc G p₁ h₁
    have hd' : data C e F χ q₁.vector = data C e F χ p₂.vector :=
      (data_gaugeState C e F χ G p₁).trans hd
    have hρ : densityL1 (data C e F χ q₁.vector) = densityL1 (data C e F χ p₁.vector) :=
      (congrArg densityL1 (data_gaugeState C e F χ G p₁)).trans
        (G.densityL1_shiftPair (data C e F χ p₁.vector))
    have hcutoff' : (∀ᵐ k ∂volume, χ.value k ≠ 0) ∨
        ∃ α : ℝ, 0 < α ∧ Integrable (fun x => Real.exp (α * ‖x‖) *
          densityL1 (data C e F χ q₁.vector) x) volume := by
      simpa only [hρ] using hcutoff
    have h := hohenberg_kohn_on_open C e F χ hN U (G.gaugeVector A₁) A₂
      v₁ v₂ c hc q₁ p₂ hg₁ h₂ hd' he hχ hcutoff' hΩ hconn hfull (Or.inr hright)
    have hE₁ := energy_gaugeState C e F χ A₁ v₁ c hc G p₁
    refine ⟨?_, ?_⟩
    · filter_upwards [G.coeFn_gaugeVector A₁, h.1] with x hx hy
      exact hy.symm.trans hx
    · filter_upwards [h.2] with x hx
      exact hx.trans (congrArg (fun E : ℝ => v₂.val x +
        (E - energy C e F χ A₂ v₂ c hc p₂.vector) / N) hE₁)

theorem hohenberg_kohn_gauge
    (G : WeakSpatialGauge) (hd : G.shiftPair (data C e F χ p₁.vector) = data C e F χ p₂.vector)
    (hreg : Nonempty (RegularityOn A₁ v₁ Set.univ) ∨ Nonempty (RegularityOn A₂ v₂ Set.univ)) :
    (A₂.val : Position → Vector) =ᵐ[volume] (fun x => A₁.val x - G.gradientVector x) ∧
      ∀ᵐ x ∂volume, v₁.val x = v₂.val x +
        (energy C e F χ A₁ v₁ c hc p₁.vector - energy C e F χ A₂ v₂ c hc p₂.vector) / N :=
  hohenberg_kohn_gauge_on_open C e F χ hN U A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂ he hχ hcutoff G hd
    isOpen_univ isPreconnected_univ (ae_of_all _ fun _ => Set.mem_univ _) hreg

theorem hohenberg_kohn_gauge_classes_on_open
    (hd : GaugeClasses.dataClass (data C e F χ p₁.vector) =
      GaugeClasses.dataClass (data C e F χ p₂.vector))
    {Ω : Set PhysicalSourceCoordinates.Position} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hfull : ∀ᵐ x ∂volume, x ∈ Ω)
    (hreg : Nonempty (RegularityOn A₁ v₁ Ω) ∨ Nonempty (RegularityOn A₂ v₂ Ω)) :
    GaugeClasses.potentialClass (v₁, A₁) = GaugeClasses.potentialClass (v₂, A₂) := by
  obtain ⟨G, hG⟩ := (GaugeClasses.dataClass_eq_iff _ _).mp hd
  have h := hohenberg_kohn_gauge_on_open C e F χ hN U A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂
    he hχ hcutoff G hG hΩ hconn hfull hreg
  apply (GaugeClasses.potentialClass_eq_iff _ _).mpr
  exact ⟨G, (energy C e F χ A₁ v₁ c hc p₁.vector -
    energy C e F χ A₂ v₂ c hc p₂.vector) / N, h.1, h.2⟩

theorem hohenberg_kohn_gauge_classes
    (hd : GaugeClasses.dataClass (data C e F χ p₁.vector) =
      GaugeClasses.dataClass (data C e F χ p₂.vector))
    (hreg : Nonempty (RegularityOn A₁ v₁ Set.univ) ∨ Nonempty (RegularityOn A₂ v₂ Set.univ)) :
    GaugeClasses.potentialClass (v₁, A₁) = GaugeClasses.potentialClass (v₂, A₂) :=
  hohenberg_kohn_gauge_classes_on_open C e F χ hN U A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂
    he hχ hcutoff hd isOpen_univ isPreconnected_univ (ae_of_all _ fun _ => Set.mem_univ _) hreg

end PfHk.PauliHohenbergKohn

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
