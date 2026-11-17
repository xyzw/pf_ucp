import PfHk.WeakGaugePotentials

/-! Actual quotient spaces for density-current data and unshifted external
potentials. Potentials are also identified under additive scalar constants. -/

noncomputable section

namespace PfHk.GaugeClasses

open MeasureTheory GptLean.PhysicalPairSpace GptLean.PhysicalPairDuality
open GptLean.TransformationsGauge

set_option Elab.async false
set_option maxHeartbeats 600000

/-- Two density-current pairs belong to the same weak gauge orbit. -/
def DataRelated (d₁ d₂ : Pair) : Prop :=
  ∃ G : WeakSpatialGauge, G.shiftPair d₁ = d₂

theorem dataRelated_refl (d : Pair) : DataRelated d d :=
  ⟨WeakSpatialGauge.zero, WeakSpatialGauge.zero_shiftPair d⟩

theorem dataRelated_symm {d₁ d₂ : Pair} (h : DataRelated d₁ d₂) :
    DataRelated d₂ d₁ := by
  obtain ⟨G, hG⟩ := h
  exact ⟨G.neg, hG ▸ G.neg_shiftPair d₁⟩

theorem dataRelated_trans {d₁ d₂ d₃ : Pair} (h₁ : DataRelated d₁ d₂)
    (h₂ : DataRelated d₂ d₃) : DataRelated d₁ d₃ := by
  obtain ⟨G, hG⟩ := h₁
  obtain ⟨H, hH⟩ := h₂
  exact ⟨G.add H, (G.add_shiftPair H d₁).trans (by rw [hG, hH])⟩

def dataSetoid : Setoid Pair where
  r := DataRelated
  iseqv := ⟨dataRelated_refl, dataRelated_symm, dataRelated_trans⟩

def DataClass := Quotient dataSetoid

def dataClass (d : Pair) : DataClass := Quotient.mk dataSetoid d

theorem dataClass_eq_iff (d₁ d₂ : Pair) :
    dataClass d₁ = dataClass d₂ ↔ ∃ G : WeakSpatialGauge, G.shiftPair d₁ = d₂ :=
  Quotient.eq

theorem densityL1_eq_of_dataRelated {d₁ d₂ : Pair} (h : DataRelated d₁ d₂) :
    densityL1 d₁ = densityL1 d₂ := by
  obtain ⟨G, hG⟩ := h
  rw [← hG, G.densityL1_shiftPair]

theorem densityL1_eq_of_dataClass_eq {d₁ d₂ : Pair}
    (h : dataClass d₁ = dataClass d₂) : densityL1 d₁ = densityL1 d₂ :=
  densityL1_eq_of_dataRelated ((dataClass_eq_iff d₁ d₂).mp h)

/-- The scalar density is a well-defined function of the data gauge class. -/
def classDensity : DataClass → Lp ℝ 1 (volume : Measure Position) :=
  Quotient.lift densityL1 (fun _ _ h => densityL1_eq_of_dataRelated h)

@[simp] theorem classDensity_dataClass (d : Pair) :
    classDensity (dataClass d) = densityL1 d := rfl

/-- This product uses the unshifted scalar potential v, not v plus |A|²/2. -/
abbrev UnshiftedPotentials := ScalarPotential × VectorPotential

/-- The physical potentials differ by a weak gauge and a scalar constant. -/
def PotentialRelated (u₁ u₂ : UnshiftedPotentials) : Prop :=
  ∃ (G : WeakSpatialGauge) (c : ℝ),
    (u₂.2.val : Position → Vector) =ᵐ[volume]
      (fun x => u₁.2.val x - G.gradientVector x) ∧
    (u₁.1.val : Position → ℝ) =ᵐ[volume] (fun x => u₂.1.val x + c)

theorem potentialRelated_refl (u : UnshiftedPotentials) : PotentialRelated u u := by
  refine ⟨WeakSpatialGauge.zero, 0, ?_, ?_⟩
  · exact ae_of_all _ fun x => by
      simp only [WeakSpatialGauge.zero_gradientVector, sub_zero]
  · exact ae_of_all _ fun x => by simp only [add_zero]

theorem potentialRelated_symm {u₁ u₂ : UnshiftedPotentials}
    (h : PotentialRelated u₁ u₂) : PotentialRelated u₂ u₁ := by
  obtain ⟨G, c, hA, hv⟩ := h
  refine ⟨G.neg, -c, ?_, ?_⟩
  · filter_upwards [hA] with x hx
    rw [hx, G.neg_gradientVector]
    abel
  · filter_upwards [hv] with x hx
    rw [hx]
    ring

theorem potentialRelated_trans {u₁ u₂ u₃ : UnshiftedPotentials}
    (h₁ : PotentialRelated u₁ u₂) (h₂ : PotentialRelated u₂ u₃) :
    PotentialRelated u₁ u₃ := by
  obtain ⟨G, c, hA, hv⟩ := h₁
  obtain ⟨H, d, hB, hw⟩ := h₂
  refine ⟨G.add H, c + d, ?_, ?_⟩
  · filter_upwards [hA, hB] with x hx hy
    rw [hy, hx, G.add_gradientVector H]
    abel
  · filter_upwards [hv, hw] with x hx hy
    rw [hx, hy]
    ring

def potentialSetoid : Setoid UnshiftedPotentials where
  r := PotentialRelated
  iseqv := ⟨potentialRelated_refl, potentialRelated_symm, potentialRelated_trans⟩

def PotentialClass := Quotient potentialSetoid

def potentialClass (u : UnshiftedPotentials) : PotentialClass :=
  Quotient.mk potentialSetoid u

theorem potentialClass_eq_iff (u₁ u₂ : UnshiftedPotentials) :
    potentialClass u₁ = potentialClass u₂ ↔ PotentialRelated u₁ u₂ := Quotient.eq

end PfHk.GaugeClasses
