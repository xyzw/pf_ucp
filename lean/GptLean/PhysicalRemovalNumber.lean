import GptLean.PhysicalGaussianRealTests
import GptLean.PhysicalFockHardNumber

/-!
The prepared Gaussian hard marginal has exactly the original hard photon
number. This identity holds as an extended nonnegative real value and
does not assume finite total photon number.
-/

noncomputable section
namespace GptLean.PhysicalRemovalMarginal

open MeasureTheory PhysicalFock PhysicalNormalTrace PhysicalPhotonMarginal
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable (B : StandardNormalTraceBackground) {X : Type} [MeasurableSpace X]
  (ν : Measure X) [IsSeparable ν]
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure) (κ : ℝ)

/-- The positive-cutoff hard number is bounded by the original radiation energy. -/
theorem hardNumber_le_radiation (hκ : 0 < κ) {x : B.Trace PhotonFock}
    (hx : x ∈ (B.realization PhotonFock).rank.positive) :
    (NormalPhoton.hardNumberForm B.normal (B.realization PhotonFock).functional κ).expectation x ≤
      ENNReal.ofReal (1 / κ) *
        (NormalPhoton.radiationForm B.normal (B.realization PhotonFock).functional).expectation x := by
  have hset : MeasurableSet {p | κ ≤ NormalPhoton.frequency p} :=
    measurableSet_le measurable_const NormalPhoton.frequency_measurable
  have hmeas : Measurable (fun p => ENNReal.ofReal (NormalPhoton.frequency p) *
      NormalPhoton.density B.normal x hx p) :=
    NormalPhoton.frequency_measurable.ennreal_ofReal.mul
      (NormalPhoton.density_measurable B.normal x hx)
  rw [NormalPhoton.density_hardNumber B.normal (B.realization PhotonFock).functional κ x hx,
    NormalPhoton.density_radiation B.normal (B.realization PhotonFock).functional x hx,
    ← lintegral_const_mul _ hmeas, ← lintegral_indicator hset]
  refine lintegral_mono fun p => ?_
  by_cases hp : κ ≤ NormalPhoton.frequency p
  · rw [Set.indicator_of_mem (s := {p : PhotonMode | κ ≤ NormalPhoton.frequency p})
      (a := p) hp, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / κ)]
    have hratio : 1 ≤ 1 / κ * NormalPhoton.frequency p := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hκ]
      simpa using hp
    calc NormalPhoton.density B.normal x hx p =
        1 * NormalPhoton.density B.normal x hx p := (one_mul _).symm
      _ ≤ _ := mul_le_mul' (ENNReal.one_le_ofReal.mpr hratio) le_rfl
  · rw [Set.indicator_of_notMem (s := {p : PhotonMode | κ ≤ NormalPhoton.frequency p})
      (a := p) hp]
    exact bot_le

attribute [local irreducible] RemovalState.PositiveForm.expectation

include C in
theorem numberFromCoordinates_gaussianHardTarget {x : B.Trace (Lp PhotonFock 2 ν)}
    (hx : x ∈ (B.realization (Lp PhotonFock 2 ν)).rank.positive) :
    numberFromCoordinates B (gaussianHardTarget B ν BF κ x) =
      (NormalPhoton.hardNumberForm B.normal (B.realization PhotonFock).functional κ).expectation
        (marginal B ν x) := by
  have hcoordinates :=
    numberFromCoordinates_apply B (hardTargetTrace_positive BF κ B ν hx)
  exact hcoordinates.trans
    (hardSplit_number_expectation B.normal (B.realization PhotonFock).functional BF C κ
      (marginal B ν x) (marginal_positive B ν hx))

include C in
theorem number_eq_of_gaussianHardTarget
    {x y : B.Trace (Lp PhotonFock 2 ν)}
    (hx : x ∈ (B.realization (Lp PhotonFock 2 ν)).rank.positive)
    (hy : y ∈ (B.realization (Lp PhotonFock 2 ν)).rank.positive)
    (h : fullMarginal B ν y = gaussianHardTarget B ν BF κ x) :
    (NormalPhoton.numberForm B.normal (B.realization PhotonFock).functional).expectation
      (marginal B ν y) =
      (NormalPhoton.hardNumberForm B.normal (B.realization PhotonFock).functional κ).expectation
        (marginal B ν x) := by
  have hn := numberFromCoordinates_apply B (marginal_positive B ν hy)
  change numberFromCoordinates B (fullMarginal B ν y) = _ at hn
  exact hn.symm.trans ((congrArg (numberFromCoordinates B) h).trans
    (numberFromCoordinates_gaussianHardTarget B ν BF C κ hx))

end GptLean.PhysicalRemovalMarginal
