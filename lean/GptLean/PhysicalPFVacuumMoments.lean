import GptLean.PhysicalPFVacuumInsertion
import GptLean.PhysicalFockHardVacuumTraceBounds
import GptLean.PhysicalPhotonMarginalMoments

/-!
The actual spatial vacuum insertion kills the full soft-photon energy.
The number estimate holds on the same full normal state, obtained through
the actual photon marginal rather than a separate family of test values.
-/

noncomputable section

namespace GptLean.PhysicalPFVacuumInsertion

open MeasureTheory PhysicalFock PhysicalNormalTrace PhysicalPhotonMarginal
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Type} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ]
  (B : StandardNormalTraceBackground) (BF : StandardSymmetricFockExponential)

theorem insertion_softEnergy (κ : ℝ)
    (x : B.Trace (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ))
    (hx : x ∈ (B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ)).rank.positive) :
    (fullForm B μ (NormalPhoton.softEnergyForm (B.normal (H := PhotonFock))
      (B.realization PhotonFock).functional κ)).expectation
        (B.push (insertion μ BF κ).toContinuousLinearMap x) = 0 := by
  rw [fullForm_expectation, insertion_marginal μ BF κ B hx]
  exact hardPhotonVacuumEmbedding_push_softEnergy B BF κ (marginal B μ x)
    (marginal_positive B μ hx)

theorem insertion_rankOne_softEnergy (κ : ℝ)
    (v : Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ) :
    (fullForm B μ (NormalPhoton.softEnergyForm (B.normal (H := PhotonFock))
      (B.realization PhotonFock).functional κ)).expectation
        ((B.realization (Lp PhotonFock 2 μ)).rank.rankOne (insertion μ BF κ v)) = 0 := by
  have h := insertion_softEnergy μ B BF κ _
    ((B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ)).rank.rankOne_positive v)
  rw [B.push_rankOne] at h
  exact h

theorem insertion_number_le {κ : ℝ} (hκ : 0 < κ)
    (x : B.Trace (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ))
    (hx : x ∈ (B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ)).rank.positive) :
    (fullForm B μ (NormalPhoton.numberForm (B.normal (H := PhotonFock))
      (B.realization PhotonFock).functional)).expectation
        (B.push (insertion μ BF κ).toContinuousLinearMap x) ≤
      ENNReal.ofReal κ⁻¹ *
        (fullForm B μ (NormalPhoton.radiationForm (B.normal (H := PhotonFock))
          (B.realization PhotonFock).functional)).expectation
            (B.push (insertion μ BF κ).toContinuousLinearMap x) := by
  let E : RemovalState.PositiveForm (B.traceData (H := PhotonFock)) :=
    NormalPhoton.numberForm (B.normal (H := PhotonFock)) (B.realization PhotonFock).functional
  let F : RemovalState.PositiveForm (B.traceData (H := PhotonFock)) :=
    NormalPhoton.radiationForm (B.normal (H := PhotonFock)) (B.realization PhotonFock).functional
  change E.expectation (marginal B μ (B.push (insertion μ BF κ).toContinuousLinearMap x)) ≤
    ENNReal.ofReal κ⁻¹ *
      F.expectation (marginal B μ (B.push (insertion μ BF κ).toContinuousLinearMap x))
  have he := insertion_marginal μ BF κ B hx
  have hn := congrArg E.expectation he
  have hr := congrArg F.expectation he
  exact hn.le.trans
    ((hardPhotonVacuumEmbedding_push_number_le B BF hκ (marginal B μ x)
      (marginal_positive B μ hx)).trans_eq
        (congrArg (fun t : ℝ≥0∞ => ENNReal.ofReal κ⁻¹ * t) hr.symm))

end GptLean.PhysicalPFVacuumInsertion
