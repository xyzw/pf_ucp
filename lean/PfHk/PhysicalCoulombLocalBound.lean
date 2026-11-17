import GptLean.PhysicalCoulombH1
import PfHk.ConfigurationGeometry

/-! The actual repulsive pair Coulomb potential is nonnegative and
measurable globally, and bounded on a neighborhood of every regular
configuration. No local boundedness of the interaction is assumed. -/

noncomputable section
namespace PfHk.PhysicalCoulombLocalBound

open MeasureTheory GptLean GptLean.SymmetricLift
open scoped ENNReal Topology

set_option Elab.async false
set_option maxHeartbeats 20000

variable {N : ℕ}

theorem potential_continuousAt {O : Configuration N}
    (hO : O ∈ distinctConfigurations N) : ContinuousAt (PhysicalCoulombH1.potential N) O := by
  unfold PhysicalCoulombH1.potential
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  by_cases hij : i < j
  · simp only [if_pos hij]
    exact ((pairDifferenceLinear i j).continuous_of_finiteDimensional.continuousAt.norm).inv₀
      (ne_of_gt (pairDistance_pos_of_distinct hO (ne_of_lt hij)))
  · simp only [if_neg hij]
    exact continuousAt_const

theorem local_memLp_top_of_continuousAt (b : Configuration N → ℝ)
    (hb : AEStronglyMeasurable b volume) {O : Configuration N} (hc : ContinuousAt b O) :
    ∃ ρ : ℝ, 0 < ρ ∧ MemLp b ∞ (volume.restrict (Metric.ball O ρ)) := by
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.continuousAt_iff.mp hc 1 (by norm_num)
  refine ⟨ρ, hρ, memLp_top_of_bound hb.restrict (‖b O‖ + 1) ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_ball] with X hX
  have hdist : ‖b X - b O‖ < 1 := by
    simpa only [dist_eq_norm] using hsmall hX
  exact (norm_le_norm_sub_add (b X) (b O)).trans (by linarith only [hdist])

theorem scaled_potential_nonneg (c : ℝ) (hc : 0 ≤ c) (X : Configuration N) :
    0 ≤ c * PhysicalCoulombH1.potential N X :=
  mul_nonneg hc (PhysicalCoulombH1.potential_nonneg N X)

theorem scaled_potential_measurable (c : ℝ) :
    Measurable (fun X : Configuration N => c * PhysicalCoulombH1.potential N X) :=
  measurable_const.mul (PhysicalCoulombH1.potential_measurable N)

theorem scaled_potential_local_memLp (c : ℝ) {O : Configuration N}
    (hO : O ∈ distinctConfigurations N) :
    ∃ ρ : ℝ, 0 < ρ ∧ MemLp (fun X => c * PhysicalCoulombH1.potential N X) ∞
      (volume.restrict (Metric.ball O ρ)) :=
  local_memLp_top_of_continuousAt _ (scaled_potential_measurable c).aestronglyMeasurable
    (continuousAt_const.mul (potential_continuousAt hO))

end PfHk.PhysicalCoulombLocalBound
