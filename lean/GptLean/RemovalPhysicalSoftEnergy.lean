import GptLean.RemovalLatticeOutput
import GptLean.RemovalOptimized

/-!
The ordinary original spectral trace identity identifies the removed
energy with the physical soft form. Both the free-scale and optimized
estimates retain the same output state and all its proved properties.
-/

namespace GptLean.RemovalEnergy

open SoftRemoval RemovalAssembly
open scoped ENNReal

variable {M Pair Marginal Hs : Type*} [NormedAddCommGroup Hs]

theorem spectral_soft_energy_identification (soft : M → ℝ≥0∞) (m : M)
    (vectors : ℕ → Hs)
    (original : soft m = ENNReal.ofReal (∑' n, ‖vectors n‖ ^ 2)) :
    soft m < ⊤ ∧ (soft m).toReal = ∑' n, ‖vectors n‖ ^ 2 := by
  rw [original]
  exact ⟨ENNReal.ofReal_lt_top, ENNReal.toReal_ofReal (tsum_nonneg (fun n => sq_nonneg _))⟩

/-- The physical soft energy is subtracted on the very same constructed
state. Only the original state's usual spectral trace formula is added. -/
theorem localizedOutput_physical_soft_energy_bound
    {B : DFT.StateModel M Pair} {m : M} {marginal : M → Marginal} {target : Marginal}
    {C e k R a b : ℝ} (soft : M → ℝ≥0∞) (vectors : ℕ → Hs)
    (original : soft m = ENNReal.ofReal (∑' n, ‖vectors n‖ ^ 2))
    (out : LocalizedOutput B m marginal target (∑' n, ‖vectors n‖ ^ 2) C e k R a b)
    (hC : 0 ≤ C) (he : 0 ≤ e) (hk : 0 ≤ k) :
    soft m < ⊤ ∧
      B.energy out.state ≤ B.energy m - (soft m).toReal +
        C * RemovalEstimates.scaleError e k R b (a ^ 2 * (soft m).toReal + b ^ 2) := by
  obtain ⟨hfinite, heq⟩ := spectral_soft_energy_identification soft m vectors original
  refine ⟨hfinite, ?_⟩
  rw [heq]
  exact out.energy_bound hC he hk

/-- Optimizing the actual scale family retains every property of the
chosen output, including zero soft energy and fermionic support, while
the removed term is the original physical soft expectation. -/
theorem optimized_physical_output_with_property
    {B : DFT.StateModel M Pair} (m : M) (marginal : M → Marginal) (target : Marginal)
    (property : M → Prop) (soft : M → ℝ≥0∞) (vectors : ℕ → Hs)
    (original : soft m = ENNReal.ofReal (∑' n, ‖vectors n‖ ^ 2))
    {C e k a b : ℝ} (hC : 0 ≤ C) (he : 0 ≤ e) (hk : 0 < k) (hk1 : k ≤ 1)
    (outputs : ∀ R, 1 ≤ R → k * R ≤ 1 →
      {out : LocalizedOutput B m marginal target (∑' n, ‖vectors n‖ ^ 2) C e k R a b //
        property out.state}) :
    soft m < ⊤ ∧ ∃ r, B.density r = B.density m ∧ marginal r = target ∧ property r ∧
      B.energy r ≤ B.energy m - (soft m).toReal +
        (3 * C) * SoftPurification.removalError e k a b (soft m).toReal := by
  obtain ⟨hfinite, heq⟩ := spectral_soft_energy_identification soft m vectors original
  refine ⟨hfinite, ?_⟩
  rw [heq]
  exact optimized_output_with_property m marginal target property hC he hk hk1
    (tsum_nonneg (fun n => sq_nonneg _)) outputs

end GptLean.RemovalEnergy
