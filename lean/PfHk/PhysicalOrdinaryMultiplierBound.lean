import PfHk.PhysicalLocalEnergySobolev

/-! Scalar multiplication estimates in the ordinary electronic gradient.
These are independent of diamagnetism for the Pauli contraction. -/

noncomputable section
namespace PfHk.PhysicalOrdinaryMultiplierBound

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PhysicalLocalEnergy
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

variable {I : Type} [Fintype I] [DecidableEq I] (V : Position I → ℝ)

attribute [local irreducible] inclusion ordinary roughMultiply

theorem normGradientEnergy_le (u : Reference I V) :
    normGradientEnergy V u ≤ ∑ i, ‖ordinary I V i u‖ ^ 2 := by
  unfold normGradientEnergy
  apply Finset.sum_le_sum
  intro i _
  rw [l2_norm_sq]
  apply integral_mono
    ((normGradient_memLp V u i).integrable_sq)
    ((Lp.memLp (ordinary I V i u)).norm.integrable_sq)
  intro x
  have h : ‖normGradient V u i x‖ ≤ ‖ordinary I V i u x‖ :=
    PhysicalSourceCurrentBounds.norm_re_inner_div_norm_le _ _
  have hs := pow_le_pow_left₀ (norm_nonneg (normGradient V u i x)) h 2
  simpa only [Real.norm_eq_abs, sq_abs] using hs

theorem scalar_bound (w : Position I → ℝ) (ε C₀ : ℝ) (hε : 0 ≤ ε)
    (hSob : ScalarMultiplierBound w ε C₀) (u : Reference I V)
    (hu : HasMultiplier w (inclusion I V u)) :
    ‖roughMultiply w (inclusion I V u) hu‖ ^ 2 ≤
      ε * (∑ i, ‖ordinary I V i u‖ ^ 2) + C₀ * ‖inclusion I V u‖ ^ 2 :=
  (scalar_bound_on_physical_norm V w ε C₀ hSob u hu).trans
    (add_le_add (mul_le_mul_of_nonneg_left (normGradientEnergy_le V u) hε) le_rfl)

end PfHk.PhysicalOrdinaryMultiplierBound
