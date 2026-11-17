import PfHk.PhysicalExternalOperator
import PfHk.LpFiniteProducts

/-! Actual scalar multiplication commutes with finite coefficient sums. -/

noncomputable section
namespace PfHk.PhysicalExternalOperator

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalLocalEnergy

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]

theorem roughMultiply_sum (b : J → Position I → ℝ) (u : WaveSpace I)
    (hb : ∀ j, HasMultiplier (b j) u)
    (hs : HasMultiplier (fun x => ∑ j, b j x) u) :
    roughMultiply (fun x => ∑ j, b j x) u hs = ∑ j, roughMultiply (b j) u (hb j) := by
  unfold roughMultiply
  unfold HasMultiplier at hb hs
  exact LpFiniteProducts.sum b u hb hs

theorem roughMultiply_add (b c : Position I → ℝ) (u : WaveSpace I)
    (hb : HasMultiplier b u) (hc : HasMultiplier c u)
    (hs : HasMultiplier (fun x => b x + c x) u) :
    roughMultiply (fun x => b x + c x) u hs = roughMultiply b u hb + roughMultiply c u hc := by
  unfold roughMultiply
  unfold HasMultiplier at hb hc hs
  exact LpFiniteProducts.add b c u hb hc hs

end PfHk.PhysicalExternalOperator

