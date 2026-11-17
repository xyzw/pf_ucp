import GptLean.PhysicalPairDuality
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! Every actual L-infinity plus finite-Lp coefficient admits a bounded
part and an arbitrarily small Lp remainder. This is proved from density
of simple functions and does not contain a Sobolev or physical form bound. -/

noncomputable section
namespace PfHk.ScalarLpDecomposition

open MeasureTheory GptLean.PhysicalPairDuality
open scoped ENNReal

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}

theorem small_parts (v : LpSum ℝ p μ) (hp : p ≠ ∞) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b c : X → ℝ, MemLp b ∞ μ ∧ MemLp c p μ ∧
      (v.val : X → ℝ) =ᵐ[μ] (fun x => b x + c x) ∧ (eLpNorm c p μ).toReal < δ := by
  let a := parts v
  obtain ⟨g, hg, hgp⟩ := (Lp.memLp a.2).exists_simpleFunc_eLpNorm_sub_lt hp
    (ENNReal.ofReal_ne_zero_iff.mpr hδ)
  let b : X → ℝ := fun x => a.1 x + g x
  let c : X → ℝ := fun x => a.2 x - g x
  have hb : MemLp b ∞ μ := (Lp.memLp a.1).add (g.memLp_top μ)
  have hc : MemLp c p μ := (Lp.memLp a.2).sub hgp
  have hparts : (v.val : X → ℝ) =ᵐ[μ] fun x => a.1 x + a.2 x := by
    have he : a.1.val + a.2.val = v.val := parts_spec v
    exact (Filter.EventuallyEq.of_eq
      (congrArg (fun f : X →ₘ[μ] ℝ => (f : X → ℝ)) he.symm)).trans
        (AEEqFun.coeFn_add a.1.val a.2.val)
  refine ⟨b, c, hb, hc, ?_, ?_⟩
  · filter_upwards [hparts] with x hx
    exact hx.trans (by dsimp [b, c]; ring)
  · have he := (ENNReal.toReal_lt_toReal hc.eLpNorm_ne_top ENNReal.ofReal_ne_top).mpr hg
    simpa only [ENNReal.toReal_ofReal hδ.le] using he

end PfHk.ScalarLpDecomposition
