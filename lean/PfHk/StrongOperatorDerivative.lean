import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Module

/-! Product differentiation for a strongly differentiable family of
bounded operators with a local uniform norm bound. -/

noncomputable section
namespace PfHk.StrongOperatorDerivative

open Filter
open scoped Topology
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {X D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem tendsto_apply {l : Filter X} {A : X → D →L[ℝ] H} {A₀ : D →L[ℝ] H}
    {v : X → D} {v₀ : D} {C : ℝ}
    (hA : ∀ u, Tendsto (fun x => A x u) l (𝓝 (A₀ u)))
    (hbound : ∀ᶠ x in l, ‖A x‖ ≤ C) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun x => A x (v x)) l (𝓝 (A₀ v₀)) := by
  have hsmall : Tendsto (fun x => A x (v x - v₀)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
      (show Tendsto (fun x => C * ‖v x - v₀‖) l (𝓝 0) by
        have hc : Tendsto (fun _ : X => v₀) l (𝓝 v₀) := tendsto_const_nhds
        simpa using ((hv.sub hc).norm.const_mul C))
    exact hbound.mono fun x hx => ((A x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have h := hsmall.add (hA v₀)
  simpa only [map_sub, sub_add_cancel, zero_add] using h

theorem hasDerivAt_apply {A : ℝ → D →L[ℝ] H} {dA : D → H}
    {q : ℝ → D} {dq : D} {t C : ℝ}
    (hA : ∀ u, HasDerivAt (fun s => A s u) (dA u) t)
    (hbound : ∀ᶠ s in 𝓝 t, ‖A s‖ ≤ C) (hq : HasDerivAt q dq t) :
    HasDerivAt (fun s => A s (q s)) (A t dq + dA (q t)) t := by
  have ht : Tendsto (fun h : ℝ => t + h) (𝓝[≠] 0) (𝓝 t) := by
    have hz : Tendsto (fun h : ℝ => h) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hc : Tendsto (fun _ : ℝ => t) (𝓝[≠] (0 : ℝ)) (𝓝 t) := tendsto_const_nhds
    simpa only [add_zero] using hc.add hz
  have happly := tendsto_apply (A₀ := A t)
    (fun u => (hA u).continuousAt.tendsto.comp ht) (ht.eventually hbound) hq.tendsto_slope_zero
  have h := happly.add (hA (q t)).tendsto_slope_zero
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  convert h using 1
  funext h
  simp only [map_smul, map_sub]
  module

end PfHk.StrongOperatorDerivative
