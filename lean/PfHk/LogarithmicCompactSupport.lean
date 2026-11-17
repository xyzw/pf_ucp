import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Compact support under the logarithmic radius and locality of ordinary
derivatives outside its compact interval. -/

noncomputable section
namespace PfHk.LogarithmicCompactSupport
open Set Filter
open scoped Topology

theorem exists_interval {X : Type*} [NormedAddCommGroup X]
    {K : Set X} (hK : IsCompact K) (t₀ : ℝ)
    (hKpos : ∀ x ∈ K, 0 < ‖x‖)
    (hKsmall : ∀ x ∈ K, ‖x‖ < Real.exp (-t₀)) :
    ∃ a b : ℝ, t₀ < a ∧ ∀ x ∈ K, -Real.log ‖x‖ ∈ Icc a b := by
  have hc : ContinuousOn (fun x : X => -Real.log ‖x‖) K :=
    (continuous_norm.continuousOn.log (fun x hx => ne_of_gt (hKpos x hx))).neg
  have hl (x : X) (hx : x ∈ K) : t₀ < -Real.log ‖x‖ := by
    have hh := Real.log_lt_log (hKpos x hx) (hKsmall x hx)
    rw [Real.log_exp] at hh
    linarith
  obtain ⟨a, ha, hla⟩ := hK.exists_forall_le' hc hl
  obtain ⟨b, hb⟩ := (hK.image_of_continuousOn hc).bddAbove
  exact ⟨a, b, ha, fun x hx => ⟨hla x hx, hb (mem_image_of_mem _ hx)⟩⟩

theorem derivative_zero_outside {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {u du : ℝ → H} {a b : ℝ}
    (hu : ∀ t, HasDerivAt u (du t) t)
    (hs : ∀ t, t ∉ Icc a b → u t = 0) :
    ∀ t, t ∉ Icc a b → du t = 0 := by
  intro t ht
  have he : u =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds ht] with s hs'
    exact hs s hs'
  exact (hu t).unique ((hasDerivAt_const t (0 : H)).congr_of_eventuallyEq he)

end PfHk.LogarithmicCompactSupport
