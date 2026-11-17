import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Module

/-! A continuous family of bounded linear directional derivatives is a
genuine continuous Fréchet derivative. This elementary calculus lemma
upgrades the already proved physical line derivatives. -/

noncomputable section
namespace PfHk.C1FromLines

open Filter Asymptotics Set
open scoped Topology
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem curve_hasDerivAt {f : E → H} {L : E → E →L[ℝ] H}
    (hf : ∀ x v, HasLineDerivAt ℝ f (L x v) x v) (x v : E) (t : ℝ) :
    HasDerivAt (fun s => f (x + s • v)) (L (x + t • v) v) t := by
  have h₀ : HasDerivAt (fun s : ℝ => f ((x + t • v) + s • v))
      (L (x + t • v) v) (0 : ℝ) := hf (x + t • v) v
  have h₀' : HasDerivAt (fun s : ℝ => f ((x + t • v) + s • v))
      (L (x + t • v) v) (t - t) := by simpa only [sub_self] using h₀
  have h := h₀'.scomp (h := fun s : ℝ => s - t) t ((hasDerivAt_id t).sub_const t)
  convert! h using 1
  · funext s
    congr 1
    module
  · simp

theorem hasFDerivAt {f : E → H} {L : E → E →L[ℝ] H}
    (hf : ∀ x v, HasLineDerivAt ℝ f (L x v) x v) {x : E} (hL : ContinuousAt L x) :
    HasFDerivAt f (L x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  obtain ⟨r, hr, hclose⟩ := Metric.continuousAt_iff.mp hL ε hε
  apply Metric.mem_nhds_iff.mpr
  refine ⟨r, hr, ?_⟩
  intro h hh
  have hhn : ‖h‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hh
  let g : ℝ → H := fun s => f (x + s • h) - f x - s • L x h
  have hd (s : ℝ) : HasDerivAt g ((L (x + s • h) - L x) h) s := by
    have hd := ((curve_hasDerivAt hf x h s).sub_const (f x)).sub
      ((hasDerivAt_id s).smul_const (L x h))
    convert! hd using 1 <;>
      simp only [g, ContinuousLinearMap.sub_apply, one_smul, Pi.sub_apply, id_eq]
  have hb (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ‖deriv g s‖ ≤ ε * ‖h‖ := by
    rw [(hd s).deriv]
    have hdist : dist (x + s • h) x < r := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hs.1]
      exact (mul_le_of_le_one_left (norm_nonneg h) hs.2).trans_lt hhn
    have hop : ‖L (x + s • h) - L x‖ ≤ ε := (by
      simpa only [dist_eq_norm] using hclose hdist : ‖L (x + s • h) - L x‖ < ε).le
    exact ((L (x + s • h) - L x).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right hop (norm_nonneg h))
  have hbound := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun s (_ : s ∈ Icc (0 : ℝ) 1) => (hd s).differentiableAt) hb
    (convex_Icc (0 : ℝ) 1) (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  change ‖f (x + h) - f x - L x h‖ ≤ ε * ‖h‖
  simpa only [g, one_smul, zero_smul, add_zero, sub_self, sub_zero,
    norm_one, mul_one] using hbound

theorem contDiff_one {f : E → H} {L : E → E →L[ℝ] H}
    (hf : ∀ x v, HasLineDerivAt ℝ f (L x v) x v) (hL : Continuous L) :
    ContDiff ℝ (1 : ℕ∞) f :=
  contDiff_one_iff_hasFDerivAt.mpr ⟨L, hL, fun _ => hasFDerivAt hf hL.continuousAt⟩

end PfHk.C1FromLines
