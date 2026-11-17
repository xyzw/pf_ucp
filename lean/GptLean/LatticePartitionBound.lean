import GptLean.LatticePartitionOne
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Monoid

/-!
The derivative energy of the normalized integer translates is continuous
and periodic. Its maximum on one compact period gives a uniform constant
for the concrete one-dimensional square partition.
-/

noncomputable section

namespace GptLean.LatticePartition

open Function Set
open scoped Topology

set_option backward.isDefEq.respectTransparency.types false

/-- Derivatives inherit the reindexing identity of the lattice partition. -/
theorem eta_deriv_translate (z k : ℤ) (x : ℝ) :
    deriv (eta z) (x + (k : ℝ)) = deriv (eta (z - k)) x := by
  calc
    deriv (eta z) (x + (k : ℝ)) = deriv (fun y => eta z (y + (k : ℝ))) x :=
      (deriv_comp_add_const (eta z) (k : ℝ) x).symm
    _ = deriv (eta (z - k)) x :=
      congrArg (fun f : ℝ → ℝ => deriv f x) (funext fun y => eta_translate z k y)

/-- Only finitely many partition derivatives occur near any point. -/
theorem eta_deriv_locallyFinite :
    LocallyFinite fun z : ℤ => support (deriv (eta z)) :=
  eta_locallyFinite.closure.subset fun _ => support_deriv_subset

theorem eta_deriv_sq_locallyFinite :
    LocallyFinite fun z : ℤ => support (fun x => deriv (eta z) x ^ 2) := by
  refine eta_deriv_locallyFinite.subset fun z x hx => ?_
  change deriv (eta z) x ≠ 0
  intro hz
  exact hx (by simp [hz])

/-- The squared derivative sum of the concrete one-dimensional partition. -/
def metric (x : ℝ) : ℝ := ∑' z : ℤ, deriv (eta z) x ^ 2

theorem metric_nonneg (x : ℝ) : 0 ≤ metric x :=
  tsum_nonneg fun _ => sq_nonneg _

theorem metric_continuous : Continuous metric := by
  have hc : Continuous fun x : ℝ => ∑ᶠ z : ℤ, deriv (eta z) x ^ 2 :=
    continuous_finsum
      (fun z => ((eta_contDiff z).continuous_deriv (by simp)).pow 2)
      eta_deriv_sq_locallyFinite
  convert hc using 1
  funext x
  exact tsum_eq_finsum (eta_deriv_sq_locallyFinite.point_finite x)

theorem metric_translate (k : ℤ) (x : ℝ) : metric (x + (k : ℝ)) = metric x := by
  simp only [metric, eta_deriv_translate]
  simpa only [Equiv.coe_addRight, sub_eq_add_neg] using
    (Equiv.addRight (-k)).tsum_eq (fun z : ℤ => deriv (eta z) x ^ 2)

theorem metric_periodic : Function.Periodic metric 1 := by
  intro x
  simpa using metric_translate 1 x

theorem metric_fract (x : ℝ) : metric (Int.fract x) = metric x := by
  simpa only [Int.fract_add_floor] using (metric_translate ⌊x⌋ (Int.fract x)).symm

/-- The one-dimensional lattice partition has a uniform derivative bound. -/
theorem exists_metric_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x, (∑' z : ℤ, deriv (eta z) x ^ 2) ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      metric_continuous.continuousOn
  refine ⟨|C| + 1, by positivity, fun x => ?_⟩
  change metric x ≤ |C| + 1
  have hx : Int.fract x ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  calc
    metric x = metric (Int.fract x) := (metric_fract x).symm
    _ ≤ ‖metric (Int.fract x)‖ := le_abs_self _
    _ ≤ C := hC _ hx
    _ ≤ |C| + 1 := by linarith [le_abs_self C]

end GptLean.LatticePartition
