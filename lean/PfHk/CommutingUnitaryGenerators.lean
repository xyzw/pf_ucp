import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

/-! Weak generator pairings from commuting unitary curves. The proof
differentiates a scalar pairing twice and needs no operator products or
second derivatives of a vector. -/

noncomputable section
namespace PfHk.CommutingUnitaryGenerators

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedSpace ℝ H]

/-- The pairing identity supplied by two commuting unitary groups implies
the mixed pairing identity for their first derivatives at zero. -/
theorem paired_derivatives (U V : ℝ → H → H) (u v a b c d : H)
    (hpair : ∀ s t : ℝ,
      inner ℂ (U t u) (V s v) = inner ℂ (V (-s) u) (U (-t) v))
    (ha : HasDerivAt (fun t => U t u) a 0)
    (hb : HasDerivAt (fun t => U t v) b 0)
    (hc : HasDerivAt (fun t => V t u) c 0)
    (hd : HasDerivAt (fun t => V t v) d 0) :
    inner ℂ a d = inner ℂ c b := by
  have hnV : HasDerivAt (fun t : ℝ => V (-t) u) (-c) 0 := by
    simpa only [neg_zero, Function.comp_def, Pi.neg_apply, id_eq, neg_smul, one_smul] using
      hc.scomp_of_eq (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).neg) (by simp)
  have hnU : HasDerivAt (fun t : ℝ => U (-t) v) (-b) 0 := by
    simpa only [neg_zero, Function.comp_def, Pi.neg_apply, id_eq, neg_smul, one_smul] using
      hb.scomp_of_eq (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).neg) (by simp)
  have hfirst (t : ℝ) : inner ℂ (U t u) d = -inner ℂ c (U (-t) v) := by
    have hl := (hasDerivAt_const (0 : ℝ) (U t u)).inner ℂ hd
    have hr := hnV.inner ℂ (hasDerivAt_const (0 : ℝ) (U (-t) v))
    have he := hl.unique (hr.congr_of_eventuallyEq
      (Eventually.of_forall (fun s => hpair s t)))
    simpa only [inner_zero_left, inner_zero_right, zero_add, add_zero,
      inner_neg_left] using he
  have hl := ha.inner ℂ (hasDerivAt_const (0 : ℝ) d)
  have hr := ((hasDerivAt_const (0 : ℝ) c).inner ℂ hnU).neg
  have he := hl.unique (hr.congr_of_eventuallyEq (Eventually.of_forall hfirst))
  simpa only [inner_zero_left, inner_zero_right, zero_add, add_zero,
    inner_neg_right, neg_neg] using he

end PfHk.CommutingUnitaryGenerators
