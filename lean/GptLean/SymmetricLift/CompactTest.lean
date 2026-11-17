import GptLean.SymmetricLift.WeakDerivativeClosure
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Helpers for assembling local Sobolev approximation into actual weak
derivative identities. Restricted L2 control suffices for an integrable
test product when the test vanishes outside the restriction set. The final
lemma combines two independently proved strong L2 convergence statements.
No compactness, approximation existence or tested-integral limit is assumed.
-/

namespace GptLean.SymmetricLift

open MeasureTheory Filter
open scoped ENNReal Topology

variable {X V : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Local L2 control gives a globally integrable test product when the test
vanishes off the set on which the L2 control is known. -/
theorem integrable_smul_of_memLp_on_support {K : Set X} {φ : X → ℝ} {f : X → V}
    (hφ : MemLp φ 2 (μ.restrict K)) (hf : MemLp f 2 (μ.restrict K))
    (hzero : ∀ x, x ∉ K → φ x = 0) : Integrable (fun x => φ x • f x) μ := by
  have hsupp : Function.support (fun x => φ x • f x) ⊆ K := by
    intro x hx
    by_contra hxK
    apply hx
    change φ x • f x = 0
    rw [hzero x hxK, zero_smul]
  apply (integrableOn_iff_integrable_of_support_subset hsupp).mp
  exact memLp_one_iff_integrable.mp (hf.smul hφ)

/-- A supported test has the same pairing against the full measure and its
restriction, without a separate global integrability assumption. -/
theorem integral_smul_eq_setIntegral {K : Set X} {φ : X → ℝ} (f : X → V)
    (hzero : ∀ x, x ∉ K → φ x = 0) :
    (∫ x, φ x • f x ∂μ) = ∫ x in K, φ x • f x ∂μ := by
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro x hx
  rw [hzero x hx, zero_smul]

omit [NormedSpace ℝ V] in
/-- Strong L2 convergence is preserved by addition, stated for raw functions
and their L2 seminorm errors. -/
theorem tendsto_eLpNorm_add_of_tendsto
    {A : Type*} {l : Filter A} {fn gn : A → X → V} {f g : X → V}
    (hfn : ∀ n, MemLp (fn n) 2 μ) (hgn : ∀ n, MemLp (gn n) 2 μ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfconv : Tendsto (fun n => eLpNorm (fn n - f) 2 μ) l (𝓝 0))
    (hgconv : Tendsto (fun n => eLpNorm (gn n - g) 2 μ) l (𝓝 0)) :
    Tendsto (fun n => eLpNorm ((fn n + gn n) - (f + g)) 2 μ) l (𝓝 0) := by
  have hF := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fn hfn f hf).mpr hfconv
  have hG := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' gn hgn g hg).mpr hgconv
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => fn n + gn n)
    (fun n => (hfn n).add (hgn n)) (f + g) (hf.add hg)).mp
  have hsum : (fun n => ((hfn n).add (hgn n)).toLp (fn n + gn n)) =
      (fun n => (hfn n).toLp (fn n) + (hgn n).toLp (gn n)) := by
    funext n
    exact MemLp.toLp_add (hfn n) (hgn n)
  rw [hsum, MemLp.toLp_add hf hg]
  exact hF.add hG

end GptLean.SymmetricLift
