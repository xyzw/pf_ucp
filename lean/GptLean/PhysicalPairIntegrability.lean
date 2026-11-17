import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.NormNum

/-!
Integrability of physical densities and currents from their Hilbert-valued
source representatives. The current is the real covariant inner product,
with all components in the Euclidean norm. Holder gives the article's
L1 and L(3/2) current spaces from an L2 and L6 source and L2 derivatives.
No integrability or spatial-space membership of the output pair is assumed.
The Sobolev input on the source is kept separate from this algebraic step.
-/

noncomputable section

namespace GptLean.PhysicalPairIntegrability

open MeasureTheory
open scoped ENNReal

variable {X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The real covariant pairing used by the combined current. -/
def currentComponent (u v : H) : ℝ := (inner ℂ u v).re

theorem abs_currentComponent_le (u v : H) :
    |currentComponent u v| ≤ ‖u‖ * ‖v‖ :=
  (Complex.abs_re_le_norm _).trans (norm_inner_le_norm u v)

theorem currentComponent_measurable {u v : X → H}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun x => currentComponent (u x) (v x)) μ :=
  Complex.continuous_re.comp_aestronglyMeasurable (hu.inner hv)

/-- Holder applies to the actual current pairing, including its sign. -/
theorem currentComponent_memLp {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    {u v : X → H} (hu : MemLp u p μ) (hv : MemLp v q μ) :
    MemLp (fun x => currentComponent (u x) (v x)) r μ := by
  have hproduct : MemLp (fun x => ‖u x‖ * ‖v x‖) r μ := hv.norm.mul' hu.norm
  apply hproduct.of_le_mul (c := 1) (currentComponent_measurable hu.1 hv.1)
  filter_upwards [] with x
  simpa only [one_mul, Real.norm_eq_abs, abs_mul, abs_norm] using
    abs_currentComponent_le (u x) (v x)

theorem currentComponent_eLpNorm_le {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    {u v : X → H} (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ) :
    eLpNorm (fun x => currentComponent (u x) (v x)) r μ ≤
      eLpNorm u p μ * eLpNorm v q μ := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := p) (q := q) (r := r) hu hv
    (fun a b : H => currentComponent a b) 1
    (Filter.Eventually.of_forall fun x => by
      simpa only [NNReal.coe_one, one_mul, Real.norm_eq_abs] using
        abs_currentComponent_le (u x) (v x))
  simpa only [ENNReal.coe_one, one_mul] using h

/-- The particle marginal of a Hilbert-valued source. Its fiber can also
contain the spectral-ensemble index, so this formula covers mixed states. -/
def density (N : ℕ) (u : X → H) : X → ℝ := fun x => (N : ℝ) * ‖u x‖ ^ 2

variable {ι : Type*} [Fintype ι]

def current (N : ℕ) (u : X → H) (d : ι → X → H) : X → EuclideanSpace ℝ ι :=
  fun x => WithLp.toLp 2 (fun i => (N : ℝ) * currentComponent (u x) (d i x))

omit [MeasurableSpace X] [Fintype ι] in
@[simp] theorem current_apply (N : ℕ) (u : X → H) (d : ι → X → H) (x : X) (i : ι) :
    current N u d x i = (N : ℝ) * currentComponent (u x) (d i x) := rfl

omit [MeasurableSpace X] [InnerProductSpace ℂ H] in
theorem density_nonneg (N : ℕ) (u : X → H) (x : X) : 0 ≤ density N u x := by
  exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

omit [InnerProductSpace ℂ H] in
theorem density_memLp_one (N : ℕ) {u : X → H} (hu : MemLp u 2 μ) :
    MemLp (density N u) 1 μ := by
  have h : MemLp (fun x => ‖u x‖ ^ 2) 1 μ := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      ENNReal.div_self (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)] using
      hu.norm_rpow_div 2
  exact h.const_mul N

omit [InnerProductSpace ℂ H] in
theorem density_memLp_three (N : ℕ) {u : X → H} (hu : MemLp u 6 μ) :
    MemLp (density N u) 3 μ := by
  have h : MemLp (fun x => ‖u x‖ ^ 2) 3 μ := by
    have hdiv : (6 : ℝ≥0∞) / 2 = 3 :=
      (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        (by norm_num [ENNReal.toReal_div])
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hdiv] using hu.norm_rpow_div 2
  exact h.const_mul N

theorem current_memLp_one (N : ℕ) {u : X → H} {d : ι → X → H}
    (hu : MemLp u 2 μ) (hd : ∀ i, MemLp (d i) 2 μ) :
    MemLp (current N u d) 1 μ := by
  apply MemLp.of_eval_piLp
  intro i
  exact (currentComponent_memLp hu (hd i)).const_mul N

theorem current_memLp_three_halves (N : ℕ) {u : X → H} {d : ι → X → H}
    (hu : MemLp u 6 μ) (hd : ∀ i, MemLp (d i) 2 μ) :
    MemLp (current N u d) (3 / 2) μ := by
  let : ENNReal.HolderTriple 6 2 (3 / 2) :=
    ENNReal.HolderTriple.of_toReal ⟨by norm_num [ENNReal.toReal_div], by norm_num, by norm_num⟩
  apply MemLp.of_eval_piLp
  intro i
  exact (currentComponent_memLp hu (hd i)).const_mul N

/-- Both components belong to precisely the two integrability spaces
used by the article, from one common source and its covariant derivatives. -/
theorem pair_memLp (N : ℕ) {u : X → H} {d : ι → X → H}
    (hu₂ : MemLp u 2 μ) (hu₆ : MemLp u 6 μ) (hd : ∀ i, MemLp (d i) 2 μ) :
    MemLp (density N u) 1 μ ∧ MemLp (density N u) 3 μ ∧
      MemLp (current N u d) 1 μ ∧ MemLp (current N u d) (3 / 2) μ :=
  ⟨density_memLp_one N hu₂, density_memLp_three N hu₆,
    current_memLp_one N hu₂ hd, current_memLp_three_halves N hu₆ hd⟩

end GptLean.PhysicalPairIntegrability
