import PfHk.OrdinaryWeakSobolev
import PfHk.ScalarSobolevNormAlgebra
import PfHk.PhysicalScalarSobolev

/-! The scalar Sobolev input of the zero-set recurrence is a theorem.
Its exponent, dimension identity and constant are constructed from the
ordinary weak Sobolev inequality. -/

noncomputable section
namespace PfHk.ScalarSobolevFromWeak

open MeasureTheory GptLean GptLean.PhysicalPFReference
  PfHk.PhysicalInfiniteOrder
open scoped ENNReal NNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 30000

variable {I : Type} [Fintype I] [DecidableEq I]

theorem exists_scalarSobolevBound (hd : 2 < Fintype.card I) :
    ∃ p q S : ℝ, p.HolderConjugate q ∧ (Fintype.card I : ℝ) = 2 * q ∧
      0 ≤ S ∧ ScalarSobolevBound (I := I) p S := by
  let d : ℝ := Fintype.card I
  have hd2 : 2 < d := by
    dsimp [d]
    exact_mod_cast hd
  have hd0 : 0 < d := by linarith only [hd2]
  have hm : 0 < d - 2 := by linarith only [hd2]
  let p : ℝ := d / (d - 2)
  let q : ℝ := d / 2
  have hp : 0 < p := div_pos hd0 hm
  have hp1 : 1 < p := (one_lt_div hm).mpr (by linarith only [hd2])
  have hpq : p.HolderConjugate q := Real.holderConjugate_iff.mpr ⟨hp1, by
    dsimp [p, q]
    field_simp [hd0.ne', hm.ne']
    <;> ring⟩
  let r : ℝ≥0 := ⟨2 * p, (mul_pos (by norm_num) hp).le⟩
  have hr : (r : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (Fintype.card I : ℝ)⁻¹ := by
    change (2 * (d / (d - 2)))⁻¹ = (2 : ℝ)⁻¹ - d⁻¹
    field_simp [hd0.ne', hm.ne']
    <;> ring
  let S : ℝ := (OrdinaryWeakSobolev.constant I : ℝ) ^ 2 * Fintype.card I
  refine ⟨p, q, S, hpq, ?_, by dsimp [S]; positivity, ?_⟩
  · dsimp [q, d]
    ring
  · intro f g hw hf hg
    have h := OrdinaryWeakSobolev.weak_bound (by omega : 0 < Fintype.card I) hr f g hw hf hg
    have hrp : (r : ℝ≥0∞) = ENNReal.ofReal (2 * p) := by
      exact ENNReal.ofReal_coe_nnreal.symm
    have hm : MemLp f (ENNReal.ofReal (2 * p)) volume := by
      simpa only [hrp] using h.1
    have hb : (eLpNorm f (ENNReal.ofReal (2 * p)) volume).toReal ^ 2 ≤
        S * ∑ i, ∫ x, g i x ^ 2 := by
      simpa only [hrp] using h.2
    exact ⟨ScalarSobolevNormAlgebra.square_memLp hp hm,
      (ScalarSobolevNormAlgebra.square_integral_rpow hp hm).le.trans hb⟩

end PfHk.ScalarSobolevFromWeak
