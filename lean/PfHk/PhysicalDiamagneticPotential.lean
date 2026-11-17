import GptLean.TransformationsPotentials

/-! The diamagnetic square of an actual L3+L-infinity vector potential
is an actual L^(3/2)+L-infinity scalar potential. This constructs the
shifted pair used by the gpt physical ground-state variational model. -/

noncomputable section
namespace PfHk.PhysicalDiamagneticPotential

open MeasureTheory GptLean GptLean.PhysicalPairSpace GptLean.PhysicalPairDuality
open GptLean.TransformationsPotentials
open scoped ENNReal RealInnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

private def cross (A : VectorPotential) (x : Position) : ℝ :=
  inner ℝ ((parts A).1 x) ((parts A).2 x)

private theorem cross_memLp (A : VectorPotential) : MemLp (cross A) 3 volume :=
  (innerSL ℝ (E := Vector)).memLp_of_bilin 3 (Lp.memLp (parts A).1) (Lp.memLp (parts A).2)

private def low (A : VectorPotential) (x : Position) : ℝ :=
  (1 / 2 : ℝ) * ‖(parts A).1 x‖ ^ 2 + clampOne (cross A x)

private def high (A : VectorPotential) (x : Position) : ℝ :=
  (1 / 2 : ℝ) * ‖(parts A).2 x‖ ^ 2 + (cross A x - clampOne (cross A x))

private theorem low_memLp (A : VectorPotential) : MemLp (low A) ∞ volume := by
  have hb := (Lp.memLp (parts A).1).norm
  have hb2 : MemLp (fun x => ‖(parts A).1 x‖ ^ 2) ∞ volume := by
    have hm : MemLp ((fun x => ‖(parts A).1 x‖) * fun x => ‖(parts A).1 x‖) ∞ volume :=
      hb.mul hb
    exact (memLp_congr_ae (Filter.Eventually.of_forall (fun x => by
      change ‖(parts A).1 x‖ * ‖(parts A).1 x‖ = ‖(parts A).1 x‖ ^ 2
      exact (pow_two _).symm))).mp hm
  exact (hb2.const_mul (1 / 2 : ℝ)).add (memLp_top_clampOne (cross_memLp A).aestronglyMeasurable)

private theorem high_memLp (A : VectorPotential) : MemLp (high A) (3 / 2) volume := by
  have hc2 : MemLp (fun x => ‖(parts A).2 x‖ ^ 2) (3 / 2) volume := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (Lp.memLp (parts A).2).norm_rpow_div 2
  exact (hc2.const_mul (1 / 2 : ℝ)).add (memLp_three_halves_sub_clampOne (cross_memLp A))

def halfSquare (A : VectorPotential) : ScalarPotential :=
  ofParts ((low_memLp A).toLp (low A)) ((high_memLp A).toLp (high A))

theorem coeFn_halfSquare (A : VectorPotential) :
    ((halfSquare A).val : Position → ℝ) =ᵐ[volume]
      (fun x => (1 / 2 : ℝ) * ‖A.val x‖ ^ 2) := by
  have he := coeFn_ofParts ((low_memLp A).toLp (low A)) ((high_memLp A).toLp (high A))
  filter_upwards [he, (low_memLp A).coeFn_toLp, (high_memLp A).coeFn_toLp,
    coeFn_parts A] with x hsum hlo hhi hA
  change (halfSquare A).val x = _ at hsum ⊢
  rw [hsum, hlo, hhi, hA, norm_add_sq_real]
  dsimp only [low, high, cross]
  ring

def shifted (v : ScalarPotential) (A : VectorPotential) : Potential :=
  (v + halfSquare A, A)

theorem shifted_scalar_ae (v : ScalarPotential) (A : VectorPotential) :
    ((shifted v A).1.val : Position → ℝ) =ᵐ[volume]
      (fun x => v.val x + (1 / 2 : ℝ) * ‖A.val x‖ ^ 2) := by
  filter_upwards [coeFn_sum_add v (halfSquare A), coeFn_halfSquare A] with x hsum hsq
  exact hsum.trans (congrArg (v.val x + ·) hsq)

theorem shifted_scalar_sum_ae (v : ScalarPotential) (A : VectorPotential) :
    ((shifted v A).1.val : Position → ℝ) =ᵐ[volume]
      (fun x => v.val x + (1 / 2 : ℝ) * ∑ i : Fin 3, A.val x i ^ 2) := by
  filter_upwards [shifted_scalar_ae v A] with x hx
  simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using hx

@[simp] theorem shifted_vector (v : ScalarPotential) (A : VectorPotential) :
    (shifted v A).2 = A := rfl

end PfHk.PhysicalDiamagneticPotential
