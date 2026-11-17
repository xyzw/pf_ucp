import PfHk.SpinfulCounterexampleField
import PfHk.CounterexamplePotentials

/-! The cylindrical spinful family in the actual global potential spaces. -/

noncomputable section
namespace PfHk.SpinfulCounterexamplePotentials

open MeasureTheory Filter GptLean.PhysicalPairDuality GptLean.TransformationsPotentials
  PfHk.SpinfulCounterexampleField
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 400000

abbrev coulomb := CounterexamplePotentials.coulomb

theorem vector_memLp_top (t : ℝ) : MemLp (vectorPotential t) ∞ volume :=
  field_memLp_top.const_smul t

def vector (t : ℝ) : VectorPotential :=
  ofParts ((vector_memLp_top t).toLp (vectorPotential t)) 0

theorem vector_ae (t : ℝ) :
    ((vector t).val : Space → Space) =ᵐ[volume] vectorPotential t :=
  (coeFn_ofParts_zero ((vector_memLp_top t).toLp (vectorPotential t))).trans
    (vector_memLp_top t).coeFn_toLp

theorem zeeman_memLp_top (t : ℝ) : MemLp (fun x => t * weight x ^ 2) ∞ volume := by
  have hsq : MemLp (fun x => weight x ^ 2) ∞ volume := by
    apply (weight_memLp_top.mul weight_memLp_top).ae_eq
    exact ae_of_all _ fun x => by simp only [Pi.mul_apply, pow_two]
  exact hsq.const_mul t

def zeeman (t : ℝ) : ScalarPotential :=
  ofParts ((zeeman_memLp_top t).toLp (fun x => t * weight x ^ 2)) 0

theorem zeeman_ae (t : ℝ) :
    ((zeeman t).val : Space → ℝ) =ᵐ[volume] fun x => t * weight x ^ 2 :=
  (coeFn_ofParts_zero ((zeeman_memLp_top t).toLp (fun x => t * weight x ^ 2))).trans
    (zeeman_memLp_top t).coeFn_toLp

def scalar (Z t : ℝ) : ScalarPotential :=
  coulomb Z - PhysicalDiamagneticPotential.halfSquare (vector t) + zeeman t

theorem scalar_ae (Z t : ℝ) :
    ((scalar Z t).val : Space → ℝ) =ᵐ[volume] scalarPotential Z t := by
  have hs : ((scalar Z t).val : Space → ℝ) =ᵐ[volume]
      fun x => (coulomb Z - PhysicalDiamagneticPotential.halfSquare (vector t)).val x +
        (zeeman t).val x := AEEqFun.coeFn_add _ _
  have hsub : ((coulomb Z - PhysicalDiamagneticPotential.halfSquare (vector t)).val : Space → ℝ) =ᵐ[volume]
      fun x => (coulomb Z).val x - (PhysicalDiamagneticPotential.halfSquare (vector t)).val x :=
    AEEqFun.coeFn_sub _ _
  filter_upwards [hs, hsub, CounterexamplePotentials.coulomb_ae Z,
    PhysicalDiamagneticPotential.coeFn_halfSquare (vector t), vector_ae t, zeeman_ae t]
    with x hadd hsub hZ hsq ht hze
  rw [hadd, hsub, hZ, hsq, ht, hze]
  simp only [scalarPotential, vectorPotential, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

@[simp] theorem shifted_eq (Z t : ℝ) :
    PhysicalDiamagneticPotential.shifted (scalar Z t) (vector t) =
      (coulomb Z + zeeman t, vector t) := by
  unfold PhysicalDiamagneticPotential.shifted scalar
  congr 1
  abel

end PfHk.SpinfulCounterexamplePotentials
