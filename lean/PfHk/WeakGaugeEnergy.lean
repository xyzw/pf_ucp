import GptLean.AppendixAGaugeForm
import GptLean.PhysicalGroundState
import PfHk.PhysicalDiamagneticPotential

/-! The diamagnetically shifted dual pairing equals the ordinary external
energy used in the weak-gauge calculation. -/

noncomputable section
namespace PfHk.WeakGaugeEnergy

open MeasureTheory GptLean GptLean.PhysicalPairSpace GptLean.PhysicalPairDuality
  GptLean.TransformationsGauge GptLean.TransformationsPotentials
  PfHk.PhysicalDiamagneticPotential
open scoped ENNReal RealInnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

attribute [local irreducible] PfHk.PhysicalDiamagneticPotential.halfSquare

theorem halfSquare_pairing_add_current (A : VectorPotential) (d : Pair) :
    pairing (halfSquare A) d.1 + pairing A d.2 =
      vectorEnergy (fun a x => A.val x a) d := by
  have hs : Integrable (fun x => (halfSquare A).val x * densityL1 d x) := by
    change Integrable (fun x => (halfSquare A).val x * fst d.1 x)
    simpa only [Real.inner_apply] using
      PhysicalGroundState.integrable_pairing (halfSquare A) d.1
  have hv : Integrable (fun x => inner ℝ (A.val x) (currentL1 d x)) := by
    change Integrable (fun x => inner ℝ (A.val x) (fst d.2 x))
    exact PhysicalGroundState.integrable_pairing A d.2
  rw [pairing_density, pairing_current]
  calc
    _ = ∫ x, (halfSquare A).val x * densityL1 d x +
        inner ℝ (A.val x) (currentL1 d x) := by
      exact (integral_add hs hv).symm
    _ = ∫ x, ∑ a : Fin 3, (A.val x a * currentL1 d x a +
        (1 / 2 : ℝ) * A.val x a ^ 2 * densityL1 d x) := by
      apply integral_congr_ae
      filter_upwards [coeFn_halfSquare A] with x hx
      have algebra (u j : Vector) (r : ℝ) :
          (1 / 2 : ℝ) * ‖u‖ ^ 2 * r + inner ℝ u j =
            ∑ a : Fin 3, (u a * j a + (1 / 2 : ℝ) * u a ^ 2 * r) := by
        simp only [EuclideanSpace.norm_sq_eq, PiLp.inner_apply,
          Real.norm_eq_abs, sq_abs, Real.inner_apply]
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        ring
      exact (congrArg (fun r : ℝ => r * densityL1 d x +
        inner ℝ (A.val x) (currentL1 d x)) hx).trans
          (algebra (A.val x) (currentL1 d x) (densityL1 d x))
    _ = vectorEnergy (fun a x => A.val x a) d := by
      exact integral_finsetSum Finset.univ (fun a _ =>
        vectorEnergy_integrable (fun a x => A.val x a)
          (vectorPotential_component_in_sum A) d a)

theorem shifted_pairEnergy (v : ScalarPotential) (A : VectorPotential)
    (E : ℝ) (d : Pair) :
    E + pairPotential (shifted v A) d =
      externalEnergy v (fun a x => A.val x a) E d := by
  change E + (pairing (v + halfSquare A) d.1 + pairing A d.2) = _
  rw [pairing_add]
  change E + ((pairing v d.1 + pairing (halfSquare A) d.1) + pairing A d.2) = _
  have h := halfSquare_pairing_add_current A d
  unfold externalEnergy
  linarith

theorem externalEnergy_congr_vector (v : ScalarPotential)
    (A A' : Fin 3 → Position → ℝ) (E : ℝ) (d : Pair)
    (hA : ∀ a, A a =ᵐ[volume] A' a) :
    externalEnergy v A E d = externalEnergy v A' E d := by
  apply congrArg (fun r : ℝ => E + pairing v d.1 + r)
  apply Finset.sum_congr rfl
  intro a _
  apply integral_congr_ae
  filter_upwards [hA a] with x hx
  rw [hx]

theorem gauge_shifted_pairEnergy (G : WeakSpatialGauge)
    (v : ScalarPotential) (A A' : VectorPotential) (E : ℝ) (d : Pair)
    (hA : (A'.val : Position → Vector) =ᵐ[volume]
      fun x => A.val x - G.gradientVector x) :
    (E + G.energyShift d) + pairPotential (shifted v A') (G.shiftPair d) =
      E + pairPotential (shifted v A) d := by
  calc
    _ = externalEnergy v (fun a x => A'.val x a)
        (E + G.energyShift d) (G.shiftPair d) := shifted_pairEnergy v A' _ _
    _ = externalEnergy v (fun a x => A.val x a - G.gradient a x)
        (E + G.energyShift d) (G.shiftPair d) := by
      apply externalEnergy_congr_vector
      intro a
      filter_upwards [hA] with x hx
      rw [hx, PiLp.sub_apply, G.gradientVector_apply]
    _ = externalEnergy v (fun a x => A.val x a) E d :=
      G.externalEnergy_shift v (fun a x => A.val x a)
        (vectorPotential_component_in_sum A) E d
    _ = _ := (shifted_pairEnergy v A E d).symm

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

end PfHk.WeakGaugeEnergy
