import PfHk.WeightedNorm

/-! Weighted kinetic energies under addition of a finite family of
external multiplication terms. -/

noncomputable section
namespace PfHk.WeightedCovariantEnergy

open MeasureTheory

set_option Elab.async false
set_option maxHeartbeats 20000

variable {X H J : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  [Fintype J] {μ : Measure X}

theorem sum_add_integrable_bound (w : X → ℝ) (d a p : J → X → H)
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (heq : ∀ j, p j =ᵐ[μ] fun x => d j x + a j x)
    (hmeas : AEStronglyMeasurable (fun x => w x * ∑ j, ‖p j x‖ ^ 2) μ)
    (hd : Integrable (fun x => w x * ∑ j, ‖d j x‖ ^ 2) μ)
    (ha : ∀ j, Integrable (fun x => w x * ‖a j x‖ ^ 2) μ) :
    Integrable (fun x => w x * ∑ j, ‖p j x‖ ^ 2) μ ∧
      (∫ x, w x * ∑ j, ‖p j x‖ ^ 2 ∂μ) ≤
        2 * (∫ x, w x * ∑ j, ‖d j x‖ ^ 2 ∂μ) +
          2 * ∑ j, ∫ x, w x * ‖a j x‖ ^ 2 ∂μ := by
  classical
  have haSum : Integrable (fun x => ∑ j, w x * ‖a j x‖ ^ 2) μ :=
    integrable_finsetSum _ fun j _ => ha j
  have hmajor : Integrable (fun x =>
      2 * (w x * ∑ j, ‖d j x‖ ^ 2) + 2 * ∑ j, w x * ‖a j x‖ ^ 2) μ :=
    (hd.const_mul 2).add (haSum.const_mul 2)
  have hbound : ∀ᵐ x ∂μ, w x * ∑ j, ‖p j x‖ ^ 2 ≤
      2 * (w x * ∑ j, ‖d j x‖ ^ 2) + 2 * ∑ j, w x * ‖a j x‖ ^ 2 := by
    filter_upwards [hw, Filter.eventually_all.mpr heq] with x hx hpx
    have hsum : (∑ j, ‖p j x‖ ^ 2) ≤ ∑ j, (2 * ‖d j x‖ ^ 2 + 2 * ‖a j x‖ ^ 2) :=
      Finset.sum_le_sum fun j _ => by
        rw [hpx j]
        exact WeightedNorm.add_sq_bound _ _
    apply (mul_le_mul_of_nonneg_left hsum hx).trans_eq
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
    ring
  have hi : Integrable (fun x => w x * ∑ j, ‖p j x‖ ^ 2) μ :=
    hmajor.mono' hmeas (by
      filter_upwards [hw, hbound] with x hx hb
      simpa only [Real.norm_of_nonneg
        (mul_nonneg hx (Finset.sum_nonneg fun j _ => sq_nonneg _))] using hb)
  refine ⟨hi, (integral_mono_ae hi hmajor hbound).trans_eq ?_⟩
  rw [integral_add (hd.const_mul 2) (haSum.const_mul 2), integral_const_mul,
    integral_const_mul, integral_finsetSum _ (fun j _ => ha j)]

end PfHk.WeightedCovariantEnergy
