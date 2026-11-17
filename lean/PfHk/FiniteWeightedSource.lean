import PfHk.WeightedNorm
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Finite perturbation sums with an actual almost-everywhere operator
identity. Integrability is derived from the component source estimates. -/

noncomputable section
namespace PfHk.FiniteWeightedSource

open MeasureTheory

set_option Elab.async false
set_option maxHeartbeats 20000

variable {J H : Type*} [NormedAddCommGroup H]

theorem norm_sum_sq (S : Finset J) (v : J → H) :
    ‖∑ j ∈ S, v j‖ ^ 2 ≤ (S.card : ℝ) * ∑ j ∈ S, ‖v j‖ ^ 2 := by
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S v) 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun j => ‖v j‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  exact hnorm.trans hcs

theorem norm_smul_sum_sq [NormedSpace ℂ H] (S : Finset J) (c : J → ℂ) (v : J → H)
    (hc : ∀ j ∈ S, ‖c j‖ ≤ 1) :
    ‖∑ j ∈ S, c j • v j‖ ^ 2 ≤ (S.card : ℝ) * ∑ j ∈ S, ‖v j‖ ^ 2 := by
  apply (norm_sum_sq S (fun j => c j • v j)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j hj
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (hc j hj) (norm_nonneg _)).trans_eq (one_mul _)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem source_sum_bound [NormedSpace ℂ H]
    (S : Finset J) (c : J → ℂ) (f : J → X → H) (g : X → H) (w : X → ℝ)
    (hc : ∀ j ∈ S, ‖c j‖ ≤ 1)
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hoperator : g =ᵐ[μ] fun x => ∑ j ∈ S, c j • f j x)
    (hmeas : AEStronglyMeasurable (fun x => w x * ‖g x‖ ^ 2) μ)
    (hint : ∀ j ∈ S, Integrable (fun x => w x * ‖f j x‖ ^ 2) μ) :
    Integrable (fun x => w x * ‖g x‖ ^ 2) μ ∧
      (∫ x, w x * ‖g x‖ ^ 2 ∂μ) ≤
        (S.card : ℝ) * ∑ j ∈ S, ∫ x, w x * ‖f j x‖ ^ 2 ∂μ := by
  let majorant := fun x => (S.card : ℝ) * ∑ j ∈ S, w x * ‖f j x‖ ^ 2
  have hm : Integrable majorant μ := (integrable_finsetSum S hint).const_mul _
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ w x * ‖g x‖ ^ 2 :=
    hw.mono fun x hx => mul_nonneg hx (sq_nonneg _)
  have hbound : ∀ᵐ x ∂μ, w x * ‖g x‖ ^ 2 ≤ majorant x := by
    filter_upwards [hw, hoperator] with x hx heq
    rw [heq]
    have h := mul_le_mul_of_nonneg_left (norm_smul_sum_sq S c (fun j => f j x) hc) hx
    apply h.trans_eq
    dsimp [majorant]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hg : Integrable (fun x => w x * ‖g x‖ ^ 2) μ := hm.mono' hmeas (by
    filter_upwards [hnonneg, hbound] with x h0 hle
    simpa only [Real.norm_of_nonneg h0] using hle)
  refine ⟨hg, (integral_mono_ae hg hm hbound).trans_eq ?_⟩
  dsimp [majorant]
  rw [integral_const_mul, integral_finsetSum S hint]

end PfHk.FiniteWeightedSource
