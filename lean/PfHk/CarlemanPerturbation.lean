import PfHk.DyadicFractional
import PfHk.WeightedNorm

/-! Transfer of weighted source estimates to scalar perturbations. The
source quantities below are actual squared-norm integrals. The unperturbed
Carleman estimate is an explicit theorem input, and the norm-square triangle
and absorption steps are proved for the operator images themselves. -/

noncomputable section
namespace PfHk.CarlemanPerturbation

open MeasureTheory

set_option maxHeartbeats 80000
set_option Elab.async false

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] {μ : Measure X}

def source (w : X → ℝ) (f : X → H) : ℝ := ∫ x, w x * ‖f x‖ ^ 2 ∂μ

theorem source_nonneg {w : X → ℝ} (hw : ∀ᵐ x ∂μ, 0 ≤ w x) (f : X → H) :
    0 ≤ source (μ := μ) w f :=
  integral_nonneg_of_ae (hw.mono fun _ hx => mul_nonneg hx (sq_nonneg _))

/-- The comparison of two operator images is proved under their actual
pointwise perturbation identity. -/
theorem source_triangle {w : X → ℝ} {free perturbed error : X → H}
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hf : Integrable (fun x => w x * ‖free x‖ ^ 2) μ)
    (hp : Integrable (fun x => w x * ‖perturbed x‖ ^ 2) μ)
    (he : Integrable (fun x => w x * ‖error x‖ ^ 2) μ)
    (hoperator : free =ᵐ[μ] fun x => perturbed x - error x) :
    source (μ := μ) w free ≤ 2 * source (μ := μ) w perturbed +
      2 * source (μ := μ) w error := by
  exact (WeightedNorm.sub_integrable_bound hw hf.aestronglyMeasurable hp he hoperator).2

theorem source_absorption {w : X → ℝ} {free perturbed error : X → H}
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hf : Integrable (fun x => w x * ‖free x‖ ^ 2) μ)
    (hp : Integrable (fun x => w x * ‖perturbed x‖ ^ 2) μ)
    (he : Integrable (fun x => w x * ‖error x‖ ^ 2) μ)
    (hoperator : free =ᵐ[μ] fun x => perturbed x - error x)
    (hsmall : source (μ := μ) w error ≤ source (μ := μ) w free / 4) :
    source (μ := μ) w free ≤ 4 * source (μ := μ) w perturbed :=
  CarlemanAlgebra.perturbation_absorption (source_triangle hw hf hp he hoperator) hsmall

/-- The scalar multiplier estimate and its bounded remainder have decaying
parameter powers. A single threshold transfers the supplied unperturbed
Carleman integral to the perturbed operator image for every larger parameter. -/
theorem scalar_parameter_transfer (w density : ℝ → X → ℝ)
    (free perturbed error : X → H) {a A B C τbase : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hw : ∀ τ, τbase ≤ τ → ∀ᵐ x ∂μ, 0 ≤ w τ x)
    (hf : ∀ τ, τbase ≤ τ → Integrable (fun x => w τ x * ‖free x‖ ^ 2) μ)
    (hp : ∀ τ, τbase ≤ τ → Integrable (fun x => w τ x * ‖perturbed x‖ ^ 2) μ)
    (he : ∀ τ, τbase ≤ τ → Integrable (fun x => w τ x * ‖error x‖ ^ 2) μ)
    (hoperator : free =ᵐ[μ] fun x => perturbed x - error x)
    (hfree : ∀ τ, τbase ≤ τ → (∫ x, density τ x ∂μ) ≤ C * source (μ := μ) (w τ) free)
    (herror : ∀ τ, τbase ≤ τ → source (μ := μ) (w τ) error ≤
      (A * τ ^ (-a) + B * τ ^ (-3 : ℝ)) * source (μ := μ) (w τ) free) :
    ∃ τ₀ : ℝ, τbase ≤ τ₀ ∧ 1 ≤ τ₀ ∧ ∀ τ, τ₀ ≤ τ →
      source (μ := μ) (w τ) free ≤ 4 * source (μ := μ) (w τ) perturbed ∧
      (∫ x, density τ x ∂μ) ≤ (4 * C) * source (μ := μ) (w τ) perturbed := by
  obtain ⟨T, hT1, hT⟩ := CarlemanWeights.exists_parameter_small ha
    (by norm_num : (0 : ℝ) < 1 / 4) A B
  refine ⟨max τbase T, le_max_left _ _, hT1.trans (le_max_right _ _), ?_⟩
  intro τ hτ
  have hb := (le_max_left τbase T).trans hτ
  have ht := (le_max_right τbase T).trans hτ
  have hsmall : source (μ := μ) (w τ) error ≤ source (μ := μ) (w τ) free / 4 := by
    have hh := mul_le_mul_of_nonneg_right (hT τ ht).le (source_nonneg (hw τ hb) free)
    exact (herror τ hb).trans (hh.trans_eq (by ring))
  have hs := source_absorption (hw τ hb) (hf τ hb) (hp τ hb) (he τ hb) hoperator hsmall
  exact ⟨hs, CarlemanAlgebra.transfer_estimate hC (hfree τ hb) hs⟩

/-- The actual two annular sums give the scalar multiplier coefficient.
The radius bounds are the scalar ratios `rᵃ / β(-log r)`, not a physical
smallness hypothesis. -/
theorem scalar_dyadic_bound {J : Type*} (S : Finset J) (β R Qs Q₀ : J → ℝ)
    {τ s σs σ₀ Cs C₀ A B F E : ℝ}
    (hτ : 0 < τ) (hσs : 0 ≤ σs) (hσ₀ : 0 ≤ σ₀) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hβ : ∀ j ∈ S, 0 < β j) (hR : ∀ j ∈ S, 0 < R j)
    (hQs : ∀ j ∈ S, 0 ≤ Qs j) (hQ₀ : ∀ j ∈ S, 0 ≤ Q₀ j)
    (hratios : ∀ j ∈ S, R j ^ (4 - 2 * s) / β j ≤ σs)
    (hratio₀ : ∀ j ∈ S, R j ^ (4 : ℝ) / β j ≤ σ₀)
    (hs : (∑ j ∈ S, DyadicFractional.coefficient τ (β j) (R j) s * Qs j) ≤ Cs * F)
    (hzero : (∑ j ∈ S, DyadicFractional.coefficient τ (β j) (R j) 0 * Q₀ j) ≤ C₀ * F)
    (hmultiplier : E ≤ A * (∑ j ∈ S, R j ^ (2 : ℝ) * Qs j) +
      B * (∑ j ∈ S, R j ^ (2 : ℝ) * Q₀ j)) :
    E ≤ (A * σs * Cs * τ ^ (-(3 - 2 * s)) +
      B * σ₀ * C₀ * τ ^ (-3 : ℝ)) * F := by
  have hs' := DyadicFractional.multiplier_sum_bound S β R Qs hτ hσs hβ hR hQs hratios hs
  have hzero' := DyadicFractional.multiplier_sum_bound S β R Q₀ (s := 0)
    hτ hσ₀ hβ hR hQ₀ (by simpa using hratio₀) hzero
  have hh := hmultiplier.trans (add_le_add (mul_le_mul_of_nonneg_left hs' hA)
    (mul_le_mul_of_nonneg_left hzero' hB))
  exact hh.trans_eq (by norm_num; ring)

/-- The local Sobolev multiplier bounds for each localized vector combine
with a genuine square partition to bound the actual weighted error integral. -/
theorem partition_multiplier_bound {J : Type*} (S : Finset J)
    (η : J → X → ℝ) (a r : X → ℝ) (error : X → H) (R Qs Q₀ : J → ℝ)
    {K A B : ℝ} (hK : 0 ≤ K)
    (hpart : ∀ x, error x ≠ 0 → (∑ j ∈ S, η j x ^ 2) = 1)
    (hscale : ∀ j ∈ S, ∀ x, η j x ≠ 0 → r x ^ 2 ≤ K * R j ^ 2)
    (hmeas : AEStronglyMeasurable (fun x => a x ^ 2 * r x ^ 2 * ‖error x‖ ^ 2) μ)
    (hint : ∀ j ∈ S, Integrable (fun x => η j x ^ 2 * a x ^ 2 * ‖error x‖ ^ 2) μ)
    (hSobolev : ∀ j ∈ S,
      (∫ x, η j x ^ 2 * a x ^ 2 * ‖error x‖ ^ 2 ∂μ) ≤ A * Qs j + B * Q₀ j) :
    source (μ := μ) (fun x => a x ^ 2 * r x ^ 2) error ≤
      (K * A) * (∑ j ∈ S, R j ^ 2 * Qs j) +
      (K * B) * (∑ j ∈ S, R j ^ 2 * Q₀ j) := by
  have hb := DyadicFractional.partition_radius_integral_bound S η a r
    (fun x => ‖error x‖ ^ 2) R (fun x => sq_nonneg _) (by
      intro x hx
      apply hpart x
      intro hzero
      exact hx (by simp [hzero])) hscale hmeas hint
  apply hb.2.trans
  calc
    _ ≤ K * (∑ j ∈ S, R j ^ 2 * (A * Qs j + B * Q₀ j)) := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hSobolev j hj) (sq_nonneg _)
    _ = K * (A * (∑ j ∈ S, R j ^ 2 * Qs j) + B * (∑ j ∈ S, R j ^ 2 * Q₀ j)) := by
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by ring

/-- The local Sobolev multiplier bounds for each localized vector combine
with a square lower bound to bound the actual weighted error integral. -/
theorem partition_multiplier_bound_of_lower {J : Type*} (S : Finset J)
    (η : J → X → ℝ) (a r : X → ℝ) (error : X → H) (R Qs Q₀ : J → ℝ)
    {K m A B : ℝ} (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hpart : ∀ x, error x ≠ 0 → 1 ≤ m * (∑ j ∈ S, η j x ^ 2))
    (hscale : ∀ j ∈ S, ∀ x, η j x ≠ 0 → r x ^ 2 ≤ K * R j ^ 2)
    (hmeas : AEStronglyMeasurable (fun x => a x ^ 2 * r x ^ 2 * ‖error x‖ ^ 2) μ)
    (hint : ∀ j ∈ S, Integrable (fun x => η j x ^ 2 * a x ^ 2 * ‖error x‖ ^ 2) μ)
    (hSobolev : ∀ j ∈ S,
      (∫ x, η j x ^ 2 * a x ^ 2 * ‖error x‖ ^ 2 ∂μ) ≤ A * Qs j + B * Q₀ j) :
    source (μ := μ) (fun x => a x ^ 2 * r x ^ 2) error ≤
      (m * K * A) * (∑ j ∈ S, R j ^ 2 * Qs j) +
      (m * K * B) * (∑ j ∈ S, R j ^ 2 * Q₀ j) := by
  have hb := DyadicFractional.partition_radius_integral_bound_of_lower S η a r
    (fun x => ‖error x‖ ^ 2) R hm (fun x => sq_nonneg _) (by
      intro x hx
      apply hpart x
      intro hzero
      exact hx (by simp [hzero])) hscale hmeas hint
  apply hb.2.trans
  calc
    _ ≤ (m * K) * (∑ j ∈ S, R j ^ 2 * (A * Qs j + B * Q₀ j)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hm hK)
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hSobolev j hj) (sq_nonneg _)
    _ = (m * K) * (A * (∑ j ∈ S, R j ^ 2 * Qs j) + B * (∑ j ∈ S, R j ^ 2 * Q₀ j)) := by
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by ring

end PfHk.CarlemanPerturbation
