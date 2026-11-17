import GptLean.ElectronicLocalizationPartition
import GptLean.Repair.Channel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Module

/-!
Countable mass, tested potential, current and IMS identities for the actual
symmetric spatial multipliers. Finite active sets are extracted from local
finiteness. Vanishing derivatives outside these sets are proved using
nonnegativity, including boundary points of the supports.
-/

noncomputable section

namespace GptLean.ElectronicLocalization

open Finset Filter MeasureTheory
open scoped Topology InnerProductSpace ComplexConjugate

variable {A E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem finite_partition_data (f : A → E → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (f a)))
    (hd : ∀ a, Differentiable ℝ (f a)) (hpos : ∀ a x, 0 ≤ f a x)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1) (x v : E) :
    ∃ s : Finset A,
      (∀ a ∉ s, f a x = 0 ∧ fderiv ℝ (f a) x v = 0) ∧
      (∑ a ∈ s, f a x ^ 2) = 1 ∧
      (∑ a ∈ s, f a x * fderiv ℝ (f a) x v) = 0 := by
  classical
  let s := (hloc.point_finite x).toFinset
  have hz : ∀ a ∉ s, f a x = 0 := by
    intro a ha
    by_contra h
    exact ha ((hloc.point_finite x).mem_toFinset.mpr h)
  have hdz : ∀ a ∉ s, fderiv ℝ (f a) x v = 0 := by
    intro a ha
    rw [fderiv_eq_zero_of_nonneg (hpos a) (hz a ha)]
    rfl
  refine ⟨s, fun a ha => ⟨hz a ha, hdz a ha⟩, ?_, ?_⟩
  · exact (hasSum_sum_of_ne_finset_zero (fun a ha => by simp [hz a ha])).unique (hpart x)
  · exact (hasSum_sum_of_ne_finset_zero (fun a ha => by simp [hz a ha])).unique
      (square_partition_connection f hloc hd hpart x v)

def localizedValue (f : A → E → ℝ) (ψ : E → H) (a : A) (x : E) : H :=
  (f a x : ℂ) • ψ x

def localizedDerivative (f : A → E → ℝ) (u ψ : E → H)
    (v : E) (a : A) (x : E) : H :=
  (f a x : ℂ) • u x - Complex.I • (fderiv ℝ (f a) x v : ℂ) • ψ x

/-- The localized derivative is the derivative of the actual product at
every differentiability point, also on the multiplier's zero set. -/
theorem localizedValue_fderiv (f : A → E → ℝ) (ψ : E → H) (a : A) (x v : E)
    (hf : DifferentiableAt ℝ (f a) x) (hψ : DifferentiableAt ℝ ψ x) :
    fderiv ℝ (localizedValue f ψ a) x v =
      (f a x : ℂ) • fderiv ℝ ψ x v + (fderiv ℝ (f a) x v : ℂ) • ψ x := by
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt
  have hp := hc.smul hψ.hasFDerivAt
  exact congrArg (fun L : E →L[ℝ] H => L v) hp.fderiv

theorem localizedDerivative_eq_covariant (f : A → E → ℝ) (ψ : E → H)
    (K : E → H →ₗ[ℂ] H) (a : A) (x v : E)
    (hf : DifferentiableAt ℝ (f a) x) (hψ : DifferentiableAt ℝ ψ x) :
    -Complex.I • fderiv ℝ (localizedValue f ψ a) x v - K x (localizedValue f ψ a x) =
      localizedDerivative f (fun y => -Complex.I • fderiv ℝ ψ y v - K y (ψ y)) ψ v a x := by
  rw [localizedValue_fderiv f ψ a x v hf hψ]
  simp only [localizedValue, localizedDerivative, smul_add, smul_sub, map_smul,
    neg_smul, smul_smul]
  module

theorem real_scalar_norm_sq (r : ℝ) (ψ : H) : ‖(r : ℂ) • ψ‖ ^ 2 = r ^ 2 * ‖ψ‖ ^ 2 := by
  simp [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- The current created by differentiating any real scalar multiplier is
purely imaginary before taking the real part. -/
theorem real_scalar_current (r dr : ℝ) (u ψ : H) :
    (inner ℂ ((r : ℂ) • ψ)
      ((r : ℂ) • u - Complex.I • (dr : ℂ) • ψ)).re = r ^ 2 * (inner ℂ ψ u).re := by
  simp only [inner_sub_right, inner_smul_left, inner_smul_right,
    inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem localization_mass_hasSum (f : A → E → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1) (ψ : E → H) (x : E) :
    HasSum (fun a => ‖localizedValue f ψ a x‖ ^ 2) (‖ψ x‖ ^ 2) := by
  simpa only [localizedValue, real_scalar_norm_sq, one_mul] using
    (hpart x).mul_right (‖ψ x‖ ^ 2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Every scalar multiplication potential is preserved pointwise. -/
theorem localization_potential_hasSum (f : A → E → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (ψ : E → H) (W : E → ℝ) (x : E) :
    HasSum (fun a => W x * ‖localizedValue f ψ a x‖ ^ 2) (W x * ‖ψ x‖ ^ 2) :=
  (localization_mass_hasSum f hpart ψ x).mul_left (W x)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Fibre quadratic observables, including a radiation form once its form
map is supplied, are preserved by the same real scalar multipliers. -/
theorem localization_fiber_form_hasSum (f : A → E → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (ψ : E → H) (K : E → H →ₗ[ℂ] H) (x : E) :
    HasSum (fun a => ‖K x (localizedValue f ψ a x)‖ ^ 2) (‖K x (ψ x)‖ ^ 2) := by
  simpa only [localizedValue, map_smul, real_scalar_norm_sq, one_mul] using
    (hpart x).mul_right (‖K x (ψ x)‖ ^ 2)

theorem localization_current_hasSum (f : A → E → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (u ψ : E → H) (x v : E) :
    HasSum (fun a => (inner ℂ (localizedValue f ψ a x)
      (localizedDerivative f u ψ v a x)).re) (inner ℂ (ψ x) (u x)).re := by
  simpa only [localizedValue, localizedDerivative, real_scalar_current, one_mul] using
    (hpart x).mul_right (inner ℂ (ψ x) (u x)).re

/-- Exact countable covariant IMS identity, with all series proved summable
from a common finite active set. -/
theorem localization_ims_hasSum (f : A → E → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (f a)))
    (hd : ∀ a, Differentiable ℝ (f a)) (hpos : ∀ a x, 0 ≤ f a x)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (u ψ : E → H) (x v : E) :
    HasSum (fun a => ‖localizedDerivative f u ψ v a x‖ ^ 2)
      (‖u x‖ ^ 2 + (∑' a, fderiv ℝ (f a) x v ^ 2) * ‖ψ x‖ ^ 2) := by
  classical
  obtain ⟨s, hz, hs, hc⟩ := finite_partition_data f hloc hd hpos hpart x v
  have hk : ∑ a : s, ‖(f a x : ℂ)‖ ^ 2 = 1 := by
    have hs' : (∑ a : s, f a x ^ 2) = 1 :=
      (Finset.sum_coe_sort s (fun a : A => f a x ^ 2)).trans hs
    simpa [Real.norm_eq_abs, sq_abs] using hs'
  have hconn : ∑ a : s, conj (f a x : ℂ) * (fderiv ℝ (f a) x v : ℂ) =
      Complex.I * (0 : ℝ) := by
    simp only [Complex.conj_ofReal, Complex.ofReal_zero, mul_zero]
    norm_cast
    exact (Finset.sum_coe_sort s
      (fun a : A => f a x * fderiv ℝ (f a) x v)).trans hc
  have hfinite := GptLean.Repair.channel_energy_scalar
    (fun a : s => (f a x : ℂ)) (fun a : s => (fderiv ℝ (f a) x v : ℂ))
    0 hk hconn (u x) (ψ x)
  have hderiv : HasSum (fun a => fderiv ℝ (f a) x v ^ 2)
      (∑ a ∈ s, fderiv ℝ (f a) x v ^ 2) :=
    hasSum_sum_of_ne_finset_zero fun a ha => by simp [(hz a ha).2]
  have hsum : (∑ a ∈ s, ‖localizedDerivative f u ψ v a x‖ ^ 2) =
      ‖u x‖ ^ 2 + (∑' a, fderiv ℝ (f a) x v ^ 2) * ‖ψ x‖ ^ 2 := by
    have hfinite' : (∑ a : s, ‖localizedDerivative f u ψ v a x‖ ^ 2) =
        ‖u x‖ ^ 2 + (∑ a : s, fderiv ℝ (f a) x v ^ 2) * ‖ψ x‖ ^ 2 := by
      simpa [localizedDerivative, Real.norm_eq_abs, sq_abs] using hfinite
    rw [Finset.sum_coe_sort s (fun a : A => ‖localizedDerivative f u ψ v a x‖ ^ 2),
      Finset.sum_coe_sort s (fun a : A => fderiv ℝ (f a) x v ^ 2)] at hfinite'
    simpa only [hderiv.tsum_eq] using hfinite'
  rw [← hsum]
  exact hasSum_sum_of_ne_finset_zero fun a ha => by
    simp [localizedDerivative, (hz a ha).1, (hz a ha).2]

variable {N : ℕ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- In particular, taking the permutation character to be the sign shows
that localization stays inside the antisymmetric electronic space. -/
theorem symmetricMultiplier_preserves_character (η : A → E → ℝ)
    (ψ : (Fin N → E) → H) (χ : Equiv.Perm (Fin N) → ℂ)
    (hψ : ∀ (X : Fin N → E) (π : Equiv.Perm (Fin N)), ψ (X ∘ π) = χ π • ψ X)
    (α : Fin N → A) (X : Fin N → E) (π : Equiv.Perm (Fin N)) :
    localizedValue (symmetricMultiplier η) ψ α (X ∘ π) =
      χ π • localizedValue (symmetricMultiplier η) ψ α X := by
  simp only [localizedValue, symmetricMultiplier_perm, hψ, smul_smul, mul_comm]

/-- The IMS theorem is instantiated with the constructed symmetric RMS
partition, so its normalization and connection are not residual inputs. -/
theorem symmetric_localization_ims (η : A → E → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (η a)))
    (hd : ∀ a, Differentiable ℝ (η a)) (hpos : ∀ a x, 0 ≤ η a x)
    (hpart : ∀ x, HasSum (fun a => η a x ^ 2) 1)
    (u ψ : (Fin N → E) → H) (X V : Fin N → E) :
    HasSum (fun α : Fin N → A =>
      ‖localizedDerivative (symmetricMultiplier η) u ψ V α X‖ ^ 2)
      (‖u X‖ ^ 2 + (∑' α : Fin N → A,
        fderiv ℝ (symmetricMultiplier η α) X V ^ 2) * ‖ψ X‖ ^ 2) :=
  localization_ims_hasSum _ (symmetricMultiplier_locallyFinite η hloc)
    (symmetricMultiplier_differentiable η hd hpos)
    (symmetricMultiplier_nonneg η)
    (symmetricMultiplier_hasSum_sq η hloc hpart) u ψ X V

section Integration

variable [Countable A] [MeasurableSpace E] {μ : Measure E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem hasSum_integral_nonnegative_countable {F : A → E → ℝ} {G : E → ℝ}
    (hF : ∀ a, AEStronglyMeasurable (F a) μ)
    (hpos : ∀ a, ∀ᵐ x ∂μ, 0 ≤ F a x)
    (hs : ∀ᵐ x ∂μ, HasSum (fun a => F a x) (G x))
    (hG : Integrable G μ) :
    HasSum (fun a => ∫ x, F a x ∂μ) (∫ x, G x ∂μ) := by
  apply hasSum_integral_of_dominated_convergence F hF
  · intro a
    filter_upwards [hpos a] with x hx
    rw [Real.norm_of_nonneg hx]
  · exact hs.mono fun _ h => h.summable
  · exact hG.congr (hs.mono fun _ h => h.tsum_eq.symm)
  · exact hs

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem integrated_localization_mass (f : A → E → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) μ)
    (ψ : E → H) (hψ : AEStronglyMeasurable ψ μ)
    (hint : Integrable (fun x => ‖ψ x‖ ^ 2) μ) :
    HasSum (fun a => ∫ x, ‖localizedValue f ψ a x‖ ^ 2 ∂μ)
      (∫ x, ‖ψ x‖ ^ 2 ∂μ) := by
  apply hasSum_integral_nonnegative_countable
  · intro a
    exact (((Complex.continuous_ofReal.comp_aestronglyMeasurable (hf a)).smul hψ).norm).pow 2
  · exact fun _ => Filter.Eventually.of_forall fun _ => sq_nonneg _
  · exact Filter.Eventually.of_forall (localization_mass_hasSum f hpart ψ)
  · exact hint

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem integrated_localization_nonnegative_potential (f : A → E → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) μ)
    (ψ : E → H) (hψ : AEStronglyMeasurable ψ μ)
    (W : E → ℝ) (hW : AEStronglyMeasurable W μ) (hWpos : ∀ᵐ x ∂μ, 0 ≤ W x)
    (hint : Integrable (fun x => W x * ‖ψ x‖ ^ 2) μ) :
    HasSum (fun a => ∫ x, W x * ‖localizedValue f ψ a x‖ ^ 2 ∂μ)
      (∫ x, W x * ‖ψ x‖ ^ 2 ∂μ) := by
  apply hasSum_integral_nonnegative_countable
  · intro a
    exact hW.mul ((((Complex.continuous_ofReal.comp_aestronglyMeasurable (hf a)).smul hψ).norm).pow 2)
  · intro a
    exact hWpos.mono fun x hx => mul_nonneg hx (sq_nonneg _)
  · exact Filter.Eventually.of_forall (localization_potential_hasSum f hpart ψ W)
  · exact hint

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Signed multiplication potentials are preserved whenever their source
expectation is absolutely integrable. -/
theorem integrated_localization_potential (f : A → E → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) μ)
    (ψ : E → H) (W : E → ℝ)
    (hint : Integrable (fun x => W x * ‖ψ x‖ ^ 2) μ) :
    HasSum (fun a => ∫ x, W x * ‖localizedValue f ψ a x‖ ^ 2 ∂μ)
      (∫ x, W x * ‖ψ x‖ ^ 2 ∂μ) := by
  have heq (a : A) (x : E) : W x * ‖localizedValue f ψ a x‖ ^ 2 =
      f a x ^ 2 * (W x * ‖ψ x‖ ^ 2) := by
    rw [localizedValue, real_scalar_norm_sq]
    ring
  let bound : A → E → ℝ := fun a x => f a x ^ 2 * ‖W x * ‖ψ x‖ ^ 2‖
  have hb : ∀ x, HasSum (fun a => bound a x) ‖W x * ‖ψ x‖ ^ 2‖ := fun x => by
    simpa only [bound, one_mul] using (hpart x).mul_right ‖W x * ‖ψ x‖ ^ 2‖
  apply hasSum_integral_of_dominated_convergence bound
  · intro a
    apply (((hf a).pow 2).mul hint.aestronglyMeasurable).congr
    exact Filter.Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, Pi.pow_apply, heq]
  · intro a
    filter_upwards with x
    simp only [heq, norm_mul, Real.norm_of_nonneg (sq_nonneg _), bound, le_refl]
  · exact Filter.Eventually.of_forall fun x => (hb x).summable
  · exact hint.norm.congr (Filter.Eventually.of_forall fun x => (hb x).tsum_eq.symm)
  · exact Filter.Eventually.of_forall (localization_potential_hasSum f hpart ψ W)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The integrated fibre form uses the same scalar-localized vector and
requires only measurability and integrability of its source form map. -/
theorem integrated_localization_fiber_form (f : A → E → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) μ)
    (ψ : E → H) (K : E → H →ₗ[ℂ] H)
    (hK : AEStronglyMeasurable (fun x => K x (ψ x)) μ)
    (hint : Integrable (fun x => ‖K x (ψ x)‖ ^ 2) μ) :
    HasSum (fun a => ∫ x, ‖K x (localizedValue f ψ a x)‖ ^ 2 ∂μ)
      (∫ x, ‖K x (ψ x)‖ ^ 2 ∂μ) := by
  simpa only [localizedValue, map_smul] using
    integrated_localization_mass f hpart hf (fun x => K x (ψ x)) hK hint

/-- The current identity passes to the integral with absolute domination
by the source current, so no exchange of a nonintegrable series is used. -/
theorem integrated_localization_current (f : A → E → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) μ)
    (u ψ : E → H) (v : E)
    (hint : Integrable (fun x => (inner ℂ (ψ x) (u x)).re) μ) :
    HasSum (fun a => ∫ x, (inner ℂ (localizedValue f ψ a x)
      (localizedDerivative f u ψ v a x)).re ∂μ)
      (∫ x, (inner ℂ (ψ x) (u x)).re ∂μ) := by
  let bound : A → E → ℝ := fun a x => f a x ^ 2 * ‖(inner ℂ (ψ x) (u x)).re‖
  have hb : ∀ x, HasSum (fun a => bound a x) ‖(inner ℂ (ψ x) (u x)).re‖ := fun x => by
    simpa only [bound, one_mul] using (hpart x).mul_right ‖(inner ℂ (ψ x) (u x)).re‖
  apply hasSum_integral_of_dominated_convergence bound
  · intro a
    apply (((hf a).pow 2).mul hint.aestronglyMeasurable).congr
    exact Filter.Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, Pi.pow_apply, localizedValue, localizedDerivative,
        real_scalar_current]
  · intro a
    filter_upwards with x
    simp only [localizedValue, localizedDerivative, real_scalar_current, norm_mul,
      Real.norm_of_nonneg (sq_nonneg _), bound, le_refl]
  · exact Filter.Eventually.of_forall fun x => (hb x).summable
  · exact hint.norm.congr (Filter.Eventually.of_forall fun x => (hb x).tsum_eq.symm)
  · exact Filter.Eventually.of_forall fun x => localization_current_hasSum f hpart u ψ x v

/-- Integrating the proved pointwise IMS identity gives the countable
kinetic identity whenever its explicit source-plus-metric density is
integrable. A uniform bound from `symmetricMultiplier_total_metric_le`
supplies the corresponding physical majorant. -/
theorem integrated_localization_ims (f : A → E → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (f a)))
    (hd : ∀ a, Differentiable ℝ (f a)) (hpos : ∀ a x, 0 ≤ f a x)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) μ)
    (u ψ : E → H) (v : E)
    (hu : AEStronglyMeasurable u μ) (hψ : AEStronglyMeasurable ψ μ)
    (hdf : ∀ a, AEStronglyMeasurable (fun x => fderiv ℝ (f a) x v) μ)
    (hint : Integrable (fun x => ‖u x‖ ^ 2 +
      (∑' a, fderiv ℝ (f a) x v ^ 2) * ‖ψ x‖ ^ 2) μ) :
    HasSum (fun a => ∫ x, ‖localizedDerivative f u ψ v a x‖ ^ 2 ∂μ)
      (∫ x, ‖u x‖ ^ 2 + (∑' a, fderiv ℝ (f a) x v ^ 2) * ‖ψ x‖ ^ 2 ∂μ) := by
  apply hasSum_integral_nonnegative_countable
  · intro a
    exact (((Complex.continuous_ofReal.comp_aestronglyMeasurable (hf a)).smul hu).sub
      (((Complex.continuous_ofReal.comp_aestronglyMeasurable (hdf a)).smul hψ).const_smul
        Complex.I)).norm.pow 2
  · exact fun _ => Filter.Eventually.of_forall fun _ => sq_nonneg _
  · exact Filter.Eventually.of_forall fun x => localization_ims_hasSum f hloc hd hpos hpart u ψ x v
  · exact hint

end Integration

end GptLean.ElectronicLocalization
