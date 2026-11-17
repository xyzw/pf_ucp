import GptLean.Repair.General
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Hilbert-basis coordinates of a unit-valued tensor lift give the scalar
repair multipliers. Their normalization, connection and metric series are
derived from Parseval rather than supplied as separate channel hypotheses.

The vector `z` is the value of the lift and `dz` one of its weak derivatives.
The results are pointwise and can therefore be used on their common
almost-everywhere domain. Measurability of the physical multiplication
channel and transport of the Pauli–Fierz form domain remain separate tasks.
-/

namespace GptLean.Repair

open scoped ComplexConjugate ENNReal

variable {ι V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Coordinates of the actual Hilbert-valued lift. -/
noncomputable def coordinate (b : HilbertBasis ι ℂ V) (z : V) (a : ι) : ℂ :=
  inner ℂ (b a) z

/-- Each scalar multiplier is bounded by the Hilbert-valued lift norm. -/
theorem coordinate_norm_le (b : HilbertBasis ι ℂ V) (z : V) (a : ι) :
    ‖coordinate b z a‖ ≤ ‖z‖ := by
  simpa only [coordinate, b.orthonormal.norm_eq_one, one_mul] using
    norm_inner_le_norm (b a) z

theorem coordinate_aestronglyMeasurable {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} (b : HilbertBasis ι ℂ V) {z : X → V}
    (hz : MeasureTheory.AEStronglyMeasurable z μ) (a : ι) :
    MeasureTheory.AEStronglyMeasurable (fun x => coordinate b (z x) a) μ := by
  exact (innerSL ℂ (b a)).continuous.comp_aestronglyMeasurable hz

/-- Coordinate projection transports the vector weak derivative identity.
This applies directly to the weak identity for the constructed tensor lift. -/
theorem coordinate_weak_derivative [CompleteSpace V]
    {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (b : HilbertBasis ι ℂ V) (a : ι) {z dz : X → V} {φ φ' : X → ℝ}
    (hd : MeasureTheory.Integrable (fun x => φ x • dz x) μ)
    (hz : MeasureTheory.Integrable (fun x => φ' x • z x) μ)
    (hweak : (∫ x, φ x • dz x ∂μ) = -(∫ x, φ' x • z x ∂μ)) :
    (∫ x, φ x • coordinate b (dz x) a ∂μ) =
      -(∫ x, φ' x • coordinate b (z x) a ∂μ) := by
  let L : V →L[ℝ] ℂ := (innerSL ℂ (b a)).restrictScalars ℝ
  have h := congrArg L hweak
  rw [← L.integral_comp_comm hd, map_neg, ← L.integral_comp_comm hz] at h
  change (∫ x, φ x • L (dz x) ∂μ) = -(∫ x, φ' x • L (z x) ∂μ)
  simpa only [map_smul] using h

theorem coordinate_inner_hasSum (b : HilbertBasis ι ℂ V) (z w : V) :
    HasSum (fun a => conj (coordinate b z a) * coordinate b w a) (inner ℂ z w) := by
  simpa only [coordinate, inner_conj_symm] using b.hasSum_inner_mul_inner z w

theorem coordinate_norm_sq_hasSum (b : HilbertBasis ι ℂ V) (z : V) :
    HasSum (fun a => ‖coordinate b z a‖ ^ 2) (‖z‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (b.repr z)
  simpa [Real.rpow_two, b.repr_apply_apply, coordinate] using h

theorem coordinate_normalization (b : HilbertBasis ι ℂ V) {z : V} (hz : ‖z‖ = 1) :
    HasSum (fun a => ‖coordinate b z a‖ ^ 2) 1 := by
  simpa only [hz, one_pow] using coordinate_norm_sq_hasSum b z

theorem coordinate_connection (b : HilbertBasis ι ℂ V) {z dz : V} {s : ℝ}
    (hconn : inner ℂ z dz = Complex.I * s) :
    HasSum (fun a => conj (coordinate b z a) * coordinate b dz a) (Complex.I * s) := by
  rw [← hconn]
  exact coordinate_inner_hasSum b z dz

/-- Parseval survives tensoring the scalar coordinates with fibre vectors. -/
theorem coordinate_smul_inner_hasSum (b : HilbertBasis ι ℂ V) (z w : V) (u v : H) :
    HasSum (fun a => inner ℂ (coordinate b z a • u) (coordinate b w a • v))
      (inner ℂ z w * inner ℂ u v) := by
  have he : (fun a => inner ℂ (coordinate b z a • u) (coordinate b w a • v)) =
      (fun a => (conj (coordinate b z a) * coordinate b w a) * inner ℂ u v) := by
    funext a
    simp only [inner_smul_left, inner_smul_right]
    ring
  rw [he]
  exact (coordinate_inner_hasSum b z w).mul_right (inner ℂ u v)

theorem coordinate_smul_norm_sq_hasSum (b : HilbertBasis ι ℂ V) (z : V) (u : H) :
    HasSum (fun a => ‖coordinate b z a • u‖ ^ 2) (‖z‖ ^ 2 * ‖u‖ ^ 2) := by
  simpa only [norm_smul, mul_pow] using (coordinate_norm_sq_hasSum b z).mul_right (‖u‖ ^ 2)

/-- The countable current identity from one unit vector and its connection. -/
theorem coordinate_channel_current (b : HilbertBasis ι ℂ V) {z dz : V} {s : ℝ}
    (hz : ‖z‖ = 1) (hconn : inner ℂ z dz = Complex.I * s) (u ψ : H) :
    HasSum (fun a => inner ℂ (coordinate b z a • ψ)
      (coordinate b z a • u - Complex.I • coordinate b dz a • ψ))
      (inner ℂ ψ u + (s : ℂ) * ‖ψ‖ ^ 2) := by
  have hn : HasSum (fun a => inner ℂ (coordinate b z a • ψ)
      (coordinate b z a • u)) (inner ℂ ψ u) := by
    simpa [inner_self_eq_norm_sq_to_K, hz]
      using coordinate_smul_inner_hasSum b z z ψ u
  have hc : HasSum (fun a => inner ℂ (coordinate b z a • ψ)
      (coordinate b dz a • ψ)) (Complex.I * ((s : ℂ) * ‖ψ‖ ^ 2)) := by
    simpa [hconn, inner_self_eq_norm_sq_to_K, mul_assoc]
      using coordinate_smul_inner_hasSum b z dz ψ ψ
  have hs := hn.sub (hc.mul_left Complex.I)
  simpa only [inner_sub_right, inner_smul_right, ← mul_assoc,
    Complex.I_mul_I, neg_one_mul, neg_mul, sub_neg_eq_add, one_mul] using hs

/-- The kinetic identity with the full Hilbert derivative norm as remainder. -/
theorem coordinate_channel_energy (b : HilbertBasis ι ℂ V) {z dz : V} {s : ℝ}
    (hz : ‖z‖ = 1) (hconn : inner ℂ z dz = Complex.I * s) (u ψ : H) :
    HasSum (fun a => ‖coordinate b z a • u - Complex.I • coordinate b dz a • ψ‖ ^ 2)
      (‖u‖ ^ 2 + 2 * s * (inner ℂ u ψ).re + ‖dz‖ ^ 2 * ‖ψ‖ ^ 2) := by
  have hn : HasSum (fun a => ‖coordinate b z a • u‖ ^ 2) (‖u‖ ^ 2) := by
    simpa only [hz, one_pow, one_mul] using coordinate_smul_norm_sq_hasSum b z u
  have hc : HasSum (fun a => inner ℂ (coordinate b z a • u)
      (coordinate b dz a • ψ)) (Complex.I * inner ℂ u ((s : ℂ) • ψ)) := by
    simpa only [hconn, inner_smul_right, mul_assoc]
      using coordinate_smul_inner_hasSum b z dz u ψ
  have he := countable_channel_energy
    (fun a => coordinate b z a • (LinearMap.id : H →ₗ[ℂ] H))
    (fun a => coordinate b dz a • (LinearMap.id : H →ₗ[ℂ] H))
    ((s : ℂ) • (LinearMap.id : H →ₗ[ℂ] H)) u ψ (‖dz‖ ^ 2 * ‖ψ‖ ^ 2)
    hn hc (coordinate_smul_norm_sq_hasSum b dz ψ)
  simpa only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_right,
    Complex.re_ofReal_mul, mul_assoc] using he

/-- Any commuting bounded observable is preserved by the same coordinates. -/
theorem coordinate_channel_preserves (b : HilbertBasis ι ℂ V) {z : V}
    (hz : ‖z‖ = 1) (W : H →ₗ[ℂ] H) (ψ : H) :
    HasSum (fun a => inner ℂ (coordinate b z a • ψ) (W (coordinate b z a • ψ)))
      (inner ℂ ψ (W ψ)) := by
  simpa [inner_self_eq_norm_sq_to_K, hz] using
    coordinate_smul_inner_hasSum b z z ψ (W ψ)

/-- The real current shift, with the unnormalized density factor retained. -/
theorem coordinate_channel_current_real (b : HilbertBasis ι ℂ V) {z dz : V} {s : ℝ}
    (hz : ‖z‖ = 1) (hconn : inner ℂ z dz = Complex.I * s) (u ψ : H) :
    HasSum (fun a => (inner ℂ (coordinate b z a • ψ)
      (coordinate b z a • u - Complex.I • coordinate b dz a • ψ)).re)
      ((inner ℂ ψ u).re + s * ‖ψ‖ ^ 2) := by
  simpa [← Complex.ofReal_pow] using
    Complex.hasSum_re (coordinate_channel_current b hz hconn u ψ)

/-- All electronic derivative directions use the same normalized coordinates.
The remainder is the actual lift metric times the local density. -/
theorem coordinate_repair_kinetic {J : Type*} [Fintype J]
    (b : HilbertBasis ι ℂ V) {z : V} (dz : J → V) (s : J → ℝ)
    (hz : ‖z‖ = 1) (hconn : ∀ j, inner ℂ z (dz j) = Complex.I * s j)
    (u : J → H) (ψ : H) :
    1 / 2 * ∑ j, ∑' a,
      ‖coordinate b z a • u j - Complex.I • coordinate b (dz j) a • ψ‖ ^ 2 =
      1 / 2 * ∑ j, ‖u j‖ ^ 2 + ∑ j, s j * (inner ℂ (u j) ψ).re +
        1 / 2 * (∑ j, ‖dz j‖ ^ 2) * ‖ψ‖ ^ 2 := by
  simp_rw [(coordinate_channel_energy b hz (hconn _) (u _) ψ).tsum_eq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- A metric estimate on the Hilbert lift gives the repaired kinetic bound.
No norm or connection series is assumed for the scalar multipliers. -/
theorem coordinate_repair_kinetic_le {J : Type*} [Fintype J]
    (b : HilbertBasis ι ℂ V) {z : V} (dz : J → V) (s : J → ℝ)
    (hz : ‖z‖ = 1) (hconn : ∀ j, inner ℂ z (dz j) = Complex.I * s j)
    (u : J → H) (ψ : H) {M : ℝ} (hmetric : (∑ j, ‖dz j‖ ^ 2) ≤ M) :
    1 / 2 * ∑ j, ∑' a,
      ‖coordinate b z a • u j - Complex.I • coordinate b (dz j) a • ψ‖ ^ 2 ≤
      1 / 2 * ∑ j, ‖u j‖ ^ 2 + ∑ j, s j * (inner ℂ (u j) ψ).re +
        1 / 2 * M * ‖ψ‖ ^ 2 := by
  rw [coordinate_repair_kinetic b dz s hz hconn u ψ]
  have hm := mul_le_mul_of_nonneg_right hmetric (sq_nonneg ‖ψ‖)
  linarith

end GptLean.Repair
