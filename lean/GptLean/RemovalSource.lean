import GptLean.ElectronicLocalizationIMS
import GptLean.Gaussian.CovariantSlicing
import GptLean.Repair.ParameterSections

/-!
Source normalization and tested constraints from actual localized L²
vectors followed by a Wiener--Itô--Segal unitary. The source and spatial
indices are flattened explicitly. No localized source sum is postulated.
The original spectral trace expansion and rank-one action of bounded
observables are the operator inputs.
-/

namespace GptLean.RemovalSource

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open MeasureTheory Filter Gaussian ElectronicLocalization
open scoped ENNReal Topology

section Series

variable {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]

/-- Absolute summability justifies flattening signed or complex tested
source series, including both localization and spectral indices. -/
theorem flatten_hasSum {f : ℕ → ℕ → F} {row : ℕ → F} {target : F}
    (habs : Summable (fun p : ℕ × ℕ => ‖f p.1 p.2‖))
    (hrow : ∀ n, HasSum (f n) (row n)) (hsource : HasSum row target) :
    HasSum (fun i => f (Nat.unpair i).1 (Nat.unpair i).2) target := by
  have hs := habs.of_norm
  have ht : (∑' p : ℕ × ℕ, f p.1 p.2) = target := by
    rw [hs.tsum_prod' (fun n => (hrow n).summable)]
    exact (tsum_congr (fun n => (hrow n).tsum_eq)).trans hsource.tsum_eq
  change HasSum ((fun p : ℕ × ℕ => f p.1 p.2) ∘ Nat.pairEquiv.symm) target
  exact (Nat.pairEquiv.symm.hasSum_iff
    (f := fun p : ℕ × ℕ => f p.1 p.2) (a := target)).mpr (ht ▸ hs.hasSum)

end Series

section ScalarLocalization

variable {X F : Type*} [MeasurableSpace X] {ν : Measure X}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The square partition preserves every integrable scalar or Banach
valued observable, with an explicit absolutely integrable majorant. -/
theorem square_partition_integral (f : ℕ → X → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν)
    {g : X → F} (hg : Integrable g ν) :
    HasSum (fun a => ∫ x, (f a x ^ 2) • g x ∂ν) (∫ x, g x ∂ν) := by
  let bound : ℕ → X → ℝ := fun a x => f a x ^ 2 * ‖g x‖
  have hb (x : X) : HasSum (fun a => bound a x) ‖g x‖ := by
    simpa only [bound, one_mul] using (hpart x).mul_right ‖g x‖
  apply hasSum_integral_of_dominated_convergence bound
    (fun a => ((hf a).pow 2).smul hg.aestronglyMeasurable)
  · intro a
    filter_upwards with x
    change ‖(f a x ^ 2) • g x‖ ≤ f a x ^ 2 * ‖g x‖
    simp only [norm_smul, Real.norm_of_nonneg (sq_nonneg _), le_refl]
  · exact Eventually.of_forall (fun x => (hb x).summable)
  · exact hg.norm.congr (Eventually.of_forall (fun x => (hb x).tsum_eq.symm))
  · exact Eventually.of_forall (fun x => by simpa using (hpart x).smul_const (g x))

end ScalarLocalization

section LocalizedVectors

variable {X H : Type*} [MeasurableSpace X] {ν : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem partition_square_le_one (f : ℕ → X → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1) (a : ℕ) (x : X) :
    f a x ^ 2 ≤ 1 := by
  simpa only [Finset.sum_singleton, (hpart x).tsum_eq] using
    (hpart x).summable.sum_le_tsum {a} (fun i _ => sq_nonneg (f i x))

theorem lp_norm_sq (ψ : Lp H 2 ν) : ‖ψ‖ ^ 2 = ∫ x, ‖ψ x‖ ^ 2 ∂ν := by
  simpa only [Lp.toLp_coeFn] using Repair.toL2_norm_sq (Lp.memLp ψ)

theorem localized_memLp (f : ℕ → X → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : Lp H 2 ν) (a : ℕ) :
    MemLp (localizedValue f ψ a) 2 ν := by
  have hm := (Complex.continuous_ofReal.comp_aestronglyMeasurable (hf a)).smul
    (Lp.memLp ψ).1
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply ((memLp_two_iff_integrable_sq_norm (Lp.memLp ψ).1).mp (Lp.memLp ψ)).mono'
    (hm.norm.pow 2)
  filter_upwards with x
  change ‖‖localizedValue f ψ a x‖ ^ 2‖ ≤ ‖ψ x‖ ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _), localizedValue, real_scalar_norm_sq]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (partition_square_le_one f hpart a x) (sq_nonneg ‖ψ x‖)

/-- The source is localized before applying the Gaussian unitary. -/
noncomputable def localizedVector (f : ℕ → X → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : Lp H 2 ν) (a : ℕ) : Lp H 2 ν :=
  (localized_memLp f hpart hf ψ a).toLp (localizedValue f ψ a)

theorem localizedVector_mass (f : ℕ → X → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : Lp H 2 ν) :
    HasSum (fun a => ‖localizedVector f hpart hf ψ a‖ ^ 2) (‖ψ‖ ^ 2) := by
  have hm := (memLp_two_iff_integrable_sq_norm (Lp.memLp ψ).1).mp (Lp.memLp ψ)
  simpa only [localizedVector, Repair.toL2_norm_sq, ← lp_norm_sq] using
    integrated_localization_mass f hpart hf ψ (Lp.memLp ψ).1 hm

theorem localizedVector_mass_prod (f : ℕ → X → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : ℕ → Lp H 2 ν)
    (hmass : Summable (fun n => ‖ψ n‖ ^ 2)) :
    Summable (fun p : ℕ × ℕ => ‖localizedVector f hpart hf (ψ p.1) p.2‖ ^ 2) := by
  apply (summable_prod_of_nonneg (fun p => sq_nonneg _)).mpr
  refine ⟨fun n => (localizedVector_mass f hpart hf (ψ n)).summable, ?_⟩
  simpa only [(localizedVector_mass f hpart hf _).tsum_eq] using hmass

end LocalizedVectors

section GaussianSource

variable {X Q H K : Type*} [MeasurableSpace X] [MeasurableSpace Q]
  {ν : Measure X} {μ : Measure Q}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The conditional source is the actual WIS image of the localized
spectral vector, with a fixed enumeration of the two countable indices. -/
noncomputable def localizedFiber (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 μ)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : ℕ → Lp H 2 ν)
    (i : ℕ) (q : Q) : K :=
  unitaryFiber U (localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2) q

/-- A normalized spectral source gives normalized localized Gaussian
fibres. Neither conditional normalization nor its total sum is an input. -/
theorem localizedFiber_normalized (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 μ)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : ℕ → Lp H 2 ν)
    (hmass : HasSum (fun n => ‖ψ n‖ ^ 2) 1) :
    HasSum (fun i => ∫ q, ‖localizedFiber U f hpart hf ψ i q‖ ^ 2 ∂μ) 1 := by
  simpa only [localizedFiber, unitaryFiber_norm_sq, Repair.flattenVectors] using
    Repair.flattenVectors_mass (fun n => localizedVector_mass f hpart hf (ψ n)) hmass

/-- When the hard fibre is the electronic L² space, normalization has
exactly the iterated-integral form required by the removal channel. -/
theorem localizedFiber_spatial_normalized {Y Hhard : Type*} [MeasurableSpace Y]
    {σ : Measure Y} [NormedAddCommGroup Hhard] [InnerProductSpace ℂ Hhard]
    (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp (Lp Hhard 2 σ) 2 μ)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : ℕ → Lp H 2 ν)
    (hmass : HasSum (fun n => ‖ψ n‖ ^ 2) 1) :
    HasSum (fun i => ∫ q, ∫ x, ‖localizedFiber U f hpart hf ψ i q x‖ ^ 2 ∂σ ∂μ) 1 := by
  simpa only [← lp_norm_sq] using localizedFiber_normalized U f hpart hf ψ hmass

/-- Unitarity evaluates each conditional tested source on its original
localized vector. This is the common bridge for density and hard tests. -/
theorem localizedFiber_test (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 μ)
    (B : K →L[ℂ] K) (f : ℕ → X → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : ℕ → Lp H 2 ν) (i : ℕ) :
    (∫ q, inner ℂ (localizedFiber U f hpart hf ψ i q)
      (B (localizedFiber U f hpart hf ψ i q)) ∂μ) =
      inner ℂ (localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2)
        (unitaryTest U B (localizedVector f hpart hf (ψ (Nat.unpair i).1)
          (Nat.unpair i).2)) :=
  (unitary_tested_current U B _ _).2.symm

/-- A bounded fibre multiplication observable is integrable on each
source vector, before any partition or spectral sum is taken. -/
theorem fiber_quadratic_integrable (W : X → H →L[ℂ] H) {C : ℝ}
    (hW : ∀ᵐ x ∂ν, ‖W x‖ ≤ C) (ψ : Lp H 2 ν)
    (hmeas : AEStronglyMeasurable (fun x => W x (ψ x)) ν) :
    Integrable (fun x => inner ℂ (ψ x) (W x (ψ x))) ν := by
  have hm := (memLp_two_iff_integrable_sq_norm (Lp.memLp ψ).1).mp (Lp.memLp ψ)
  apply (hm.const_mul C).mono' ((Lp.memLp ψ).1.inner hmeas)
  filter_upwards [hW] with x hx
  calc
    ‖inner ℂ (ψ x) (W x (ψ x))‖ ≤ ‖ψ x‖ * ‖W x (ψ x)‖ := norm_inner_le_norm _ _
    _ ≤ ‖ψ x‖ * (‖W x‖ * ‖ψ x‖) :=
      mul_le_mul_of_nonneg_left ((W x).le_opNorm _) (norm_nonneg _)
    _ = ‖W x‖ * ‖ψ x‖ ^ 2 := by ring
    _ ≤ C * ‖ψ x‖ ^ 2 := mul_le_mul_of_nonneg_right hx (sq_nonneg _)

/-- The standard rank-one multiplication formula is evaluated on the
constructed localized L² representative. -/
theorem localizedVector_quadratic (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 μ)
    (B : K →L[ℂ] K) (W : X → H →L[ℂ] H)
    (hrank : ∀ v : Lp H 2 ν, inner ℂ v (unitaryTest U B v) =
      ∫ x, inner ℂ (v x) (W x (v x)) ∂ν)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : Lp H 2 ν) (a : ℕ) :
    inner ℂ (localizedVector f hpart hf ψ a)
      (unitaryTest U B (localizedVector f hpart hf ψ a)) =
      ∫ x, (f a x ^ 2) • inner ℂ (ψ x) (W x (ψ x)) ∂ν := by
  rw [hrank]
  apply integral_congr_ae
  filter_upwards [(localized_memLp f hpart hf ψ a).coeFn_toLp] with x hx
  change inner ℂ ((localized_memLp f hpart hf ψ a).toLp _ x)
    (W x ((localized_memLp f hpart hf ψ a).toLp _ x)) = _
  rw [hx]
  simp only [localizedValue, map_smul, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, Complex.real_smul, Complex.ofReal_pow]
  ring

/-- Localization preserves each bounded multiplication test on one
spectral vector. This includes spatial density and hard-photon tests. -/
theorem localizedVector_test_hasSum (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 μ)
    (B : K →L[ℂ] K) (W : X → H →L[ℂ] H) {C : ℝ}
    (hW : ∀ᵐ x ∂ν, ‖W x‖ ≤ C)
    (hrank : ∀ v : Lp H 2 ν, inner ℂ v (unitaryTest U B v) =
      ∫ x, inner ℂ (v x) (W x (v x)) ∂ν)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : Lp H 2 ν)
    (hmeas : AEStronglyMeasurable (fun x => W x (ψ x)) ν) :
    HasSum (fun a => inner ℂ (localizedVector f hpart hf ψ a)
      (unitaryTest U B (localizedVector f hpart hf ψ a)))
      (inner ℂ ψ (unitaryTest U B ψ)) := by
  simpa only [← localizedVector_quadratic U B W hrank f hpart hf ψ, ← hrank ψ] using
    square_partition_integral f hpart hf (fiber_quadratic_integrable W hW ψ hmeas)

/-- The original spectral trace expansion determines the tested sum of
the actual localized WIS fibres. All localization/source exchanges are
proved by absolute bounds from the original mass. -/
theorem localizedFiber_bounded_test_hasSum (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 μ)
    (B : K →L[ℂ] K) (W : X → H →L[ℂ] H) {C : ℝ}
    (hW : ∀ᵐ x ∂ν, ‖W x‖ ≤ C)
    (hrank : ∀ v : Lp H 2 ν, inner ℂ v (unitaryTest U B v) =
      ∫ x, inner ℂ (v x) (W x (v x)) ∂ν)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : ℕ → Lp H 2 ν)
    (hmeas : ∀ n, AEStronglyMeasurable (fun x => W x (ψ n x)) ν)
    (hmass : Summable (fun n => ‖ψ n‖ ^ 2)) {target : ℂ}
    (hsource : HasSum (fun n => inner ℂ (ψ n) (unitaryTest U B (ψ n))) target) :
    HasSum (fun i => ∫ q, inner ℂ (localizedFiber U f hpart hf ψ i q)
      (B (localizedFiber U f hpart hf ψ i q)) ∂μ) target := by
  have hb := (localizedVector_mass_prod f hpart hf ψ hmass).mul_left ‖B‖
  have habs : Summable (fun p : ℕ × ℕ =>
      ‖inner ℂ (localizedVector f hpart hf (ψ p.1) p.2)
        (unitaryTest U B (localizedVector f hpart hf (ψ p.1) p.2))‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hb
    intro p
    let v := localizedVector f hpart hf (ψ p.1) p.2
    change ‖inner ℂ v (unitaryTest U B v)‖ ≤ ‖B‖ * ‖v‖ ^ 2
    calc
      _ ≤ ‖v‖ * ‖unitaryTest U B v‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖B‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (unitaryTest_norm_le U B v) (norm_nonneg _)
      _ = ‖B‖ * ‖v‖ ^ 2 := by ring
  have hs := flatten_hasSum habs
    (fun n => localizedVector_test_hasSum U B W hW hrank f hpart hf (ψ n) (hmeas n))
    hsource
  simpa only [localizedFiber_test U B f hpart hf ψ] using hs

end GaussianSource

section CurrentSource

variable {X Q H K : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [MeasurableSpace Q] {ν : Measure X} {μ : Measure Q}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- IMS gives L² membership of each actual localized derivative from the
source kinetic density and the partition metric. -/
theorem localizedDerivative_memLp (f : ℕ → X → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (f a)))
    (hd : ∀ a, Differentiable ℝ (f a)) (hpos : ∀ a x, 0 ≤ f a x)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν)
    (ψ dψ : Lp H 2 ν) (v : X)
    (hdf : ∀ a, AEStronglyMeasurable (fun x => fderiv ℝ (f a) x v) ν)
    (hint : Integrable (fun x => ‖dψ x‖ ^ 2 +
      (∑' a, fderiv ℝ (f a) x v ^ 2) * ‖ψ x‖ ^ 2) ν) (a : ℕ) :
    MemLp (localizedDerivative f dψ ψ v a) 2 ν := by
  have hm (a : ℕ) : AEStronglyMeasurable (localizedDerivative f dψ ψ v a) ν :=
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable (hf a)).smul (Lp.memLp dψ).1).sub
      (((Complex.continuous_ofReal.comp_aestronglyMeasurable (hdf a)).smul
        (Lp.memLp ψ).1).const_smul Complex.I)
  apply (memLp_two_iff_integrable_sq_norm (hm a)).mpr
  apply Repair.integrable_term_of_nonnegative_hasSum (fun a => (hm a).norm.pow 2)
    (fun a => Eventually.of_forall (fun x => sq_nonneg _)) _ hint a
  exact Eventually.of_forall
    (fun x => localization_ims_hasSum f hloc hd hpos hpart dψ ψ x v)

/-- The actual localized covariant product derivative as an L² vector. -/
noncomputable def localizedDerivativeVector (f : ℕ → X → ℝ)
    (ψ dψ : Lp H 2 ν) (v : X)
    (hmem : ∀ a, MemLp (localizedDerivative f dψ ψ v a) 2 ν) (a : ℕ) : Lp H 2 ν :=
  (hmem a).toLp (localizedDerivative f dψ ψ v a)

/-- The integrated IMS theorem supplies the energy sum of the exact
localized derivative vectors. -/
theorem localizedDerivativeVector_ims (f : ℕ → X → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (f a)))
    (hd : ∀ a, Differentiable ℝ (f a)) (hpos : ∀ a x, 0 ≤ f a x)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν)
    (ψ dψ : Lp H 2 ν) (v : X)
    (hdf : ∀ a, AEStronglyMeasurable (fun x => fderiv ℝ (f a) x v) ν)
    (hint : Integrable (fun x => ‖dψ x‖ ^ 2 +
      (∑' a, fderiv ℝ (f a) x v ^ 2) * ‖ψ x‖ ^ 2) ν)
    (hmem : ∀ a, MemLp (localizedDerivative f dψ ψ v a) 2 ν) :
    HasSum (fun a => ‖localizedDerivativeVector f ψ dψ v hmem a‖ ^ 2)
      (∫ x, ‖dψ x‖ ^ 2 + (∑' a, fderiv ℝ (f a) x v ^ 2) * ‖ψ x‖ ^ 2 ∂ν) := by
  simpa only [localizedDerivativeVector, Repair.toL2_norm_sq] using
    integrated_localization_ims f hloc hd hpos hpart hf dψ ψ v
      (Lp.memLp dψ).1 (Lp.memLp ψ).1 hdf hint

/-- Original spectral mass and kinetic summability plus the spatial IMS
metric bound prove the double localized derivative-energy sum. -/
theorem localizedDerivativeVector_summable (f : ℕ → X → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (f a)))
    (hd : ∀ a, Differentiable ℝ (f a)) (hpos : ∀ a x, 0 ≤ f a x)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν)
    (ψ dψ : ℕ → Lp H 2 ν) (v : X)
    (hdf : ∀ a, AEStronglyMeasurable (fun x => fderiv ℝ (f a) x v) ν)
    (hint : ∀ n, Integrable (fun x => ‖dψ n x‖ ^ 2 +
      (∑' a, fderiv ℝ (f a) x v ^ 2) * ‖ψ n x‖ ^ 2) ν)
    (hmem : ∀ n a, MemLp (localizedDerivative f (dψ n) (ψ n) v a) 2 ν)
    {C : ℝ} (hmetric : ∀ x, (∑' a, fderiv ℝ (f a) x v ^ 2) ≤ C)
    (hmass : Summable (fun n => ‖ψ n‖ ^ 2))
    (hkinetic : Summable (fun n => ‖dψ n‖ ^ 2)) :
    Summable (fun p : ℕ × ℕ =>
      ‖localizedDerivativeVector f (ψ p.1) (dψ p.1) v (hmem p.1) p.2‖ ^ 2) := by
  have hrow (n : ℕ) := localizedDerivativeVector_ims f hloc hd hpos hpart hf
    (ψ n) (dψ n) v hdf (hint n) (hmem n)
  apply (summable_prod_of_nonneg (fun p => sq_nonneg _)).mpr
  refine ⟨fun n => (hrow n).summable, ?_⟩
  apply Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun a => sq_nonneg _)) _
    (hkinetic.add (hmass.mul_left C))
  intro n
  rw [(hrow n).tsum_eq]
  have hψ := (memLp_two_iff_integrable_sq_norm (Lp.memLp (ψ n)).1).mp (Lp.memLp (ψ n))
  have hdψ := (memLp_two_iff_integrable_sq_norm (Lp.memLp (dψ n)).1).mp (Lp.memLp (dψ n))
  have he := integral_mono_ae (hint n) (hdψ.add (hψ.const_mul C))
    (Eventually.of_forall (fun x => add_le_add (le_refl (‖dψ n x‖ ^ 2))
      (mul_le_mul_of_nonneg_right (hmetric x) (sq_nonneg ‖ψ n x‖))))
  change (∫ x, ‖dψ n x‖ ^ 2 + (∑' a, fderiv ℝ (f a) x v ^ 2) * ‖ψ n x‖ ^ 2 ∂ν) ≤
    (∫ x, ‖dψ n x‖ ^ 2 + C * ‖ψ n x‖ ^ 2 ∂ν) at he
  simpa only [integral_add hdψ (hψ.const_mul C), integral_const_mul, ← lp_norm_sq] using he

/-- Real spatial weights preserve the localization current identity.
The imaginary derivative of the real cutoff vanishes before summation. -/
theorem localizedVector_current_hasSum (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 μ)
    (B : K →L[ℂ] K) {weight : X → ℝ} {C : ℝ}
    (hw : AEStronglyMeasurable weight ν) (hbound : ∀ᵐ x ∂ν, ‖weight x‖ ≤ C)
    (hrank : ∀ v d : Lp H 2 ν, (inner ℂ v (unitaryTest U B d)).re =
      ∫ x, weight x * (inner ℂ (v x) (d x)).re ∂ν)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ dψ : Lp H 2 ν) (v : X)
    (hmem : ∀ a, MemLp (localizedDerivative f dψ ψ v a) 2 ν) :
    HasSum (fun a => (inner ℂ (localizedVector f hpart hf ψ a)
      (unitaryTest U B (localizedDerivativeVector f ψ dψ v hmem a))).re)
      ((inner ℂ ψ (unitaryTest U B dψ)).re) := by
  have hi : Integrable (fun x => weight x * (inner ℂ (ψ x) (dψ x)).re) ν :=
    (Complex.reCLM.integrable_comp (L2.integrable_inner (𝕜 := ℂ) ψ dψ)).bdd_mul hw hbound
  have he (a : ℕ) : (inner ℂ (localizedVector f hpart hf ψ a)
      (unitaryTest U B (localizedDerivativeVector f ψ dψ v hmem a))).re =
      ∫ x, (f a x ^ 2) • (weight x * (inner ℂ (ψ x) (dψ x)).re) ∂ν := by
    rw [hrank]
    apply integral_congr_ae
    filter_upwards [(localized_memLp f hpart hf ψ a).coeFn_toLp, (hmem a).coeFn_toLp]
      with x hψ hdψ
    change weight x * (inner ℂ ((localized_memLp f hpart hf ψ a).toLp _ x)
      ((hmem a).toLp _ x)).re = _
    rw [hψ, hdψ]
    simp only [localizedValue, localizedDerivative, real_scalar_current, smul_eq_mul]
    ring
  simpa only [← he, ← hrank ψ dψ] using square_partition_integral f hpart hf hi

/-- The current source is the WIS image of the localized physical
covariant derivative, using the identical source/localization index. -/
noncomputable def localizedDerivativeFiber (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 μ)
    (f : ℕ → X → ℝ) (ψ dψ : ℕ → Lp H 2 ν) (v : X)
    (hmem : ∀ n a, MemLp (localizedDerivative f (dψ n) (ψ n) v a) 2 ν)
    (i : ℕ) (q : Q) : K :=
  unitaryFiber U (localizedDerivativeVector f (ψ (Nat.unpair i).1) (dψ (Nat.unpair i).1)
    v (hmem (Nat.unpair i).1) (Nat.unpair i).2) q

/-- Original spectral current expansion, localization cancellation and
unitarity prove the current sum of the actual conditional sources.
The localized kinetic summability comes from the integrated IMS identity. -/
theorem localizedFiber_current_hasSum (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 μ)
    (B : K →L[ℂ] K) {weight : X → ℝ} {C : ℝ}
    (hw : AEStronglyMeasurable weight ν) (hbound : ∀ᵐ x ∂ν, ‖weight x‖ ≤ C)
    (hrank : ∀ v d : Lp H 2 ν, (inner ℂ v (unitaryTest U B d)).re =
      ∫ x, weight x * (inner ℂ (v x) (d x)).re ∂ν)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ dψ : ℕ → Lp H 2 ν) (v : X)
    (hmem : ∀ n a, MemLp (localizedDerivative f (dψ n) (ψ n) v a) 2 ν)
    (hmass : Summable (fun n => ‖ψ n‖ ^ 2))
    (hkinetic : Summable (fun p : ℕ × ℕ =>
      ‖localizedDerivativeVector f (ψ p.1) (dψ p.1) v (hmem p.1) p.2‖ ^ 2))
    {target : ℝ}
    (hsource : HasSum (fun n => (inner ℂ (ψ n) (unitaryTest U B (dψ n))).re) target) :
    HasSum (fun i => ∫ q, (inner ℂ (localizedFiber U f hpart hf ψ i q)
      (B (localizedDerivativeFiber U f ψ dψ v hmem i q))).re ∂μ) target := by
  have hb := ((localizedVector_mass_prod f hpart hf ψ hmass).add hkinetic).mul_left (‖B‖ / 2)
  have habs : Summable (fun p : ℕ × ℕ =>
      ‖(inner ℂ (localizedVector f hpart hf (ψ p.1) p.2)
        (unitaryTest U B (localizedDerivativeVector f (ψ p.1) (dψ p.1)
          v (hmem p.1) p.2))).re‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hb
    intro p
    let a := localizedVector f hpart hf (ψ p.1) p.2
    let d := localizedDerivativeVector f (ψ p.1) (dψ p.1) v (hmem p.1) p.2
    change ‖(inner ℂ a (unitaryTest U B d)).re‖ ≤ ‖B‖ / 2 * (‖a‖ ^ 2 + ‖d‖ ^ 2)
    have hr : ‖(inner ℂ a (unitaryTest U B d)).re‖ ≤ ‖B‖ * ‖a‖ * ‖d‖ := by
      calc
        _ ≤ ‖inner ℂ a (unitaryTest U B d)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖a‖ * ‖unitaryTest U B d‖ := norm_inner_le_norm _ _
        _ ≤ ‖a‖ * (‖B‖ * ‖d‖) :=
          mul_le_mul_of_nonneg_left (unitaryTest_norm_le U B d) (norm_nonneg _)
        _ = ‖B‖ * ‖a‖ * ‖d‖ := by ring
    nlinarith [mul_nonneg (norm_nonneg B) (sq_nonneg (‖a‖ - ‖d‖))]
  have hs := flatten_hasSum habs
    (fun n => localizedVector_current_hasSum U B hw hbound hrank f hpart hf
      (ψ n) (dψ n) v (hmem n)) hsource
  have he (i : ℕ) : (∫ q, (inner ℂ (localizedFiber U f hpart hf ψ i q)
      (B (localizedDerivativeFiber U f ψ dψ v hmem i q))).re ∂μ) =
      (inner ℂ (localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2)
        (unitaryTest U B (localizedDerivativeVector f (ψ (Nat.unpair i).1)
          (dψ (Nat.unpair i).1) v (hmem (Nat.unpair i).1) (Nat.unpair i).2))).re := by
    have ht := unitary_tested_current U B
      (localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2)
      (localizedDerivativeVector f (ψ (Nat.unpair i).1) (dψ (Nat.unpair i).1)
        v (hmem (Nat.unpair i).1) (Nat.unpair i).2)
    exact (integral_re ht.1).trans (congrArg Complex.re ht.2.symm)
  simpa only [he] using hs

end CurrentSource
end GptLean.RemovalSource
