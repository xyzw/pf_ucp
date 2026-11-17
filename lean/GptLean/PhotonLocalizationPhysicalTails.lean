import GptLean.PhotonLocalizationCompactness
import GptLean.PhotonLocalizationKernelCutoffs
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
The two physical cutoff tails used in local trace compactness.

The photon cutoff is the finite sum of number-sector projections. Its
tail follows from the normal spectral trace expansion and the first
number moment. The electronic cutoff is the actual product of rescaled
smooth bumps. Its tail follows from the position spectral measure and
the defining one-particle density identity for arbitrary bounded tests.
Neither cutoff tail inequality is part of the background data.
-/

namespace GptLean.PhotonLocalization

open MeasureTheory
open scoped BigOperators BoundedContinuousFunction

section Number

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The physical number cutoff, formed from the number-sector projections. -/
noncomputable def numberSectorCutoff (sector : ℕ → H →L[ℂ] H) (M : ℕ) : H →L[ℂ] H :=
  ∑ k ∈ Finset.range (M + 1), sector k

theorem numberSectorCutoff_projection
    (sector : ℕ → H →L[ℂ] H) (hsector : ∀ k, IsStarProjection (sector k))
    (horthogonal : ∀ i j, i ≠ j → sector i * sector j = 0) (M : ℕ) :
    IsStarProjection (numberSectorCutoff sector M) := by
  have hsum : ∀ s : Finset ℕ, IsStarProjection (∑ k ∈ s, sector k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
      rw [Finset.sum_insert hk]
      apply (hsector k).add ih
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => horthogonal k j (fun heq => hk (heq ▸ hj))
  exact hsum _

omit [CompleteSpace H] in
theorem numberSectorCutoff_commute
    (sector : ℕ → H →L[ℂ] H) (A : H →L[ℂ] H)
    (hcommute : ∀ k, Commute A (sector k)) (M : ℕ) :
    Commute A (numberSectorCutoff sector M) := by
  change A * (∑ k ∈ Finset.range (M + 1), sector k) =
    (∑ k ∈ Finset.range (M + 1), sector k) * A
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => (hcommute k).eq

omit [CompleteSpace H] in
/-- Normality gives the countable spectral trace expansion. The finite
cutoff expectation and its Markov bound are then consequences. -/
theorem numberSectorCutoff_tail_eq
    (sector : ℕ → H →L[ℂ] H) (φ : (H →L[ℂ] H) →L[ℂ] ℂ)
    (htrace : HasSum (fun k => (φ (sector k)).re) (φ 1).re) (M : ℕ) :
    (φ (1 - numberSectorCutoff sector M)).re =
      ∑' k, if M < k then (φ (sector k)).re else 0 := by
  classical
  have hs := htrace.summable.sum_add_tsum_compl (s := Finset.range (M + 1))
  rw [tsum_subtype ((Finset.range (M + 1) : Set ℕ)ᶜ)
    (fun k => (φ (sector k)).re)] at hs
  have heq : (fun k => ((Finset.range (M + 1) : Set ℕ)ᶜ).indicator
      (fun k => (φ (sector k)).re) k) =
      fun k => if M < k then (φ (sector k)).re else 0 := by
    funext k
    simp only [Set.indicator, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_range]
    split_ifs <;> first | rfl | omega
  rw [heq, htrace.tsum_eq] at hs
  simp only [numberSectorCutoff, map_sub, map_sum, Complex.sub_re, Complex.re_sum]
  linarith

theorem numberSectorCutoff_tail_le
    (sector : ℕ → H →L[ℂ] H) (hsector : ∀ k, IsStarProjection (sector k))
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : PhotonTrace.IsPosFunctional φ)
    (htrace : HasSum (fun k => (φ (sector k)).re) (φ 1).re)
    (hmean : Summable (fun k : ℕ => (k : ℝ) * (φ (sector k)).re))
    {B : ℝ} (hB : ∑' k : ℕ, (k : ℝ) * (φ (sector k)).re ≤ B) (M : ℕ) :
    (φ (1 - numberSectorCutoff sector M)).re ≤ B / (M + 1) := by
  rw [numberSectorCutoff_tail_eq sector φ htrace]
  exact (PhotonLoss.tail_le_mean_div
    (fun k => hφ.proj_re_nonneg (hsector k)) hmean M).trans
    (div_le_div_of_nonneg_right hB (by positivity))

end Number

section Electronic

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  {N : ℕ}

/-- The smooth configuration cutoff localizes every electronic coordinate. -/
noncomputable def electronicProduct (L : ℝ) (x : Fin N → P) : ℝ :=
  ∏ i, PhotonLocalizationKernelCutoffs.retained L (x i)

theorem electronicProduct_nonneg (L : ℝ) (x : Fin N → P) :
    0 ≤ electronicProduct L x :=
  Finset.prod_nonneg fun _ _ => PhotonLocalizationKernelCutoffs.retained_nonneg _ _

theorem electronicProduct_le_one (L : ℝ) (x : Fin N → P) :
    electronicProduct L x ≤ 1 :=
  Finset.prod_le_one
    (fun _ _ => PhotonLocalizationKernelCutoffs.retained_nonneg _ _)
    (fun _ _ => PhotonLocalizationKernelCutoffs.retained_le_one _ _)

theorem electronicProduct_continuous (L : ℝ) :
    Continuous (electronicProduct (P := P) (N := N) L) := by
  apply continuous_finsetProd
  intro i _
  exact (PhotonLocalizationKernelCutoffs.retained_smooth L).continuous.comp
    (continuous_apply i)

theorem electronicProduct_eq_one {L : ℝ} (hL : 0 < L) {x : Fin N → P}
    (hx : ∀ i, ‖x i‖ ≤ L) : electronicProduct L x = 1 := by
  unfold electronicProduct
  simp [PhotonLocalizationKernelCutoffs.retained_eq_one hL (hx _)]

theorem electronicProduct_eq_zero {L : ℝ} (hL : 0 < L) {x : Fin N → P}
    (hx : ∃ i, 2 * L ≤ ‖x i‖) : electronicProduct L x = 0 := by
  classical
  obtain ⟨i, hi⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (PhotonLocalizationKernelCutoffs.retained_eq_zero hL hi)

/-- The explicit bounded continuous multiplier used by position calculus. -/
noncomputable def electronicProductBCF (L : ℝ) : (Fin N → P) →ᵇ ℝ where
  toFun := electronicProduct L
  continuous_toFun := electronicProduct_continuous L
  map_bounded' := ⟨1, fun x y => by
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [electronicProduct_nonneg L x, electronicProduct_nonneg L y,
      electronicProduct_le_one L x, electronicProduct_le_one L y]⟩

/-- A pointwise union bound, before any state or density is chosen. -/
theorem electronicProduct_tail_pointwise {L : ℝ} (hL : 0 < L) (x : Fin N → P) :
    (1 - electronicProduct L x) ^ 2 ≤ ∑ i, if L < ‖x i‖ then (1 : ℝ) else 0 := by
  classical
  by_cases hx : ∀ i, ‖x i‖ ≤ L
  · rw [electronicProduct_eq_one hL hx]
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  · push Not at hx
    obtain ⟨i, hi⟩ := hx
    have hsum : (1 : ℝ) ≤ ∑ j : Fin N, if L < ‖x j‖ then (1 : ℝ) else 0 := by
      calc (1 : ℝ) = (if L < ‖x i‖ then (1 : ℝ) else 0) := by simp [hi]
        _ ≤ ∑ j : Fin N, if L < ‖x j‖ then (1 : ℝ) else 0 :=
          Finset.single_le_sum (f := fun j : Fin N => if L < ‖x j‖ then (1 : ℝ) else 0)
            (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
    have h0 := electronicProduct_nonneg L x
    have h1 := electronicProduct_le_one L x
    nlinarith

variable [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]
  {μ : Measure P}

/-- The defining density identity, uniformly for all bounded measurable
one-particle tests. This is a marginal identity, not a cutoff estimate. -/
structure ElectronicDensityMeasure (ν : Measure (Fin N → P)) (ρ : Lp ℝ 1 μ) : Prop where
  test : ∀ (f : P → ℝ), Measurable f → (∃ C, ∀ y, ‖f y‖ ≤ C) →
    (∫ x, ∑ i, f (x i) ∂ν) = ∫ y, f y * ‖ρ y‖ ∂μ

theorem electronicProduct_integral_tail_le
    (ν : Measure (Fin N → P)) [IsFiniteMeasure ν] (ρ : Lp ℝ 1 μ)
    (hρ : ElectronicDensityMeasure ν ρ) {L : ℝ} (hL : 0 < L) :
    (∫ x, (1 - electronicProduct L x) ^ 2 ∂ν) ≤
      ∫ y in (Metric.closedBall (0 : P) L)ᶜ, ‖ρ y‖ ∂μ := by
  classical
  let f : P → ℝ := (Metric.closedBall (0 : P) L)ᶜ.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator measurableSet_closedBall.compl
  have hfb : ∀ y, ‖f y‖ ≤ 1 := by
    intro y
    simp only [f, Set.indicator]
    split_ifs <;> norm_num
  have hcount : Integrable (fun x : Fin N → P => ∑ i, f (x i)) ν := by
    apply integrable_finsetSum
    intro i _
    exact Integrable.of_bound (hf.comp (measurable_pi_apply i)).aestronglyMeasurable 1
      (ae_of_all _ fun x => hfb (x i))
  have hcut : Integrable (fun x : Fin N → P => (1 - electronicProduct L x) ^ 2) ν := by
    apply Integrable.of_bound
      ((continuous_const.sub (electronicProduct_continuous L)).pow 2).aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      change (1 - electronicProduct L x) ^ 2 ≤ 1
      nlinarith [electronicProduct_nonneg L x, electronicProduct_le_one L x]
  calc
    (∫ x, (1 - electronicProduct L x) ^ 2 ∂ν) ≤ ∫ x, ∑ i, f (x i) ∂ν := by
      apply integral_mono hcut hcount
      intro x
      simpa only [f, Set.indicator, Set.mem_compl_iff, Metric.mem_closedBall,
        dist_zero_right, not_le] using electronicProduct_tail_pointwise hL x
    _ = ∫ y, f y * ‖ρ y‖ ∂μ := hρ.test f hf ⟨1, hfb⟩
    _ = ∫ y in (Metric.closedBall (0 : P) L)ᶜ, ‖ρ y‖ ∂μ := by
      rw [← integral_indicator measurableSet_closedBall.compl]
      apply integral_congr_ae
      exact ae_of_all _ fun y => by simp only [f, Set.indicator]; split_ifs <;> simp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Standard position spectral calculus and its normal-state measure.
All bounded continuous functions are covered by the same trace formula. -/
structure ElectronicPositionTrace (φ : (H →L[ℂ] H) →L[ℂ] ℂ)
    (ν : Measure (Fin N → P)) where
  observable : ((Fin N → P) →ᵇ ℝ) →+* (H →L[ℂ] H)
  selfadjoint : ∀ f, IsSelfAdjoint (observable f)
  trace : ∀ f, (φ (observable f)).re = ∫ x, f x ∂ν

/-- Electronic localization is the image of the explicit smooth product
under the physical position spectral calculus. -/
noncomputable def ElectronicPositionTrace.cutoff
    {φ : (H →L[ℂ] H) →L[ℂ] ℂ} {ν : Measure (Fin N → P)}
    (T : ElectronicPositionTrace φ ν) (L : ℝ) : H →L[ℂ] H :=
  T.observable (electronicProductBCF L)

theorem ElectronicPositionTrace.tail_le
    {φ : (H →L[ℂ] H) →L[ℂ] ℂ} {ν : Measure (Fin N → P)} [IsFiniteMeasure ν]
    (T : ElectronicPositionTrace φ ν) (ρ : Lp ℝ 1 μ)
    (hρ : ElectronicDensityMeasure ν ρ) {L : ℝ} (hL : 0 < L) :
    (φ ((1 - T.cutoff L) ^ 2)).re ≤
      ∫ y in (Metric.closedBall (0 : P) L)ᶜ, ‖ρ y‖ ∂μ := by
  have heq : (1 - T.cutoff L) ^ 2 =
      T.observable ((1 - electronicProductBCF L) ^ 2) := by
    simp only [map_pow, map_sub, map_one, ElectronicPositionTrace.cutoff]
  rw [heq, T.trace]
  exact electronicProduct_integral_tail_le ν ρ hρ hL

end Electronic

end GptLean.PhotonLocalization
