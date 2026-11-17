import GptLean.RemovalSource

/-!
Joint Gaussian/electronic source representatives from a product-space WIS
unitary. General bounded electronic multiplication tests act on the target
L² space, so density and current tests can vary in the electron coordinate.
All iterated source integrals follow from L² and Fubini, with their original
spectral trace expansions as the only source sum input.
-/

namespace GptLean.RemovalSource

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open MeasureTheory MeasureTheory.Measure Filter Gaussian ElectronicLocalization
open scoped ENNReal Topology

section OperatorLocalization

variable {X H : Type*} [MeasurableSpace X] {ν : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Localizing the actual L² representatives preserves every bounded
decomposable observable on the original Hilbert space. -/
theorem operator_localization_hasSum (B : Lp H 2 ν →L[ℂ] Lp H 2 ν)
    (W : X → H →L[ℂ] H) {C : ℝ} (hW : ∀ᵐ x ∂ν, ‖W x‖ ≤ C)
    (hrank : ∀ v : Lp H 2 ν, inner ℂ v (B v) =
      ∫ x, inner ℂ (v x) (W x (v x)) ∂ν)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : Lp H 2 ν)
    (hmeas : AEStronglyMeasurable (fun x => W x (ψ x)) ν) :
    HasSum (fun a => inner ℂ (localizedVector f hpart hf ψ a)
      (B (localizedVector f hpart hf ψ a))) (inner ℂ ψ (B ψ)) := by
  have he (a : ℕ) : inner ℂ (localizedVector f hpart hf ψ a)
      (B (localizedVector f hpart hf ψ a)) =
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
  simpa only [← he, ← hrank ψ] using
    square_partition_integral f hpart hf (fiber_quadratic_integrable W hW ψ hmeas)

theorem operator_localization_series (B : Lp H 2 ν →L[ℂ] Lp H 2 ν)
    (W : X → H →L[ℂ] H) {C : ℝ} (hW : ∀ᵐ x ∂ν, ‖W x‖ ≤ C)
    (hrank : ∀ v : Lp H 2 ν, inner ℂ v (B v) =
      ∫ x, inner ℂ (v x) (W x (v x)) ∂ν)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : ℕ → Lp H 2 ν)
    (hmeas : ∀ n, AEStronglyMeasurable (fun x => W x (ψ n x)) ν)
    (hmass : Summable (fun n => ‖ψ n‖ ^ 2)) {target : ℂ}
    (hsource : HasSum (fun n => inner ℂ (ψ n) (B (ψ n))) target) :
    HasSum (fun i => inner ℂ
      (localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2)
      (B (localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2))) target := by
  have hb := (localizedVector_mass_prod f hpart hf ψ hmass).mul_left ‖B‖
  have habs : Summable (fun p : ℕ × ℕ =>
      ‖inner ℂ (localizedVector f hpart hf (ψ p.1) p.2)
        (B (localizedVector f hpart hf (ψ p.1) p.2))‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hb
    intro p
    let v := localizedVector f hpart hf (ψ p.1) p.2
    change ‖inner ℂ v (B v)‖ ≤ ‖B‖ * ‖v‖ ^ 2
    calc
      ‖inner ℂ v (B v)‖ ≤ ‖v‖ * ‖B v‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖B‖ * ‖v‖) := mul_le_mul_of_nonneg_left (B.le_opNorm v) (norm_nonneg _)
      _ = ‖B‖ * ‖v‖ ^ 2 := by ring
  have hs := flatten_hasSum
    (f := fun n a => inner ℂ (localizedVector f hpart hf (ψ n) a)
      (B (localizedVector f hpart hf (ψ n) a))) habs
    (fun n => operator_localization_hasSum B W hW hrank f hpart hf (ψ n) (hmeas n)) hsource
  exact hs

end OperatorLocalization

section ProductSource

variable {Q X H K : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  {μ : Measure Q} {ν : Measure X} [SFinite μ] [SFinite ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Conjugating an actual bounded target-space observable by the WIS
unitary permits tests depending on the electronic coordinate. -/
noncomputable def conjugatedOperator (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν))
    (B : Lp K 2 (μ.prod ν) →L[ℂ] Lp K 2 (μ.prod ν)) : Lp H 2 ν →L[ℂ] Lp H 2 ν :=
  U.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (B.comp U.toContinuousLinearEquiv.toContinuousLinearMap)

theorem conjugatedOperator_inner (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν))
    (B : Lp K 2 (μ.prod ν) →L[ℂ] Lp K 2 (μ.prod ν)) (ψ dψ : Lp H 2 ν) :
    inner ℂ ψ (conjugatedOperator U B dψ) = inner ℂ (U ψ) (B (U dψ)) := by
  change inner ℂ ψ (U.symm (B (U dψ))) = inner ℂ (U ψ) (B (U dψ))
  rw [← U.inner_map_map ψ (U.symm (B (U dψ))), U.apply_symm_apply]

/-- These are actual strongly measurable joint representatives. -/
theorem localizedFiber_stronglyMeasurable
    (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν))
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : ℕ → Lp H 2 ν) (i : ℕ) :
    StronglyMeasurable (localizedFiber U f hpart hf ψ i) :=
  Lp.stronglyMeasurable _

/-- Product-space WIS gives the exact normalized iterated source mass. -/
theorem localizedFiber_product_normalized
    (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν))
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : ℕ → Lp H 2 ν)
    (hmass : HasSum (fun n => ‖ψ n‖ ^ 2) 1) :
    HasSum (fun i => ∫ q, ∫ x, ‖localizedFiber U f hpart hf ψ i (q, x)‖ ^ 2 ∂ν ∂μ) 1 := by
  have he (i : ℕ) : (∫ q, ∫ x, ‖localizedFiber U f hpart hf ψ i (q, x)‖ ^ 2 ∂ν ∂μ) =
      ∫ qx, ‖localizedFiber U f hpart hf ψ i qx‖ ^ 2 ∂μ.prod ν :=
    (integral_prod _ (unitaryFiber_norm_sq_integrable U _)).symm
  simpa only [he] using localizedFiber_normalized U f hpart hf ψ hmass

/-- Density and hard-marginal source tests are evaluated on the same
joint representatives. Multiplication formulas are standard rank-one
operator facts, and the source sum is the original spectral trace. -/
theorem localizedFiber_product_test_hasSum
    (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν))
    (B : Lp K 2 (μ.prod ν) →L[ℂ] Lp K 2 (μ.prod ν))
    (W : X → H →L[ℂ] H) (Wtarget : Q × X → K →L[ℂ] K) {C Ctarget : ℝ}
    (hW : ∀ᵐ x ∂ν, ‖W x‖ ≤ C)
    (hWt : ∀ᵐ qx ∂μ.prod ν, ‖Wtarget qx‖ ≤ Ctarget)
    (hmt : ∀ v : Lp K 2 (μ.prod ν),
      AEStronglyMeasurable (fun qx => Wtarget qx (v qx)) (μ.prod ν))
    (hsource_rankOne : ∀ v : Lp H 2 ν, inner ℂ v (conjugatedOperator U B v) =
      ∫ x, inner ℂ (v x) (W x (v x)) ∂ν)
    (htarget_rankOne : ∀ v : Lp K 2 (μ.prod ν), inner ℂ v (B v) =
      ∫ qx, inner ℂ (v qx) (Wtarget qx (v qx)) ∂μ.prod ν)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : ℕ → Lp H 2 ν)
    (hmeas : ∀ n, AEStronglyMeasurable (fun x => W x (ψ n x)) ν)
    (hmass : Summable (fun n => ‖ψ n‖ ^ 2)) {target : ℂ}
    (hsource : HasSum (fun n => inner ℂ (ψ n) (conjugatedOperator U B (ψ n))) target) :
    HasSum (fun i => ∫ q, ∫ x, inner ℂ (localizedFiber U f hpart hf ψ i (q, x))
      (Wtarget (q, x) (localizedFiber U f hpart hf ψ i (q, x))) ∂ν ∂μ) target := by
  have hs := operator_localization_series (conjugatedOperator U B) W hW
    hsource_rankOne f hpart hf ψ hmeas hmass hsource
  have he (i : ℕ) : (∫ q, ∫ x, inner ℂ (localizedFiber U f hpart hf ψ i (q, x))
      (Wtarget (q, x) (localizedFiber U f hpart hf ψ i (q, x))) ∂ν ∂μ) =
      inner ℂ (localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2)
        (conjugatedOperator U B
          (localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2)) := by
    let v := localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2
    have hi := fiber_quadratic_integrable Wtarget hWt (U v) (hmt (U v))
    exact (integral_prod _ hi).symm.trans
      ((htarget_rankOne (U v)).symm.trans (conjugatedOperator_inner U B v v).symm)
  simpa only [he] using hs

end ProductSource

section ProductCurrent

variable {Q X H K : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace Q] [MeasurableSpace X]
  {μ : Measure Q} {ν : Measure X} [SFinite μ] [SFinite ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem operator_current_localization_hasSum (B : Lp H 2 ν →L[ℂ] Lp H 2 ν)
    {weight : X → ℝ} {C : ℝ}
    (hw : AEStronglyMeasurable weight ν) (hbound : ∀ᵐ x ∂ν, ‖weight x‖ ≤ C)
    (hrank : ∀ v d : Lp H 2 ν, (inner ℂ v (B d)).re =
      ∫ x, weight x * (inner ℂ (v x) (d x)).re ∂ν)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ dψ : Lp H 2 ν) (v : X)
    (hmem : ∀ a, MemLp (localizedDerivative f dψ ψ v a) 2 ν) :
    HasSum (fun a => (inner ℂ (localizedVector f hpart hf ψ a)
      (B (localizedDerivativeVector f ψ dψ v hmem a))).re) ((inner ℂ ψ (B dψ)).re) := by
  have hi : Integrable (fun x => weight x * (inner ℂ (ψ x) (dψ x)).re) ν :=
    (Complex.reCLM.integrable_comp (L2.integrable_inner (𝕜 := ℂ) ψ dψ)).bdd_mul hw hbound
  have he (a : ℕ) : (inner ℂ (localizedVector f hpart hf ψ a)
      (B (localizedDerivativeVector f ψ dψ v hmem a))).re =
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

theorem operator_current_localization_series (B : Lp H 2 ν →L[ℂ] Lp H 2 ν)
    {weight : X → ℝ} {C : ℝ}
    (hw : AEStronglyMeasurable weight ν) (hbound : ∀ᵐ x ∂ν, ‖weight x‖ ≤ C)
    (hrank : ∀ v d : Lp H 2 ν, (inner ℂ v (B d)).re =
      ∫ x, weight x * (inner ℂ (v x) (d x)).re ∂ν)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ dψ : ℕ → Lp H 2 ν) (v : X)
    (hmem : ∀ n a, MemLp (localizedDerivative f (dψ n) (ψ n) v a) 2 ν)
    (hmass : Summable (fun n => ‖ψ n‖ ^ 2))
    (hkinetic : Summable (fun p : ℕ × ℕ =>
      ‖localizedDerivativeVector f (ψ p.1) (dψ p.1) v (hmem p.1) p.2‖ ^ 2))
    {target : ℝ} (hsource : HasSum (fun n => (inner ℂ (ψ n) (B (dψ n))).re) target) :
    HasSum (fun i => (inner ℂ
      (localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2)
      (B (localizedDerivativeVector f (ψ (Nat.unpair i).1) (dψ (Nat.unpair i).1)
        v (hmem (Nat.unpair i).1) (Nat.unpair i).2))).re) target := by
  have hb := ((localizedVector_mass_prod f hpart hf ψ hmass).add hkinetic).mul_left (‖B‖ / 2)
  have habs : Summable (fun p : ℕ × ℕ =>
      ‖(inner ℂ (localizedVector f hpart hf (ψ p.1) p.2)
        (B (localizedDerivativeVector f (ψ p.1) (dψ p.1) v (hmem p.1) p.2))).re‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hb
    intro p
    let a := localizedVector f hpart hf (ψ p.1) p.2
    let d := localizedDerivativeVector f (ψ p.1) (dψ p.1) v (hmem p.1) p.2
    change ‖(inner ℂ a (B d)).re‖ ≤ ‖B‖ / 2 * (‖a‖ ^ 2 + ‖d‖ ^ 2)
    have hr : ‖(inner ℂ a (B d)).re‖ ≤ ‖B‖ * ‖a‖ * ‖d‖ := by
      calc
        _ ≤ ‖inner ℂ a (B d)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖a‖ * ‖B d‖ := norm_inner_le_norm _ _
        _ ≤ ‖a‖ * (‖B‖ * ‖d‖) := mul_le_mul_of_nonneg_left (B.le_opNorm d) (norm_nonneg _)
        _ = ‖B‖ * ‖a‖ * ‖d‖ := by ring
    nlinarith [mul_nonneg (norm_nonneg B) (sq_nonneg (‖a‖ - ‖d‖))]
  have hs := flatten_hasSum
    (f := fun n a => (inner ℂ (localizedVector f hpart hf (ψ n) a)
      (B (localizedDerivativeVector f (ψ n) (dψ n) v (hmem n) a))).re) habs
    (fun n => operator_current_localization_hasSum B hw hbound hrank f hpart hf
      (ψ n) (dψ n) v (hmem n)) hsource
  exact hs

/-- The full tested-current source sum uses the same joint product-space
WIS representatives as density and normalization. -/
theorem localizedFiber_product_current_hasSum
    (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν))
    (B : Lp K 2 (μ.prod ν) →L[ℂ] Lp K 2 (μ.prod ν))
    {weight : X → ℝ} {weightTarget : Q × X → ℝ} {C Ct : ℝ}
    (hw : AEStronglyMeasurable weight ν) (hbound : ∀ᵐ x ∂ν, ‖weight x‖ ≤ C)
    (hwt : AEStronglyMeasurable weightTarget (μ.prod ν))
    (hbt : ∀ᵐ qx ∂μ.prod ν, ‖weightTarget qx‖ ≤ Ct)
    (hsource_rankOne : ∀ v d : Lp H 2 ν, (inner ℂ v (conjugatedOperator U B d)).re =
      ∫ x, weight x * (inner ℂ (v x) (d x)).re ∂ν)
    (htarget_rankOne : ∀ v d : Lp K 2 (μ.prod ν), (inner ℂ v (B d)).re =
      ∫ qx, weightTarget qx * (inner ℂ (v qx) (d qx)).re ∂μ.prod ν)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ dψ : ℕ → Lp H 2 ν) (v : X)
    (hmem : ∀ n a, MemLp (localizedDerivative f (dψ n) (ψ n) v a) 2 ν)
    (hmass : Summable (fun n => ‖ψ n‖ ^ 2))
    (hkinetic : Summable (fun p : ℕ × ℕ =>
      ‖localizedDerivativeVector f (ψ p.1) (dψ p.1) v (hmem p.1) p.2‖ ^ 2))
    {target : ℝ}
    (hsource : HasSum (fun n => (inner ℂ (ψ n) (conjugatedOperator U B (dψ n))).re) target) :
    HasSum (fun i => ∫ q, ∫ x, weightTarget (q, x) *
      (inner ℂ (localizedFiber U f hpart hf ψ i (q, x))
        (localizedDerivativeFiber U f ψ dψ v hmem i (q, x))).re ∂ν ∂μ) target := by
  have hs := operator_current_localization_series (conjugatedOperator U B) hw hbound
    hsource_rankOne f hpart hf ψ dψ v hmem hmass hkinetic hsource
  have he (i : ℕ) : (∫ q, ∫ x, weightTarget (q, x) *
      (inner ℂ (localizedFiber U f hpart hf ψ i (q, x))
        (localizedDerivativeFiber U f ψ dψ v hmem i (q, x))).re ∂ν ∂μ) =
      (inner ℂ (localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2)
        (conjugatedOperator U B (localizedDerivativeVector f (ψ (Nat.unpair i).1)
          (dψ (Nat.unpair i).1) v (hmem (Nat.unpair i).1) (Nat.unpair i).2))).re := by
    let a := localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2
    let d := localizedDerivativeVector f (ψ (Nat.unpair i).1) (dψ (Nat.unpair i).1)
      v (hmem (Nat.unpair i).1) (Nat.unpair i).2
    have hi : Integrable (fun qx => weightTarget qx *
        (inner ℂ (U a qx) (U d qx)).re) (μ.prod ν) :=
      (Complex.reCLM.integrable_comp (L2.integrable_inner (𝕜 := ℂ) (U a) (U d))).bdd_mul hwt hbt
    exact (integral_prod _ hi).symm.trans ((htarget_rankOne (U a) (U d)).symm.trans
      (congrArg Complex.re (conjugatedOperator_inner U B a d)).symm)
  simpa only [he] using hs

end ProductCurrent

section PhasedSource

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def phaseSource (w : ℂ) (ψ : K) : K := w • ψ

/-- The hard derivative is computed from the original conditional
covariant derivative and the residual velocity. -/
def phaseSourceDerivative (w : ℂ) (s : ℝ) (dψ ψ : K) : K :=
  w • (dψ - (s : ℂ) • ψ)

theorem phaseSource_shifted (w : ℂ) (s : ℝ) (dψ ψ : K) :
    phaseSourceDerivative w s dψ ψ + (s : ℂ) • phaseSource w ψ = w • dψ := by
  simp only [phaseSourceDerivative, phaseSource, smul_sub, smul_smul]
  module

theorem phaseSource_mass (w : ℂ) (hw : ‖w‖ = 1) (ψ : K) :
    ‖phaseSource w ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  simp only [phaseSource, norm_smul, hw, one_mul]

/-- Every hard bounded test is unchanged by the same scalar phase. -/
theorem phaseSource_test (w : ℂ) (hw : ‖w‖ = 1) (ψ : K) (B : K →L[ℂ] K) :
    inner ℂ (phaseSource w ψ) (B (phaseSource w ψ)) = inner ℂ ψ (B ψ) := by
  have hw' : (starRingEnd ℂ) w * w = 1 := by
    rw [Complex.conj_mul', hw]
    norm_num
  simp only [phaseSource, map_smul, inner_smul_left, inner_smul_right,
    ← mul_assoc]
  rw [mul_comm w ((starRingEnd ℂ) w), hw', one_mul]

theorem phaseSource_shifted_norm (w : ℂ) (hw : ‖w‖ = 1) (s : ℝ) (dψ ψ : K) :
    ‖phaseSourceDerivative w s dψ ψ + (s : ℂ) • phaseSource w ψ‖ ^ 2 = ‖dψ‖ ^ 2 := by
  rw [phaseSource_shifted, norm_smul, hw, one_mul]

/-- This is exactly the integrand in ChannelRealization.currentSource.
The residual cancels before a current is integrated or summed. -/
theorem phaseSource_current (w : ℂ) (hw : ‖w‖ = 1) (s : ℝ) (dψ ψ : K) :
    inner ℂ (phaseSource w ψ) (phaseSourceDerivative w s dψ ψ) +
      (s : ℂ) * ‖phaseSource w ψ‖ ^ 2 = inner ℂ ψ dψ := by
  have hw' : (starRingEnd ℂ) w * w = 1 := by
    rw [Complex.conj_mul', hw]
    norm_num
  calc
    _ = inner ℂ (phaseSource w ψ)
        (phaseSourceDerivative w s dψ ψ + (s : ℂ) • phaseSource w ψ) := by
      simp only [inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
      rfl
    _ = inner ℂ (w • ψ) (w • dψ) := by rw [phaseSource_shifted]; rfl
    _ = inner ℂ ψ dψ := by
      rw [inner_smul_left, inner_smul_right, ← mul_assoc, hw', one_mul]

/-- A bounded spatial current test multiplies the very same directional
hard derivative and residual used in the energy calculation. -/
theorem phaseSource_weighted_current (w : ℂ) (hw : ‖w‖ = 1)
    (c s : ℝ) (dψ ψ : K) :
    inner ℂ (phaseSource w ψ) ((c : ℂ) • phaseSourceDerivative w s dψ ψ) +
      ((c * s : ℝ) : ℂ) * ‖phaseSource w ψ‖ ^ 2 = (c : ℂ) * inner ℂ ψ dψ := by
  calc
    _ = (c : ℂ) * (inner ℂ (phaseSource w ψ) (phaseSourceDerivative w s dψ ψ) +
        (s : ℂ) * ‖phaseSource w ψ‖ ^ 2) := by
      rw [inner_smul_right, Complex.ofReal_mul]
      ring
    _ = _ := by rw [phaseSource_current w hw]

theorem phaseSource_weighted_current_re (w : ℂ) (hw : ‖w‖ = 1)
    (c s : ℝ) (dψ ψ : K) :
    (inner ℂ (phaseSource w ψ) ((c : ℂ) • phaseSourceDerivative w s dψ ψ) +
      ((c * s : ℝ) : ℂ) * ‖phaseSource w ψ‖ ^ 2).re = c * (inner ℂ ψ dψ).re := by
  rw [phaseSource_weighted_current w hw]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem phaseSource_kinetic {J : Type*} [Fintype J]
    (w : ℂ) (hw : ‖w‖ = 1) (s : J → ℝ) (dψ : J → K) (ψ : K) :
    (1 / 2 : ℝ) * ∑ j,
      ‖phaseSourceDerivative w (s j) (dψ j) ψ + (s j : ℂ) • phaseSource w ψ‖ ^ 2 =
      (1 / 2 : ℝ) * ∑ j, ‖dψ j‖ ^ 2 := by
  simp only [phaseSource_shifted_norm w hw]

end PhasedSource

section PhasedIntegrals

variable {Q X K : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  {μ : Measure Q} {ν : Measure X} [SFinite μ] [SFinite ν]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The source current is integrable on the joint space and its iterated
integral is exactly the original covariant current. -/
theorem phaseSource_current_integral {ψ dψ : Q × X → K}
    (hψ : MemLp ψ 2 (μ.prod ν)) (hdψ : MemLp dψ 2 (μ.prod ν))
    (w : Q × X → ℂ) (s : Q × X → ℝ)
    (hw : ∀ᵐ qx ∂μ.prod ν, ‖w qx‖ = 1) :
    Integrable (fun qx =>
      inner ℂ (phaseSource (w qx) (ψ qx)) (phaseSourceDerivative (w qx) (s qx) (dψ qx) (ψ qx)) +
        (s qx : ℂ) * ‖phaseSource (w qx) (ψ qx)‖ ^ 2) (μ.prod ν) ∧
    (∫ q, ∫ x,
      inner ℂ (phaseSource (w (q, x)) (ψ (q, x)))
        (phaseSourceDerivative (w (q, x)) (s (q, x)) (dψ (q, x)) (ψ (q, x))) +
        (s (q, x) : ℂ) * ‖phaseSource (w (q, x)) (ψ (q, x))‖ ^ 2 ∂ν ∂μ) =
      ∫ q, ∫ x, inner ℂ (ψ (q, x)) (dψ (q, x)) ∂ν ∂μ := by
  have heq : (fun qx =>
      inner ℂ (phaseSource (w qx) (ψ qx)) (phaseSourceDerivative (w qx) (s qx) (dψ qx) (ψ qx)) +
        (s qx : ℂ) * ‖phaseSource (w qx) (ψ qx)‖ ^ 2) =ᵐ[μ.prod ν]
      (fun qx => inner ℂ (ψ qx) (dψ qx)) :=
    hw.mono (fun qx hq => phaseSource_current (w qx) hq (s qx) (dψ qx) (ψ qx))
  refine ⟨(Gaussian.current_fubini hψ hdψ).1.congr heq.symm, ?_⟩
  exact integral_congr_ae ((ae_ae_of_ae_prod heq).mono (fun _ h => integral_congr_ae h))

end PhasedIntegrals
end GptLean.RemovalSource
