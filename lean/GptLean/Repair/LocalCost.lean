import GptLean.Repair.IntegratedChannel
import GptLean.Gaussian.LocalMoments
import Mathlib.MeasureTheory.Integral.Prod

/-!
The local kinetic cost of the actual coordinate repair channel. Completing
the square compares the repaired derivatives directly with the shifted
source derivatives. Local lift metric bounds and measured field moments
then give an integrable kinetic majorant and its quantitative integral.

The weak product rule and the construction of the lift are separate inputs.
No output kinetic inequality is an assumption of these results.
-/

namespace GptLean.Repair

open MeasureTheory MeasureTheory.Measure Filter

variable {X Q J V H : Type*} [MeasurableSpace X] [MeasurableSpace Q]
  [Fintype J] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The squared norm after the full phase and current shift. -/
theorem norm_add_real_smul_sq (u ψ : H) (s : ℝ) :
    ‖u + (s : ℂ) • ψ‖ ^ 2 =
      ‖u‖ ^ 2 + 2 * s * (inner ℂ u ψ).re + s ^ 2 * ‖ψ‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, inner_smul_right]
  change ‖u‖ ^ 2 + 2 * ((s : ℂ) * inner ℂ u ψ).re + s ^ 2 * ‖ψ‖ ^ 2 = _
  rw [Complex.re_ofReal_mul]
  ring

/-- The negative square term in the soft-removal cancellation is retained. -/
theorem coordinate_repair_kinetic_shifted
    (b : HilbertBasis ℕ ℂ V) {z : V} (dz : J → V) (s : J → ℝ)
    (hz : ‖z‖ = 1) (hconn : ∀ j, inner ℂ z (dz j) = Complex.I * s j)
    (u : J → H) (ψ : H) :
    1 / 2 * ∑ j, ∑' a,
      ‖coordinate b z a • u j - Complex.I • coordinate b (dz j) a • ψ‖ ^ 2 =
      1 / 2 * ∑ j, ‖u j + (s j : ℂ) • ψ‖ ^ 2 +
        1 / 2 * (∑ j, (‖dz j‖ ^ 2 - s j ^ 2)) * ‖ψ‖ ^ 2 := by
  rw [coordinate_repair_kinetic b dz s hz hconn u ψ]
  simp_rw [norm_add_real_smul_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Repaired kinetic density, before configuration-space integration. -/
noncomputable def localChannelKinetic (b : HilbertBasis ℕ ℂ V)
    (z : V) (dz : J → V) (u : J → H) (ψ : H) : ℝ :=
  1 / 2 * ∑ j, ∑' a,
    ‖coordinate b z a • u j - Complex.I • coordinate b (dz j) a • ψ‖ ^ 2

/-- The source kinetic density includes the residual velocity exactly. -/
noncomputable def localShiftedKinetic (u : J → H) (ψ : H) (s : J → ℝ) : ℝ :=
  1 / 2 * ∑ j, ‖u j + (s j : ℂ) • ψ‖ ^ 2

theorem localChannelKinetic_nonneg (b : HilbertBasis ℕ ℂ V)
    (z : V) (dz : J → V) (u : J → H) (ψ : H) :
    0 ≤ localChannelKinetic b z dz u ψ := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg
    (fun j _ => tsum_nonneg (fun a => sq_nonneg _)))

theorem localShiftedKinetic_nonneg (u : J → H) (ψ : H) (s : J → ℝ) :
    0 ≤ localShiftedKinetic u ψ s := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => sq_nonneg _))

/-- The same Kraus index is used in every derivative direction. -/
theorem localChannelKinetic_hasSum
    (b : HilbertBasis ℕ ℂ V) {z : V} (dz : J → V) (s : J → ℝ)
    (hz : ‖z‖ = 1) (hconn : ∀ j, inner ℂ z (dz j) = Complex.I * s j)
    (u : J → H) (ψ : H) :
    HasSum (fun a => 1 / 2 * ∑ j,
      ‖coordinate b z a • u j - Complex.I • coordinate b (dz j) a • ψ‖ ^ 2)
      (localChannelKinetic b z dz u ψ) := by
  have he := (hasSum_sum (s := Finset.univ)
    (fun j _ => coordinate_channel_energy b hz (hconn j) (u j) ψ)).mul_left (1 / 2 : ℝ)
  unfold localChannelKinetic
  simp_rw [(coordinate_channel_energy b hz (hconn _) (u _) ψ).tsum_eq]
  exact he

/-- Completion of the square removes the entire mixed term. -/
theorem localChannelKinetic_le_shifted
    (b : HilbertBasis ℕ ℂ V) {z : V} (dz : J → V) (s : J → ℝ)
    (hz : ‖z‖ = 1) (hconn : ∀ j, inner ℂ z (dz j) = Complex.I * s j)
    (u : J → H) (ψ : H) {M : ℝ} (hmetric : ∑ j, ‖dz j‖ ^ 2 ≤ M) :
    localChannelKinetic b z dz u ψ ≤
      localShiftedKinetic u ψ s + 1 / 2 * M * ‖ψ‖ ^ 2 := by
  unfold localChannelKinetic localShiftedKinetic
  rw [coordinate_repair_kinetic_shifted b dz s hz hconn u ψ]
  have hsub : ∑ j, (‖dz j‖ ^ 2 - s j ^ 2) ≤ M :=
    (Finset.sum_le_sum (fun j _ => sub_le_self _ (sq_nonneg _))).trans hmetric
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsub (by norm_num : (0 : ℝ) ≤ 1 / 2))
      (sq_nonneg ‖ψ‖))

/-- The countable channel kinetic density is measurable by its finite
Parseval expression. -/
theorem localChannelKinetic_aestronglyMeasurable {ν : Measure X}
    (b : HilbertBasis ℕ ℂ V) {z : X → V} {dz : J → X → V}
    {u : J → X → H} {ψ : X → H} {s : J → X → ℝ}
    (hdz : ∀ j, AEStronglyMeasurable (dz j) ν)
    (hu : ∀ j, AEStronglyMeasurable (u j) ν)
    (hψ : AEStronglyMeasurable ψ ν)
    (hs : ∀ j, AEStronglyMeasurable (s j) ν)
    (hunit : ∀ᵐ x ∂ν, ‖z x‖ = 1)
    (hconn : ∀ j, ∀ᵐ x ∂ν, inner ℂ (z x) (dz j x) = Complex.I * s j x) :
    AEStronglyMeasurable
      (fun x => localChannelKinetic b (z x) (fun j => dz j x) (fun j => u j x) (ψ x)) ν := by
  have hkin := Finset.aestronglyMeasurable_fun_sum Finset.univ
    (fun j _ => (hu j).norm.pow 2)
  have hcur := Finset.aestronglyMeasurable_fun_sum Finset.univ
    (fun j _ => (hs j).mul
      (Complex.continuous_re.comp_aestronglyMeasurable ((hu j).inner hψ)))
  have hmet := Finset.aestronglyMeasurable_fun_sum Finset.univ
    (fun j _ => (hdz j).norm.pow 2)
  apply (((hkin.const_mul (1 / 2 : ℝ)).add hcur).add
    ((hmet.const_mul (1 / 2 : ℝ)).mul (hψ.norm.pow 2))).congr
  filter_upwards [hunit, ae_all_iff.mpr hconn] with x hx hc
  exact (coordinate_repair_kinetic b (fun j => dz j x) (fun j => s j x)
    hx hc (fun j => u j x) (ψ x)).symm

/-- A uniform local lift bound gives finite kinetic energy and the integral
bound for the defined channel. Only shifted source kinetic energy and mass
must be integrable. -/
theorem localChannelKinetic_integrable_and_le {ν : Measure X}
    (b : HilbertBasis ℕ ℂ V) {z : X → V} {dz : J → X → V}
    {u : J → X → H} {ψ : X → H} {s : J → X → ℝ} {M : ℝ}
    (hdz : ∀ j, AEStronglyMeasurable (dz j) ν)
    (hu : ∀ j, AEStronglyMeasurable (u j) ν)
    (hψ : AEStronglyMeasurable ψ ν)
    (hs : ∀ j, AEStronglyMeasurable (s j) ν)
    (hunit : ∀ᵐ x ∂ν, ‖z x‖ = 1)
    (hconn : ∀ j, ∀ᵐ x ∂ν, inner ℂ (z x) (dz j x) = Complex.I * s j x)
    (hsource : Integrable
      (fun x => localShiftedKinetic (fun j => u j x) (ψ x) (fun j => s j x)) ν)
    (hmass : Integrable (fun x => ‖ψ x‖ ^ 2) ν)
    (hmetric : ∀ᵐ x ∂ν, ∑ j, ‖dz j x‖ ^ 2 ≤ M) :
    Integrable
      (fun x => localChannelKinetic b (z x) (fun j => dz j x) (fun j => u j x) (ψ x)) ν ∧
    (∫ x, localChannelKinetic b (z x) (fun j => dz j x) (fun j => u j x) (ψ x) ∂ν) ≤
      (∫ x, localShiftedKinetic (fun j => u j x) (ψ x) (fun j => s j x) ∂ν) +
        1 / 2 * M * (∫ x, ‖ψ x‖ ^ 2 ∂ν) := by
  have hmajor : Integrable (fun x =>
      localShiftedKinetic (fun j => u j x) (ψ x) (fun j => s j x) +
        1 / 2 * M * ‖ψ x‖ ^ 2) ν := hsource.add (hmass.const_mul (1 / 2 * M))
  have hbound : ∀ᵐ x ∂ν,
      localChannelKinetic b (z x) (fun j => dz j x) (fun j => u j x) (ψ x) ≤
        localShiftedKinetic (fun j => u j x) (ψ x) (fun j => s j x) +
          1 / 2 * M * ‖ψ x‖ ^ 2 := by
    filter_upwards [hunit, ae_all_iff.mpr hconn, hmetric] with x hx hc hm
    exact localChannelKinetic_le_shifted b _ _ hx hc _ _ hm
  have hint := hmajor.mono'
    (localChannelKinetic_aestronglyMeasurable b hdz hu hψ hs hunit hconn)
    (hbound.mono (fun x hx => by
      simpa only [Real.norm_of_nonneg (localChannelKinetic_nonneg b _ _ _ _)] using hx))
  refine ⟨hint, (integral_mono_ae hint hmajor hbound).trans_eq ?_⟩
  rw [integral_add hsource (hmass.const_mul _), integral_const_mul]

/-- The kinetic sum is the integral of the pointwise channel density. This
also proves summability of the actual integrated channel derivatives. -/
theorem integrated_localChannelKinetic {ν : Measure X}
    (b : HilbertBasis ℕ ℂ V) {z : X → V} {dz : J → X → V}
    {u : J → X → H} {ψ : X → H} {s : J → X → ℝ}
    (hz : AEStronglyMeasurable z ν)
    (hdz : ∀ j, AEStronglyMeasurable (dz j) ν)
    (hu : ∀ j, AEStronglyMeasurable (u j) ν)
    (hψ : AEStronglyMeasurable ψ ν)
    (hunit : ∀ᵐ x ∂ν, ‖z x‖ = 1)
    (hconn : ∀ j, ∀ᵐ x ∂ν, inner ℂ (z x) (dz j x) = Complex.I * s j x)
    (hint : Integrable
      (fun x => localChannelKinetic b (z x) (fun j => dz j x) (fun j => u j x) (ψ x)) ν) :
    HasSum (fun a => ∫ x, 1 / 2 * ∑ j,
      ‖channelDerivative b z (dz j) (u j) ψ a x‖ ^ 2 ∂ν)
      (∫ x, localChannelKinetic b (z x) (fun j => dz j x) (fun j => u j x) (ψ x) ∂ν) := by
  apply hasSum_integral_nonnegative
    (fun a => (Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun j _ => (channelDerivative_measurable b hz (hdz j) (hu j) hψ a).norm.pow 2)).const_mul _)
    (fun a => Eventually.of_forall (fun x => mul_nonneg (by norm_num)
      (Finset.sum_nonneg (fun j _ => sq_nonneg _)))) _ hint
  filter_upwards [hunit, ae_all_iff.mpr hconn] with x hx hc
  exact localChannelKinetic_hasSum b _ _ hx hc _ _

/-- Every repaired vector has finite integrated kinetic energy before the
countable integral sum is evaluated. -/
theorem localChannelKinetic_term_integrable {ν : Measure X}
    (b : HilbertBasis ℕ ℂ V) {z : X → V} {dz : J → X → V}
    {u : J → X → H} {ψ : X → H} {s : J → X → ℝ}
    (hz : AEStronglyMeasurable z ν)
    (hdz : ∀ j, AEStronglyMeasurable (dz j) ν)
    (hu : ∀ j, AEStronglyMeasurable (u j) ν)
    (hψ : AEStronglyMeasurable ψ ν)
    (hunit : ∀ᵐ x ∂ν, ‖z x‖ = 1)
    (hconn : ∀ j, ∀ᵐ x ∂ν, inner ℂ (z x) (dz j x) = Complex.I * s j x)
    (hint : Integrable
      (fun x => localChannelKinetic b (z x) (fun j => dz j x) (fun j => u j x) (ψ x)) ν)
    (a : ℕ) :
    Integrable (fun x => 1 / 2 * ∑ j,
      ‖channelDerivative b z (dz j) (u j) ψ a x‖ ^ 2) ν := by
  apply integrable_term_of_nonnegative_hasSum
    (fun a => (Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun j _ => (channelDerivative_measurable b hz (hdz j) (hu j) hψ a).norm.pow 2)).const_mul _)
    (fun a => Eventually.of_forall (fun x => mul_nonneg (by norm_num)
      (Finset.sum_nonneg (fun j _ => sq_nonneg _)))) _ hint a
  filter_upwards [hunit, ae_all_iff.mpr hconn] with x hx hc
  exact localChannelKinetic_hasSum b _ _ hx hc _ _

/-- Each derivative component has finite quadratic integral once the total
channel kinetic density is integrable. -/
theorem channelDerivative_integrable_sq_of_localChannelKinetic {ν : Measure X}
    (b : HilbertBasis ℕ ℂ V) {z : X → V} {dz : J → X → V}
    {u : J → X → H} {ψ : X → H} {s : J → X → ℝ}
    (hz : AEStronglyMeasurable z ν)
    (hdz : ∀ j, AEStronglyMeasurable (dz j) ν)
    (hu : ∀ j, AEStronglyMeasurable (u j) ν)
    (hψ : AEStronglyMeasurable ψ ν)
    (hunit : ∀ᵐ x ∂ν, ‖z x‖ = 1)
    (hconn : ∀ j, ∀ᵐ x ∂ν, inner ℂ (z x) (dz j x) = Complex.I * s j x)
    (hint : Integrable
      (fun x => localChannelKinetic b (z x) (fun j => dz j x) (fun j => u j x) (ψ x)) ν)
    (a : ℕ) (j : J) :
    Integrable (fun x => ‖channelDerivative b z (dz j) (u j) ψ a x‖ ^ 2) ν := by
  have hi := localChannelKinetic_term_integrable b hz hdz hu hψ hunit hconn hint a
  apply (hi.const_mul 2).mono'
    ((channelDerivative_measurable b hz (hdz j) (hu j) hψ a).norm.pow 2)
  filter_upwards with x
  change ‖‖channelDerivative b z (dz j) (u j) ψ a x‖ ^ 2‖ ≤
    2 * (1 / 2 * ∑ i, ‖channelDerivative b z (dz i) (u i) ψ a x‖ ^ 2)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hj := Finset.single_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset J)) =>
      sq_nonneg ‖channelDerivative b z (dz i) (u i) ψ a x‖) (Finset.mem_univ j)
  change ‖channelDerivative b z (dz j) (u j) ψ a x‖ ^ 2 ≤
    2 * (1 / 2 * ∑ i, ‖channelDerivative b z (dz i) (u i) ψ a x‖ ^ 2)
  linarith

/-- The local majorant used for assembling the repaired operator. -/
noncomputable def localKineticMajorant (source mass Z : Q → ℝ) (C e R : ℝ) (q : Q) : ℝ :=
  source q + C * (e ^ 2 * R ^ 2 * (mass q * Z q ^ 2) + e * (mass q * Z q))

omit [MeasurableSpace Q] in
theorem localKineticMajorant_nonneg {source p Z : Q → ℝ} {C e R : ℝ} {q : Q}
    (hsource : 0 ≤ source q) (hp : 0 ≤ p q) (hZ : 0 ≤ Z q)
    (hC : 0 ≤ C) (he : 0 ≤ e) :
    0 ≤ localKineticMajorant source p Z C e R q := by
  unfold localKineticMajorant
  positivity

/-- Both integrability and the quantitative integral bound of the explicit
majorant follow from source integrability and the local field moments. -/
theorem localKineticMajorant_integrable_and_le {μ : Measure Q}
    {source p Z : Q → ℝ} {C CZ e R k B : ℝ}
    (hC : 0 ≤ C) (hCZ : 0 ≤ CZ) (he : 0 ≤ e) (hk : 0 ≤ k) (hB : 0 ≤ B)
    (hp : ∀ q, 0 ≤ p q) (hZ : ∀ q, 0 ≤ Z q)
    (hpm : AEStronglyMeasurable p μ) (hZm : AEStronglyMeasurable Z μ)
    (hsource : Integrable source μ) (hpi : Integrable p μ)
    (hsecond : Integrable (fun q => p q * Z q ^ 2) μ)
    (hsecondbound : ∫ q, p q * Z q ^ 2 ∂μ ≤ CZ * k ^ 2 * B) :
    Integrable (localKineticMajorant source p Z C e R) μ ∧
    (∫ q, localKineticMajorant source p Z C e R q ∂μ) ≤
      (∫ q, source q ∂μ) +
        C * max CZ (Real.sqrt CZ) * e ^ 2 * k ^ 2 * R ^ 2 * B +
        C * max CZ (Real.sqrt CZ) * e * k * Real.sqrt ((∫ q, p q ∂μ) * B) := by
  let rem : Q → ℝ := fun q => C *
    (e ^ 2 * R ^ 2 * (p q * Z q ^ 2) + e * (p q * Z q))
  have hrm : AEStronglyMeasurable rem μ :=
    (((hpm.mul (hZm.pow 2)).const_mul _).add ((hpm.mul hZm).const_mul e)).const_mul C
  have hr0 : ∀ᵐ q ∂μ, 0 ≤ rem q := Eventually.of_forall (fun q => by
    dsimp [rem]
    have := hp q
    have := hZ q
    positivity)
  obtain ⟨hri, hrbound⟩ := Gaussian.integrated_repair_cost_from_moments
    hC hCZ he hk hB hp hZ hpm hZm hpi hsecond hsecondbound hrm hr0
    (Eventually.of_forall (fun _ => le_rfl))
  refine ⟨hsource.add hri, ?_⟩
  change (∫ q, source q + rem q ∂μ) ≤ _
  rw [integral_add hsource hri]
  linarith

/-- A measurable family of actual repair channels has the explicit local
majorant above. Its integrability and integrated cost are consequences of
the source energies, lift derivative estimate and field moments.

The source mass and source kinetic energy are their actual fibre integrals.
The product-rule expression is the one used by `channelDerivative`.
-/
theorem local_channel_cost_from_moments {μ : Measure Q} {ν : Measure X}
    [SFinite μ] [SFinite ν]
    (b : HilbertBasis ℕ ℂ V) {z : Q × X → V} {dz : J → Q × X → V}
    {u : J → Q × X → H} {ψ : Q × X → H} {s : J → Q × X → ℝ}
    {Z : Q → ℝ} {C CZ e R k B : ℝ}
    (hC : 0 ≤ C) (hCZ : 0 ≤ CZ) (he : 0 ≤ e) (hk : 0 ≤ k) (hB : 0 ≤ B)
    (hz : AEStronglyMeasurable z (μ.prod ν))
    (hdz : ∀ j, AEStronglyMeasurable (dz j) (μ.prod ν))
    (hu : ∀ j, AEStronglyMeasurable (u j) (μ.prod ν))
    (hψ : AEStronglyMeasurable ψ (μ.prod ν))
    (hs : ∀ j, AEStronglyMeasurable (s j) (μ.prod ν))
    (hunit : ∀ᵐ qx ∂μ.prod ν, ‖z qx‖ = 1)
    (hconn : ∀ j, ∀ᵐ qx ∂μ.prod ν,
      inner ℂ (z qx) (dz j qx) = Complex.I * s j qx)
    (hsource : Integrable
      (fun qx => localShiftedKinetic (fun j => u j qx) (ψ qx) (fun j => s j qx)) (μ.prod ν))
    (hmass : Integrable (fun qx => ‖ψ qx‖ ^ 2) (μ.prod ν))
    (hZ : ∀ q, 0 ≤ Z q) (hZm : AEStronglyMeasurable Z μ)
    (hmetric : ∀ᵐ qx ∂μ.prod ν, ∑ j, ‖dz j qx‖ ^ 2 ≤
      2 * C * (e ^ 2 * R ^ 2 * Z qx.1 ^ 2 + e * Z qx.1))
    (hsecond : Integrable
      (fun q => (∫ x, ‖ψ (q, x)‖ ^ 2 ∂ν) * Z q ^ 2) μ)
    (hsecondbound : (∫ q, (∫ x, ‖ψ (q, x)‖ ^ 2 ∂ν) * Z q ^ 2 ∂μ) ≤
      CZ * k ^ 2 * B) :
    let p : Q → ℝ := fun q => ∫ x, ‖ψ (q, x)‖ ^ 2 ∂ν
    let source : Q → ℝ := fun q =>
      ∫ x, localShiftedKinetic (fun j => u j (q, x)) (ψ (q, x)) (fun j => s j (q, x)) ∂ν
    let output : Q → ℝ := fun q =>
      ∫ x, localChannelKinetic b (z (q, x)) (fun j => dz j (q, x))
        (fun j => u j (q, x)) (ψ (q, x)) ∂ν
    let term : ℕ → Q → ℝ := fun a q => ∫ x, 1 / 2 * ∑ j,
      ‖channelDerivative b (fun y => z (q, y)) (fun y => dz j (q, y))
        (fun y => u j (q, y)) (fun y => ψ (q, y)) a x‖ ^ 2 ∂ν
    Integrable (localKineticMajorant source p Z C e R) μ ∧
    (∀ᵐ q ∂μ, HasSum (fun a => term a q) (output q)) ∧
    (∀ᵐ q ∂μ, output q ≤ localKineticMajorant source p Z C e R q) ∧
    Integrable output μ ∧
    (∫ q, output q ∂μ) ≤ (∫ q, source q ∂μ) +
      C * max CZ (Real.sqrt CZ) * e ^ 2 * k ^ 2 * R ^ 2 * B +
      C * max CZ (Real.sqrt CZ) * e * k * Real.sqrt ((∫ q, p q ∂μ) * B) := by
  dsimp only
  let p : Q → ℝ := fun q => ∫ x, ‖ψ (q, x)‖ ^ 2 ∂ν
  let source : Q → ℝ := fun q =>
    ∫ x, localShiftedKinetic (fun j => u j (q, x)) (ψ (q, x)) (fun j => s j (q, x)) ∂ν
  let output : Q → ℝ := fun q =>
    ∫ x, localChannelKinetic b (z (q, x)) (fun j => dz j (q, x))
      (fun j => u j (q, x)) (ψ (q, x)) ∂ν
  let term : ℕ → Q → ℝ := fun a q => ∫ x, 1 / 2 * ∑ j,
    ‖channelDerivative b (fun y => z (q, y)) (fun y => dz j (q, y))
      (fun y => u j (q, y)) (fun y => ψ (q, y)) a x‖ ^ 2 ∂ν
  have hp : ∀ q, 0 ≤ p q := fun q => integral_nonneg (fun x => sq_nonneg _)
  have hpi : Integrable p μ := hmass.integral_prod_left
  have hsi : Integrable source μ := hsource.integral_prod_left
  obtain ⟨hcap, hcapbound⟩ := localKineticMajorant_integrable_and_le
    hC hCZ he hk hB hp hZ hpi.aestronglyMeasurable hZm hsi hpi hsecond hsecondbound
  have houtm : AEStronglyMeasurable output μ :=
    (localChannelKinetic_aestronglyMeasurable b hdz hu hψ hs hunit hconn).integral_prod_right'
  have hlocal : ∀ᵐ q ∂μ,
      Integrable (fun x => localChannelKinetic b (z (q, x)) (fun j => dz j (q, x))
        (fun j => u j (q, x)) (ψ (q, x))) ν ∧
      output q ≤ localKineticMajorant source p Z C e R q := by
    filter_upwards [ae_all_iff.mpr (fun j => (hdz j).prodMk_left),
      ae_all_iff.mpr (fun j => (hu j).prodMk_left), hψ.prodMk_left,
      ae_all_iff.mpr (fun j => (hs j).prodMk_left), ae_ae_of_ae_prod hunit,
      ae_all_iff.mpr (fun j => ae_ae_of_ae_prod (hconn j)),
      hsource.prod_right_ae, hmass.prod_right_ae, ae_ae_of_ae_prod hmetric]
      with q hdzq huq hψq hsq hunitq hconnq hsourceq hmassq hmetricq
    obtain ⟨hi, hb⟩ := localChannelKinetic_integrable_and_le b hdzq huq hψq hsq
      hunitq hconnq hsourceq hmassq hmetricq
    refine ⟨hi, ?_⟩
    change output q ≤ source q +
      1 / 2 * (2 * C * (e ^ 2 * R ^ 2 * Z q ^ 2 + e * Z q)) * p q at hb
    calc
      output q ≤ _ := hb
      _ = localKineticMajorant source p Z C e R q := by
        unfold localKineticMajorant
        ring
  have hbound := hlocal.mono (fun _ hq => hq.2)
  have hseries : ∀ᵐ q ∂μ, HasSum (fun a => term a q) (output q) := by
    filter_upwards [hz.prodMk_left,
      ae_all_iff.mpr (fun j => (hdz j).prodMk_left),
      ae_all_iff.mpr (fun j => (hu j).prodMk_left), hψ.prodMk_left,
      ae_ae_of_ae_prod hunit, ae_all_iff.mpr (fun j => ae_ae_of_ae_prod (hconn j)), hlocal]
      with q hzq hdzq huq hψq hunitq hconnq hlocalq
    exact integrated_localChannelKinetic b hzq hdzq huq hψq hunitq hconnq hlocalq.1
  have hout0 : ∀ q, 0 ≤ output q := fun q => integral_nonneg
    (fun x => localChannelKinetic_nonneg b _ _ _ _)
  have houti : Integrable output μ := hcap.mono' houtm
    (hbound.mono (fun q hq => by simpa only [Real.norm_of_nonneg (hout0 q)] using hq))
  exact ⟨hcap, hseries, hbound, houti, (integral_mono_ae houti hcap hbound).trans hcapbound⟩

end GptLean.Repair
