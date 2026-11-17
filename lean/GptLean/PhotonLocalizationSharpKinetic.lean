import GptLean.PhotonLocalizationModel
import GptLean.PhotonLocalizationFormBoundsLifting

/-!
Sharp kinetic control through the actual Kraus and source series.

The vector computation retains the orthogonal discarded-vacuum term.
It permits spatially varying kernels, for which the integrated CCR gives
an upper bound rather than one constant kernel norm times the source mass.
The additive form estimate is then passed through positive spectral sums.
Output finiteness and its real-valued estimate are conclusions.
-/

namespace GptLean.PhotonLocalization

open PhotonLocalizationChannel PhotonLocalizationFormBounds
open Filter Topology Finset
open scoped InnerProductSpace ENNReal

section Vectors

variable {H W ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Fintype ι]

omit [InnerProductSpace ℂ H] in
/-- The integrated creation identity may have a variable kernel norm.
An upper bound on that norm suffices for the same relative field bound. -/
theorem field_norm_le_of_ccr_le (ann cre : H) {q g r s : ℝ}
    (hq : 0 ≤ q) (hg : 0 ≤ g) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hann : ‖ann‖ ≤ q * r)
    (hccr : ‖cre‖ ^ 2 ≤ ‖ann‖ ^ 2 + g ^ 2 * s ^ 2) :
    ‖ann + cre‖ ≤ 2 * q * r + g * s := by
  have hann2 : ‖ann‖ ^ 2 ≤ (q * r) ^ 2 := by
    nlinarith [norm_nonneg ann]
  have hcre : ‖cre‖ ≤ q * r + g * s := by
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith only [hccr, hann2, mul_nonneg (mul_nonneg hq hr) (mul_nonneg hg hs)]
  exact (norm_add_le ann cre).trans (by linarith)

omit [InnerProductSpace ℂ H] in
/-- A uniform kernel error controls the integrated field correction.
This works on a configuration-space L² realization and on the extra
spectral-index L² factor of a mixed-state square root. -/
theorem field_norm_le_of_ccr_le_cutoff (ann cre : H) {q g r s ε : ℝ}
    (hq : 0 ≤ q) (hg : 0 ≤ g) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hqε : q ≤ ε) (hgε : g ≤ ε)
    (hann : ‖ann‖ ≤ q * r)
    (hccr : ‖cre‖ ^ 2 ≤ ‖ann‖ ^ 2 + g ^ 2 * s ^ 2) :
    ‖ann + cre‖ ≤ ε * (2 * r + s) := by
  have h := field_norm_le_of_ccr_le ann cre hq hg hr hs hann hccr
  nlinarith [mul_le_mul_of_nonneg_right hqε hr,
    mul_le_mul_of_nonneg_right hgε hs]

/-- The dilation identity determines the localized kinetic square.
The vacuum vector may have any direction and its variance may vary
spatially. Its orthogonality and norm bound are used explicitly. -/
theorem dilation_component_bound (U : H →ₗᵢ[ℂ] W)
    (d field : H) (noise localized : W) {charge ε B mass : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hmass : 0 ≤ mass)
    (hfield : ‖field‖ ≤ ε * B)
    (hnoise : ‖noise‖ ^ 2 ≤ charge ^ 2 * ε ^ 2 * mass)
    (hidentity : localized = U (d + (charge : ℂ) • field) + noise)
    (horthogonal : ⟪U (d + (charge : ℂ) • field), noise⟫_ℂ = 0) :
    ‖localized‖ ^ 2 ≤ ‖d‖ ^ 2 + 2 * |charge| * ‖d‖ * B * ε +
      (charge ^ 2 * B ^ 2 + charge ^ 2 * mass) * ε ^ 2 := by
  rw [hidentity, vacuum_norm_sq _ _ horthogonal, U.norm_map]
  have h := covariant_component_bound d field (e := charge) hε hB hmass
    hfield (show |ε| ≤ ε by rw [abs_of_nonneg hε])
  linarith only [h, hnoise]

/-- The original energy keeps coefficient one. The source control is
homogeneous in the vector, so it can be summed over an arbitrary spectral
decomposition without normalizing its individual vectors. -/
theorem dilation_kinetic_bound (U : H →ₗᵢ[ℂ] W)
    (d field : ι → H) (noise localized : ι → W)
    {charge ε B K control : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hcontrol : 0 ≤ control)
    (hfield : ∀ i, ‖field i‖ ≤ ε * (B * Real.sqrt control))
    (hnoise : ∀ i, ‖noise i‖ ^ 2 ≤ charge ^ 2 * ε ^ 2 * control)
    (hderivative : ∑ i, ‖d i‖ ≤ K * Real.sqrt control)
    (hidentity : ∀ i, localized i = U (d i + (charge : ℂ) • field i) + noise i)
    (horthogonal : ∀ i, ⟪U (d i + (charge : ℂ) • field i), noise i⟫_ℂ = 0) :
    (1 / 2 : ℝ) * ∑ i, ‖localized i‖ ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i, ‖d i‖ ^ 2 +
        (|charge| * B * K * ε +
          (Fintype.card ι : ℝ) / 2 * (charge ^ 2 * B ^ 2 + charge ^ 2) * ε ^ 2) *
          control := by
  have hsum := sum_le_sum (s := (univ : Finset ι)) fun i _ =>
    dilation_component_bound U (d i) (field i) (noise i) (localized i)
      hε (mul_nonneg hB (Real.sqrt_nonneg _)) hcontrol (hfield i) (hnoise i)
      (hidentity i) (horthogonal i)
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
    ← mul_sum, ← sum_mul] at hsum
  have hcross := mul_le_mul_of_nonneg_left hderivative
    (show 0 ≤ 2 * |charge| * (B * Real.sqrt control) * ε by positivity)
  ring_nf at hsum hcross ⊢
  simp only [Real.sq_sqrt hcontrol] at hsum hcross
  linarith only [hsum, hcross]

end Vectors

section Channel

variable {H T ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T] [Fintype ι]
  {A : Gaussian.RankOneData H T} {Tr : RemovalState.PositiveTraceData T}

/-- The Kraus-coordinate quadratic form has exactly the norm of its
dilated derivative. This proves the pure channel form identity by
Parseval and positive monotone trace summation. -/
theorem pure_kinetic_expectation
    (kinetic : RemovalState.PositiveForm Tr) (hpositive : A.positive ⊆ Tr.positive)
    (U : KrausIsometry H) (v : H) (derivative : ι → lp (fun _ : ℕ => H) 2)
    (hevaluation : ∀ a, kinetic.expectation (A.rankOne (U v a)) =
      ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i, ‖derivative i a‖ ^ 2)) :
    kinetic.expectation (pure A U v) =
      ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i, ‖derivative i‖ ^ 2) := by
  have hs (i : ι) : HasSum (fun a => ‖derivative i a‖ ^ 2) (‖derivative i‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (derivative i)
  have hsum : HasSum (fun a => (1 / 2 : ℝ) * ∑ i, ‖derivative i a‖ ^ 2)
      ((1 / 2 : ℝ) * ∑ i, ‖derivative i‖ ^ 2) :=
    (hasSum_sum fun i _ => hs i).mul_left (1 / 2)
  rw [NormalTraceData.pure_expectation kinetic hpositive U v]
  simp_rw [hevaluation]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun a => by positivity) hsum.summable,
    hsum.tsum_eq]

/-- Additive sharp form bounds lift through the same normal channel.
The source control is only required finite on the supplied state. Each
spectral vector's control is proved finite before invoking the vector
estimate. No finiteness of the output is assumed. -/
theorem channel_form_add_le_of_finite
    (N : NormalTraceData A) (output original control : RemovalState.PositiveForm Tr)
    (hpositive : A.positive ⊆ Tr.positive) (U : KrausIsometry H) (C : ℝ≥0∞)
    (hvector : ∀ v, control.expectation (A.rankOne v) < ⊤ →
      output.expectation (pure A U v) ≤ original.expectation (A.rankOne v) +
        C * control.expectation (A.rankOne v))
    {x : T} (hx : x ∈ A.positive) (hfinite : control.expectation x < ⊤) :
    output.expectation (N.extend U x) ≤ original.expectation x + C * control.expectation x := by
  obtain ⟨v, hv⟩ := N.positive_decomposition x hx
  have hsource (E : RemovalState.PositiveForm Tr) :
      E.expectation x = ∑' n, E.expectation (A.rankOne (v n)) := by
    rw [← hv.tsum_eq, E.expectation_tsum hv.summable
      (fun n => hpositive (A.rankOne_positive (v n)))]
  have hvfinite (n : ℕ) : control.expectation (A.rankOne (v n)) < ⊤ := by
    apply lt_of_le_of_lt (ENNReal.le_tsum n) _
    rwa [← hsource control]
  have hout := N.extend_hasSum U hv
  rw [← hout.tsum_eq, output.expectation_tsum hout.summable
    (fun n => hpositive (pure_positive A U (v n))),
    hsource original, hsource control, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun n => hvector (v n) (hvfinite n)

end Channel

end GptLean.PhotonLocalization
