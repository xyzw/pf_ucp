import GptLean.PhysicalPFSpatialObservables

/-!
Bounded spatial multiplication caps construct the full nonnegative
potential form on normal traces, including infinite expectations.
-/

noncomputable section

namespace GptLean.PhysicalSpatialPotential

open MeasureTheory PhysicalNormalTrace PhysicalPFSource PhotonLocalization
  PhotonLocalizationChannel RemovalState
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
set_option Elab.async false

variable {X H : Type} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (μ : Measure X) (q : X → ℝ≥0∞) (hq : Measurable q)

def cap (n : ℕ) (x : X) : ℝ := (min (n : ℝ≥0∞) (q x)).toReal

omit [MeasurableSpace X] in
theorem cap_nonneg (n : ℕ) (x : X) : 0 ≤ cap q n x := ENNReal.toReal_nonneg

omit [MeasurableSpace X] in
theorem cap_bound (n : ℕ) (x : X) : |cap q n x| ≤ n := by
  rw [abs_of_nonneg (cap_nonneg q n x)]
  exact (ENNReal.toReal_mono (by simp) (min_le_left (n : ℝ≥0∞) _)).trans_eq (by simp)

include hq in
theorem cap_measurable (n : ℕ) : AEStronglyMeasurable (cap q n) μ :=
  (measurable_const.min hq).ennreal_toReal.aestronglyMeasurable

omit [MeasurableSpace X] in
theorem cap_ofReal (n : ℕ) (x : X) :
    ENNReal.ofReal (cap q n x) = min (n : ℝ≥0∞) (q x) :=
  ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by simp) (min_le_left _ _))

omit [MeasurableSpace X] in
theorem cap_mono (x : X) : Monotone (fun n => cap q n x) := by
  intro n m hnm
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top (by simp) (min_le_left _ _))
    (min_le_min_right _ (by exact_mod_cast hnm))

def operator (n : ℕ) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  realL2Multiplier (cap q n) (cap_measurable μ q hq n) n (ae_of_all _ (cap_bound q n))

theorem operator_ae (n : ℕ) (u : Lp H 2 μ) :
    operator μ q hq n u =ᵐ[μ] fun x => cap q n x • u x :=
  realL2Multiplier_apply _ _ _ _ _

omit [InnerProductSpace ℂ H] in
include hq in
theorem cap_integrable (n : ℕ) (u : Lp H 2 μ) :
    Integrable (fun x => cap q n x * ‖u x‖ ^ 2) μ :=
  ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)).bdd_mul
    (cap_measurable μ q hq n)
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using cap_bound q n x)

theorem operator_inner_real (n : ℕ) (u : Lp H 2 μ) :
    (⟪u, operator μ q hq n u⟫_ℂ).im = 0 := by
  rw [L2.inner_def]
  have hi := Complex.imCLM.integral_comp_comm
    (L2.integrable_inner (𝕜 := ℂ) u (operator μ q hq n u))
  simp only [Complex.imCLM_apply] at hi
  change (∫ x, ⟪u x, operator μ q hq n u x⟫_ℂ ∂μ).im = _
  rw [← hi]
  apply integral_eq_zero_of_ae
  filter_upwards [operator_ae μ q hq n u] with x hx
  rw [hx, inner_smul_right_eq_smul]
  have hz : (⟪u x, u x⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) (u x)
  simp only [Complex.smul_im, hz, smul_zero, Pi.zero_apply]

variable [CompleteSpace H] (B : StandardNormalTraceBackground)

def truncation (n : ℕ) : B.Trace (Lp H 2 μ) →L[ℝ] ℝ :=
  boundedTrace (B.realization (Lp H 2 μ)).functional (operator μ q hq n)

theorem truncation_rankOne (n : ℕ) (u : Lp H 2 μ) :
    truncation μ q hq B n ((B.realization (Lp H 2 μ)).rank.rankOne u) =
      ∫ x, cap q n x * ‖u x‖ ^ 2 ∂μ :=
  boundedTrace_multiplier_rankOne (B.realization (Lp H 2 μ)).functional
    (cap q n) (cap_measurable μ q hq n) n (ae_of_all _ (cap_bound q n)) u

theorem truncation_complex (n : ℕ) (u : Lp H 2 μ) :
    (truncation μ q hq B n ((B.realization (Lp H 2 μ)).rank.rankOne u) : ℂ) =
      ⟪u, operator μ q hq n u⟫_ℂ := by
  apply Complex.ext
  · exact boundedTrace_rankOne (B.realization (Lp H 2 μ)).functional (operator μ q hq n) u
  · exact (operator_inner_real μ q hq n u).symm

def normalForm : PositiveForm (B.traceData (H := Lp H 2 μ)) where
  truncation := truncation μ q hq B
  nonneg n x hx := B.normal.observable_nonneg _ (fun u => by
    rw [truncation_rankOne]
    exact integral_nonneg fun y => mul_nonneg (cap_nonneg q n y) (sq_nonneg _)) hx
  monotone x hx n m hnm := by
    have h := B.normal.observable_nonneg
      (truncation μ q hq B m - truncation μ q hq B n) (fun u => by
        simp only [sub_apply, truncation_rankOne]
        apply sub_nonneg.mpr
        exact integral_mono (cap_integrable μ q hq n u) (cap_integrable μ q hq m u)
          (fun y => mul_le_mul_of_nonneg_right (cap_mono q y hnm) (sq_nonneg _))) hx
    exact sub_nonneg.mp h

theorem normalForm_rankOne (u : Lp H 2 μ) :
    (normalForm μ q hq B).expectation ((B.realization (Lp H 2 μ)).rank.rankOne u) =
      ∫⁻ x, q x * ENNReal.ofReal (‖u x‖ ^ 2) ∂μ := by
  change (⨆ n, ENNReal.ofReal (truncation μ q hq B n
    ((B.realization (Lp H 2 μ)).rank.rankOne u))) = _
  have hn (n : ℕ) : ENNReal.ofReal (truncation μ q hq B n
      ((B.realization (Lp H 2 μ)).rank.rankOne u)) =
      ∫⁻ x, min (n : ℝ≥0∞) (q x) * ENNReal.ofReal (‖u x‖ ^ 2) ∂μ := by
    rw [truncation_rankOne, ofReal_integral_eq_lintegral_ofReal
      (cap_integrable μ q hq n u)
      (ae_of_all _ fun x => mul_nonneg (cap_nonneg q n x) (sq_nonneg _))]
    simp only [ENNReal.ofReal_mul (cap_nonneg q n _), cap_ofReal]
  simp only [hn]
  have hm (n : ℕ) : AEMeasurable
      (fun x => min (n : ℝ≥0∞) (q x) * ENNReal.ofReal (‖u x‖ ^ 2)) μ :=
    (measurable_const.min hq).aemeasurable.mul
      (((Lp.aestronglyMeasurable u).norm.pow 2).aemeasurable.ennreal_ofReal)
  rw [← lintegral_iSup' hm (ae_of_all _ fun x n m hnm =>
    mul_le_mul_of_nonneg_right (min_le_min_right _ (by exact_mod_cast hnm)) bot_le)]
  apply lintegral_congr
  intro x
  rw [← ENNReal.iSup_mul, ← iSup_inf_eq, ENNReal.iSup_natCast, top_inf_eq]

theorem normalForm_source {u : ℕ → Lp H 2 μ} {x : B.Trace (Lp H 2 μ)}
    (hu : HasSum (fun n => (B.realization (Lp H 2 μ)).rank.rankOne (u n)) x) :
    (normalForm μ q hq B).expectation x =
      ∑' n, ∫⁻ y, q y * ENNReal.ofReal (‖u n y‖ ^ 2) ∂μ := by
  rw [← hu.tsum_eq, (normalForm μ q hq B).expectation_tsum hu.summable
    (fun n => (B.realization (Lp H 2 μ)).rank.rankOne_positive (u n))]
  exact tsum_congr fun n => normalForm_rankOne μ q hq B (u n)

end GptLean.PhysicalSpatialPotential
