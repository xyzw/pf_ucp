import GptLean.PhysicalPolarizationFrame
import GptLean.Gaussian.FieldMoments

/-!
The article cutoff supplies a single polarization-independent profile.
Its two moments are the article's three-dimensional cutoff integrals,
and dominate every component of the physical field kernel.
-/

noncomputable section

namespace GptLean.PhysicalPolarization

open MeasureTheory Gaussian PhysicalFock
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

namespace ArticleCutoff

variable (χ : ArticleCutoff)

def profileReal (p : PhotonMode) : ℝ := ‖χ.value (-p.1)‖ ^ 2 / 2

def profile (p : PhotonMode) : ℝ≥0∞ := ENNReal.ofReal (χ.profileReal p)

theorem profileReal_nonneg (p : PhotonMode) : 0 ≤ χ.profileReal p := by
  unfold profileReal
  positivity

theorem profileReal_measurable : Measurable χ.profileReal :=
  (((χ.measurable.comp measurable_fst.neg).norm).pow_const 2).div_const 2

theorem profile_measurable : Measurable χ.profile :=
  χ.profileReal_measurable.ennreal_ofReal

theorem profileReal_integrable : Integrable χ.profileReal photonMeasure := by
  exact (((Measure.measurePreserving_neg volume).integrable_comp_of_integrable
    χ.ultraviolet).comp_fst (Measure.count : Measure (Fin 2))).div_const 2

theorem profileReal_inversefrequency_integrable :
    Integrable (fun p => (1 / ‖p.1‖) * χ.profileReal p) photonMeasure := by
  have h := (((Measure.measurePreserving_neg volume).integrable_comp_of_integrable
    χ.infrared).comp_fst (Measure.count : Measure (Fin 2))).div_const 2
  unfold photonMeasure
  apply h.congr
  exact ae_of_all _ fun p => by
    simp only [profileReal, Function.comp_def, norm_neg]
    ring

theorem profile_total_lt_top : (∫⁻ p, χ.profile p ∂photonMeasure) < ⊤ := by
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ χ.profileReal_nonneg)).mp
    χ.profileReal_integrable.2

theorem profile_inversefrequency_lt_top :
    (∫⁻ p, χ.profile p * ENNReal.ofReal (1 / ‖p.1‖) ∂photonMeasure) < ⊤ := by
  have h := (hasFiniteIntegral_iff_ofReal
    (ae_of_all _ (fun p : PhotonMode =>
      mul_nonneg (by positivity : 0 ≤ 1 / ‖p.1‖) (χ.profileReal_nonneg p)))).mp
    χ.profileReal_inversefrequency_integrable.2
  have he : (fun p : PhotonMode => χ.profile p * ENNReal.ofReal (1 / ‖p.1‖)) =
      fun p => ENNReal.ofReal ((1 / ‖p.1‖) * χ.profileReal p) := by
    funext p
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / ‖p.1‖)]
    exact mul_comm _ _
  rw [he]
  exact h

theorem profile_bsq_eq (κ : ℝ) :
    CutoffProfile.bsq photonMeasure (fun p => ‖p.1‖) χ.profile κ =
      ∫ p in {p : PhotonMode | ‖p.1‖ < κ}, χ.profileReal p ∂photonMeasure := by
  exact (integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ χ.profileReal_nonneg)
    χ.profileReal_integrable.aestronglyMeasurable.restrict).symm

theorem profile_asq_eq (κ : ℝ) :
    CutoffProfile.asq photonMeasure (fun p => ‖p.1‖) χ.profile κ =
      ∫ p in {p : PhotonMode | ‖p.1‖ < κ},
        (1 / ‖p.1‖) * χ.profileReal p ∂photonMeasure := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun p : PhotonMode =>
      mul_nonneg (by positivity : 0 ≤ 1 / ‖p.1‖) (χ.profileReal_nonneg p)))
    χ.profileReal_inversefrequency_integrable.aestronglyMeasurable.restrict]
  unfold CutoffProfile.asq profile
  congr 1
  apply lintegral_congr
  intro p
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / ‖p.1‖), mul_comm]

private theorem integral_photon_half (f : FieldSpace → ℝ) :
    (∫ p : PhotonMode, f (-p.1) / 2 ∂photonMeasure) = ∫ k, f k := by
  unfold photonMeasure
  rw [integral_fun_fst (fun k : FieldSpace => f (-k) / 2)]
  simp only [Measure.count_real_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
    Nat.cast_ofNat, smul_eq_mul]
  rw [integral_div,
    (Measure.measurePreserving_neg volume).integral_comp measurableEmbedding_neg f]
  ring

theorem integral_profileReal :
    (∫ p, χ.profileReal p ∂photonMeasure) = ∫ k, ‖χ.value k‖ ^ 2 := by
  change (∫ p : PhotonMode, ‖χ.value (-p.1)‖ ^ 2 / 2 ∂photonMeasure) = _
  exact integral_photon_half (fun k => ‖χ.value k‖ ^ 2)

theorem integral_profileReal_inversefrequency :
    (∫ p, (1 / ‖p.1‖) * χ.profileReal p ∂photonMeasure) =
      ∫ k, (1 / ‖k‖) * ‖χ.value k‖ ^ 2 := by
  calc
    _ = ∫ p : PhotonMode,
        ((1 / ‖-p.1‖) * ‖χ.value (-p.1)‖ ^ 2) / 2 ∂photonMeasure := by
      apply integral_congr_ae
      exact ae_of_all _ fun p => by
        simp only [profileReal, norm_neg]
        ring
    _ = _ := integral_photon_half (fun k => (1 / ‖k‖) * ‖χ.value k‖ ^ 2)

theorem profile_bsq_article (κ : ℝ) :
    CutoffProfile.bsq photonMeasure (fun p => ‖p.1‖) χ.profile κ =
      ∫ k in {k : FieldSpace | ‖k‖ < κ}, ‖χ.value k‖ ^ 2 := by
  have hs : MeasurableSet {k : FieldSpace | ‖k‖ < κ} :=
    measurable_norm measurableSet_Iio
  have hp : MeasurableSet {p : PhotonMode | ‖p.1‖ < κ} :=
    measurable_fst.norm measurableSet_Iio
  rw [χ.profile_bsq_eq, ← integral_indicator hp, ← integral_indicator hs]
  have h := integral_photon_half
    ({k : FieldSpace | ‖k‖ < κ}.indicator (fun k => ‖χ.value k‖ ^ 2))
  convert h using 1
  apply integral_congr_ae
  exact ae_of_all _ fun p => by
    by_cases hκ : ‖p.1‖ < κ <;> simp [profileReal, hκ]

theorem profile_asq_article (κ : ℝ) :
    CutoffProfile.asq photonMeasure (fun p => ‖p.1‖) χ.profile κ =
      ∫ k in {k : FieldSpace | ‖k‖ < κ}, (1 / ‖k‖) * ‖χ.value k‖ ^ 2 := by
  have hs : MeasurableSet {k : FieldSpace | ‖k‖ < κ} :=
    measurable_norm measurableSet_Iio
  have hp : MeasurableSet {p : PhotonMode | ‖p.1‖ < κ} :=
    measurable_fst.norm measurableSet_Iio
  rw [χ.profile_asq_eq, ← integral_indicator hp, ← integral_indicator hs]
  have h := integral_photon_half
    ({k : FieldSpace | ‖k‖ < κ}.indicator (fun k => (1 / ‖k‖) * ‖χ.value k‖ ^ 2))
  convert h using 1
  apply integral_congr_ae
  exact ae_of_all _ fun p => by
    by_cases hκ : ‖p.1‖ < κ <;> simp [profileReal, hκ, mul_div_assoc]

end ArticleCutoff

variable (F : Frame) (χ : ArticleCutoff)

theorem base_norm_sq_le_profile (i : Fin 3) (p : PhotonMode) :
    ‖base F χ i p‖ ^ 2 ≤ χ.profileReal p := by
  have he := pow_le_pow_left₀ (abs_nonneg (F.epsilon p.1 p.2 i))
    (F.epsilon_component_bound p.1 p.2 i) 2
  simp only [one_pow] at he
  simp only [base, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), ArticleCutoff.profileReal]
  exact div_le_div_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right he (sq_nonneg _))
    (by norm_num)

theorem softBase_integral_le_bsq (i : Fin 3) (κ : ℝ) :
    (∫ p, ‖softBase Prod.fst κ (base F χ i) p‖ ^ 2 ∂photonMeasure) ≤
      CutoffProfile.bsq photonMeasure (fun p => ‖p.1‖) χ.profile κ := by
  have he := softBase_weighted_integral (ν := photonMeasure)
    Prod.fst measurable_fst κ (base F χ i) (fun _ => 1)
  simp only [one_mul] at he
  rw [he, χ.profile_bsq_eq]
  exact integral_mono (base_ultraviolet F χ i).restrict
    χ.profileReal_integrable.restrict (base_norm_sq_le_profile F χ i)

theorem softBase_inversefrequency_integral_le_asq (i : Fin 3) (κ : ℝ) :
    (∫ p, (1 / ‖p.1‖) * ‖softBase Prod.fst κ (base F χ i) p‖ ^ 2 ∂photonMeasure) ≤
      CutoffProfile.asq photonMeasure (fun p => ‖p.1‖) χ.profile κ := by
  rw [softBase_weighted_integral Prod.fst measurable_fst, χ.profile_asq_eq]
  exact integral_mono (base_infrared F χ i).restrict
    χ.profileReal_inversefrequency_integrable.restrict
    (fun p => mul_le_mul_of_nonneg_left (base_norm_sq_le_profile F χ i p) (by positivity))

end GptLean.PhysicalPolarization
