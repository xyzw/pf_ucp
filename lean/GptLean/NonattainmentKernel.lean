import GptLean.PhysicalCouplingKernelNorm
import GptLean.NonattainmentCutoff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Quantitative spatial continuity of the actual article form factors, in both
the ordinary and inverse-frequency L² norms. The estimates use only the two
cutoff moments and the bounded oscillatory multiplier. They require neither
a derivative of the cutoff nor a higher ultraviolet moment.
-/

noncomputable section

namespace GptLean.Nonattainment

open MeasureTheory Gaussian PhysicalFock PhysicalPolarization
  PhotonLocalizationPhysicalKernels
open scoped InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 400000

theorem fieldPhase_sub (k x y : FieldSpace) :
    fieldPhase k x - fieldPhase k y =
      (fieldPhase k (x - y) - 1) * fieldPhase k y := by
  have h : fieldPhase k (x - y) * fieldPhase k y = fieldPhase k x := by
    rw [fieldPhase, fieldPhase, ← Complex.exp_add]
    congr 1
    simp only [inner_sub_right, Complex.ofReal_sub, Complex.ofReal_neg]
    ring
  rw [sub_mul, h, one_mul]

theorem norm_fieldPhase_sub_le (k x y : FieldSpace) :
    ‖fieldPhase k x - fieldPhase k y‖ ≤ ‖k‖ * ‖x - y‖ := by
  rw [fieldPhase_sub, norm_mul, norm_fieldPhase, mul_one]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -inner ℝ k (x - y))
  have he : fieldPhase k (x - y) =
      Complex.exp (Complex.I * ((-inner ℝ k (x - y) : ℝ) : ℂ)) := by
    unfold fieldPhase
    rw [mul_comm]
  rw [he]
  exact h.trans (by simpa only [norm_neg] using norm_inner_le_norm k (x - y))

theorem norm_fieldPhase_sub_le_cutoff (k x y : FieldSpace) :
    ‖fieldPhase k x - fieldPhase k y‖ ≤
      2 * cutoffMultiplier (fun k : FieldSpace => ‖k‖) ‖x - y‖ k := by
  have htwo : ‖fieldPhase k x - fieldPhase k y‖ ≤ 2 := by
    simpa only [norm_fieldPhase, one_add_one_eq_two] using
      norm_sub_le (fieldPhase k x) (fieldPhase k y)
  have hlin := norm_fieldPhase_sub_le k x y
  simp only [cutoffMultiplier, abs_of_nonneg (norm_nonneg _)]
  by_cases h : 1 ≤ ‖x - y‖ * ‖k‖
  · rw [min_eq_left h]
    simpa using htwo
  · rw [min_eq_right (le_of_not_ge h)]
    nlinarith [mul_nonneg (norm_nonneg k) (norm_nonneg (x - y))]

def weightedKernelBase (F : Frame) (χ : ArticleCutoff) (infrared : Bool)
    (i : Fin 3) : PhotonMode → ℂ :=
  if infrared then infraredBase Prod.fst (base F χ i) else base F χ i

theorem weightedKernelBase_measurable (F : Frame) (χ : ArticleCutoff)
    (infrared : Bool) (i : Fin 3) : Measurable (weightedKernelBase F χ infrared i) := by
  cases infrared
  · exact base_measurable F χ i
  · exact measurable_infraredBase Prod.fst measurable_fst _ (base_measurable F χ i)

theorem weightedKernelBase_integrable (F : Frame) (χ : ArticleCutoff)
    (infrared : Bool) (i : Fin 3) :
    Integrable (fun p => ‖weightedKernelBase F χ infrared i p‖ ^ 2) photonMeasure := by
  cases infrared
  · exact base_ultraviolet F χ i
  · exact infraredBase_integrable Prod.fst _ (base_infrared F χ i)

def weightedKernelProfile (χ : ArticleCutoff) (infrared : Bool) (p : PhotonMode) : ℝ :=
  if infrared then (1 / ‖p.1‖) * χ.profileReal p else χ.profileReal p

theorem weightedKernelProfile_nonneg (χ : ArticleCutoff) (infrared : Bool) (p : PhotonMode) :
    0 ≤ weightedKernelProfile χ infrared p := by
  cases infrared
  · exact χ.profileReal_nonneg p
  · exact mul_nonneg (by positivity) (χ.profileReal_nonneg p)

theorem weightedKernelProfile_integrable (χ : ArticleCutoff) (infrared : Bool) :
    Integrable (weightedKernelProfile χ infrared) photonMeasure := by
  cases infrared
  · exact χ.profileReal_integrable
  · exact χ.profileReal_inversefrequency_integrable

theorem weightedKernelBase_sum (F : Frame) (χ : ArticleCutoff)
    (infrared : Bool) (p : PhotonMode) :
    (∑ i : Fin 3, ‖weightedKernelBase F χ infrared i p‖ ^ 2) =
      weightedKernelProfile χ infrared p := by
  cases infrared
  · exact PhysicalCouplingKernelNorm.base_sum_norm_sq F χ p
  · simp only [weightedKernelBase, ↓reduceIte, infraredBase_norm_sq,
      ← Finset.mul_sum, PhysicalCouplingKernelNorm.base_sum_norm_sq, weightedKernelProfile]

private theorem integral_photon_half (f : FieldSpace → ℝ) :
    (∫ p : PhotonMode, f (-p.1) / 2 ∂photonMeasure) = ∫ k, f k := by
  unfold photonMeasure
  rw [integral_fun_fst (fun k : FieldSpace => f (-k) / 2)]
  simp only [Measure.count_real_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
    Nat.cast_ofNat, smul_eq_mul]
  rw [integral_div,
    (Measure.measurePreserving_neg volume).integral_comp measurableEmbedding_neg f]
  ring

theorem weightedKernelProfile_integral (χ : ArticleCutoff) (infrared : Bool) :
    (∫ p, weightedKernelProfile χ infrared p ∂photonMeasure) =
      ∫ k, cutoffWeight χ infrared k := by
  cases infrared
  · exact χ.integral_profileReal
  · exact χ.integral_profileReal_inversefrequency

theorem cutoff_weightedKernelProfile_integrable (χ : ArticleCutoff)
    (infrared : Bool) (ℓ : ℝ) :
    Integrable (fun p : PhotonMode =>
      cutoffMultiplier (fun k : FieldSpace => ‖k‖) ℓ p.1 ^ 2 *
        weightedKernelProfile χ infrared p) photonMeasure := by
  apply (weightedKernelProfile_integrable χ infrared).mono'
  · have hp := (weightedKernelProfile_integrable χ infrared).aestronglyMeasurable
    have hm : Measurable (fun p : PhotonMode =>
        cutoffMultiplier (fun k : FieldSpace => ‖k‖) ℓ p.1 ^ 2) := by
      unfold cutoffMultiplier
      fun_prop
    exact hm.aestronglyMeasurable.mul hp
  · exact ae_of_all _ fun p => by
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
        (weightedKernelProfile_nonneg χ infrared p))]
      exact (mul_le_mul_of_nonneg_right
        (cutoffMultiplier_sq_le_one (fun k : FieldSpace => ‖k‖) ℓ p.1)
        (weightedKernelProfile_nonneg χ infrared p)).trans_eq (one_mul _)

theorem cutoff_weightedKernelProfile_integral (χ : ArticleCutoff)
    (infrared : Bool) (ℓ : ℝ) :
    (∫ p : PhotonMode, cutoffMultiplier (fun k : FieldSpace => ‖k‖) ℓ p.1 ^ 2 *
      weightedKernelProfile χ infrared p ∂photonMeasure) =
      cutoffModulus χ infrared ℓ ^ 2 := by
  have hs : cutoffModulus χ infrared ℓ ^ 2 =
      ∫ k, cutoffMultiplier (fun k : FieldSpace => ‖k‖) ℓ k ^ 2 *
        cutoffWeight χ infrared k := by
    exact Real.sq_sqrt (integral_nonneg fun k =>
      mul_nonneg (sq_nonneg _) (cutoffWeight_nonneg χ infrared k))
  rw [hs]
  calc
    _ = ∫ p : PhotonMode,
        (cutoffMultiplier (fun k : FieldSpace => ‖k‖) ℓ (-p.1) ^ 2 *
          cutoffWeight χ infrared (-p.1)) / 2 ∂photonMeasure := by
      apply integral_congr_ae
      exact ae_of_all _ fun p => by
        cases infrared <;>
          simp only [weightedKernelProfile, cutoffWeight, Bool.false_eq_true,
            ↓reduceIte, ArticleCutoff.profileReal, cutoffMultiplier, norm_neg] <;> ring
    _ = _ := integral_photon_half (fun k =>
      cutoffMultiplier (fun k : FieldSpace => ‖k‖) ℓ k ^ 2 * cutoffWeight χ infrared k)

/-- The ordinary or inverse-frequency physical field component in momentum L². -/
def weightedFieldKernel (F : Frame) (χ : ArticleCutoff) (infrared : Bool)
    (i : Fin 3) (x : FieldSpace) : Lp ℂ 2 photonMeasure :=
  momentumKernelL2 Prod.fst measurable_fst (weightedKernelBase F χ infrared i)
    (weightedKernelBase_measurable F χ infrared i)
    (weightedKernelBase_integrable F χ infrared i) x

theorem weightedFieldKernel_false (F : Frame) (χ : ArticleCutoff)
    (i : Fin 3) (x : FieldSpace) :
    weightedFieldKernel F χ false i x = (formFactors F χ).fourierKernel (i, x) := rfl

theorem weightedFieldKernel_true (F : Frame) (χ : ArticleCutoff)
    (i : Fin 3) (x : FieldSpace) :
    weightedFieldKernel F χ true i x = (formFactors F χ).weightedFourierKernel (i, x) := rfl

theorem weightedFieldKernel_continuous (F : Frame) (χ : ArticleCutoff)
    (infrared : Bool) (i : Fin 3) : Continuous (weightedFieldKernel F χ infrared i) :=
  continuous_momentumKernelL2 Prod.fst measurable_fst _
    (weightedKernelBase_measurable F χ infrared i)
    (weightedKernelBase_integrable F χ infrared i)

theorem weightedFieldKernel_sum_norm_sq (F : Frame) (χ : ArticleCutoff)
    (infrared : Bool) (x : FieldSpace) :
    (∑ i : Fin 3, ‖weightedFieldKernel F χ infrared i x‖ ^ 2) =
      ∫ k, cutoffWeight χ infrared k := by
  simp only [weightedFieldKernel, momentumKernelL2_norm_sq]
  rw [← integral_finsetSum Finset.univ
    (fun i _ => weightedKernelBase_integrable F χ infrared i)]
  simp only [weightedKernelBase_sum]
  exact weightedKernelProfile_integral χ infrared

theorem weightedFieldKernel_difference_norm_sq (F : Frame) (χ : ArticleCutoff)
    (infrared : Bool) (i : Fin 3) (x y : FieldSpace) :
    ‖weightedFieldKernel F χ infrared i x - weightedFieldKernel F χ infrared i y‖ ^ 2 =
      ∫ p, ‖momentumKernel Prod.fst (weightedKernelBase F χ infrared i) x p -
        momentumKernel Prod.fst (weightedKernelBase F χ infrared i) y p‖ ^ 2 ∂photonMeasure := by
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (weightedFieldKernel F χ infrared i x)
      (weightedFieldKernel F χ infrared i y),
    momentumKernelL2_ae Prod.fst measurable_fst _
      (weightedKernelBase_measurable F χ infrared i)
      (weightedKernelBase_integrable F χ infrared i) x,
    momentumKernelL2_ae Prod.fst measurable_fst _
      (weightedKernelBase_measurable F χ infrared i)
      (weightedKernelBase_integrable F χ infrared i) y] with p hp hx hy
  rw [hp]
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (congrArg₂ (fun z w : ℂ => z - w) hx hy)

/-- The quantitative estimate in the article, summed over all three components. -/
theorem weightedFieldKernel_sum_difference_sq_le (F : Frame) (χ : ArticleCutoff)
    (infrared : Bool) (x y : FieldSpace) :
    (∑ i : Fin 3, ‖weightedFieldKernel F χ infrared i x -
      weightedFieldKernel F χ infrared i y‖ ^ 2) ≤
      4 * cutoffModulus χ infrared ‖x - y‖ ^ 2 := by
  have hi (i : Fin 3) : Integrable (fun p =>
      ‖momentumKernel Prod.fst (weightedKernelBase F χ infrared i) x p -
        momentumKernel Prod.fst (weightedKernelBase F χ infrared i) y p‖ ^ 2)
        photonMeasure := by
    have hm z := momentumKernel_memLp Prod.fst measurable_fst _
      (weightedKernelBase_measurable F χ infrared i)
      (weightedKernelBase_integrable F χ infrared i) z
    exact (memLp_two_iff_integrable_sq_norm
      ((hm x).sub (hm y)).aestronglyMeasurable).mp ((hm x).sub (hm y))
  simp only [weightedFieldKernel_difference_norm_sq]
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  calc
    _ ≤ ∫ p : PhotonMode,
        4 * (cutoffMultiplier (fun k : FieldSpace => ‖k‖) ‖x - y‖ p.1 ^ 2 *
          weightedKernelProfile χ infrared p) ∂photonMeasure := by
      apply integral_mono (integrable_finsetSum _ (fun i _ => hi i))
        ((cutoff_weightedKernelProfile_integrable χ infrared ‖x - y‖).const_mul 4)
      intro p
      simp only [momentumKernel, ← sub_mul, norm_mul, mul_pow, ← Finset.mul_sum,
        weightedKernelBase_sum]
      have hh := norm_fieldPhase_sub_le_cutoff p.1 x y
      have hsq : ‖fieldPhase p.1 x - fieldPhase p.1 y‖ ^ 2 ≤
          4 * cutoffMultiplier (fun k : FieldSpace => ‖k‖) ‖x - y‖ p.1 ^ 2 := by
        nlinarith [norm_nonneg (fieldPhase p.1 x - fieldPhase p.1 y),
          cutoffMultiplier_nonneg (fun k : FieldSpace => ‖k‖) ‖x - y‖ p.1]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hsq
        (weightedKernelProfile_nonneg χ infrared p)
    _ = _ := by rw [integral_const_mul, cutoff_weightedKernelProfile_integral]

theorem weightedFieldKernel_difference_le (F : Frame) (χ : ArticleCutoff)
    (infrared : Bool) (i : Fin 3) (x y : FieldSpace) :
    ‖weightedFieldKernel F χ infrared i x - weightedFieldKernel F χ infrared i y‖ ≤
      2 * cutoffModulus χ infrared ‖x - y‖ := by
  have h := (Finset.single_le_sum (fun j _ => sq_nonneg
    (‖weightedFieldKernel F χ infrared j x - weightedFieldKernel F χ infrared j y‖))
    (Finset.mem_univ i)).trans (weightedFieldKernel_sum_difference_sq_le F χ infrared x y)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num)
    (cutoffModulus_nonneg χ infrared ‖x - y‖))).mp
  nlinarith

theorem cutoffModulus_mono (χ : ArticleCutoff) (infrared : Bool)
    {ℓ L : ℝ} (hℓ : 0 ≤ ℓ) (hℓL : ℓ ≤ L) :
    cutoffModulus χ infrared ℓ ≤ cutoffModulus χ infrared L := by
  apply (sq_le_sq₀ (cutoffModulus_nonneg χ infrared ℓ)
    (cutoffModulus_nonneg χ infrared L)).mp
  rw [← cutoff_weightedKernelProfile_integral, ← cutoff_weightedKernelProfile_integral]
  apply integral_mono (cutoff_weightedKernelProfile_integrable χ infrared ℓ)
    (cutoff_weightedKernelProfile_integrable χ infrared L)
  intro p
  apply mul_le_mul_of_nonneg_right _ (weightedKernelProfile_nonneg χ infrared p)
  apply pow_le_pow_left₀ (cutoffMultiplier_nonneg _ _ _)
  simp only [cutoffMultiplier, abs_of_nonneg hℓ, abs_of_nonneg (hℓ.trans hℓL)]
  exact min_le_min le_rfl (mul_le_mul_of_nonneg_right hℓL (abs_nonneg _))

def cutoffMoment (χ : ArticleCutoff) (infrared : Bool) : ℝ :=
  Real.sqrt (∫ k, cutoffWeight χ infrared k)

theorem cutoffMoment_nonneg (χ : ArticleCutoff) (infrared : Bool) :
    0 ≤ cutoffMoment χ infrared := Real.sqrt_nonneg _

theorem cutoffMoment_sq (χ : ArticleCutoff) (infrared : Bool) :
    cutoffMoment χ infrared ^ 2 = ∫ k, cutoffWeight χ infrared k :=
  Real.sq_sqrt (integral_nonneg (cutoffWeight_nonneg χ infrared))

theorem weightedFieldKernel_norm_le (F : Frame) (χ : ArticleCutoff)
    (infrared : Bool) (i : Fin 3) (x : FieldSpace) :
    ‖weightedFieldKernel F χ infrared i x‖ ≤ cutoffMoment χ infrared := by
  apply (sq_le_sq₀ (norm_nonneg _) (cutoffMoment_nonneg χ infrared)).mp
  rw [cutoffMoment_sq, ← weightedFieldKernel_sum_norm_sq F χ infrared x]
  exact Finset.single_le_sum
    (fun j _ => sq_nonneg (‖weightedFieldKernel F χ infrared j x‖)) (Finset.mem_univ i)

end GptLean.Nonattainment
