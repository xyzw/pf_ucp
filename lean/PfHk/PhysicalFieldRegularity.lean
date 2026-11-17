import GptLean.PhysicalDipoleLengthKernels
import GptLean.Gaussian.SpatialFieldDerivative
import GptLean.PhysicalNonattainmentFluxKernel

/-!
The additional ultraviolet hypothesis used for the physical Carleman
estimate. Its consequences below are proved for the actual measurable
polarization kernels, retaining both weighted photon components.
-/

noncomputable section
namespace PfHk.PhysicalFieldRegularity

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalDipoleLengthKernels GptLean.PhotonLocalizationPhysicalKernels
  GptLean.PhysicalNonattainmentFluxKernel Gaussian
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The paper assumes `ωχ ∈ L²`, with `ω(k) = |k|`. -/
def CarlemanUV (χ : ArticleCutoff) : Prop :=
  MemLp (fun k => (‖k‖ : ℂ) * χ.value k) 2 volume

theorem omega_mul_norm_sq (k : FieldSpace) (z : ℂ) :
    ‖(‖k‖ : ℂ) * z‖ ^ 2 = ‖k‖ ^ 2 * ‖z‖ ^ 2 := by
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem carlemanUV_iff_integrable (χ : ArticleCutoff) :
    CarlemanUV χ ↔ Integrable (fun k => ‖k‖ ^ 2 * ‖χ.value k‖ ^ 2) volume := by
  have hm : AEStronglyMeasurable (fun k => (‖k‖ : ℂ) * χ.value k) volume :=
    ((Complex.measurable_ofReal.comp measurable_norm).mul χ.measurable).aestronglyMeasurable
  simpa only [CarlemanUV, omega_mul_norm_sq] using memLp_two_iff_integrable_sq_norm hm

/-- The intermediate `√ω` moment follows from the two endpoint moments. -/
theorem sqrtUV_of_carlemanUV (χ : ArticleCutoff) (hUV : CarlemanUV χ) : UVCondition χ := by
  apply (uv_iff_integrable χ).mpr
  have h := χ.ultraviolet.add ((carlemanUV_iff_integrable χ).mp hUV)
  apply h.mono' ((measurable_norm.mul (χ.measurable.norm.pow_const 2)).aestronglyMeasurable)
  filter_upwards with k
  change ‖‖k‖ * ‖χ.value k‖ ^ 2‖ ≤ ‖χ.value k‖ ^ 2 + ‖k‖ ^ 2 * ‖χ.value k‖ ^ 2
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
  have hn : ‖k‖ ≤ 1 + ‖k‖ ^ 2 := by nlinarith [sq_nonneg (‖k‖ - 1)]
  nlinarith [mul_le_mul_of_nonneg_right hn (sq_nonneg ‖χ.value k‖)]

variable (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)

def omegaBase (i : Fin 3) (p : PhotonMode) : ℂ := (‖p.1‖ : ℂ) * base F χ i p

theorem omegaBase_measurable (i : Fin 3) : Measurable (omegaBase F χ i) :=
  (Complex.measurable_ofReal.comp measurable_fst.norm).mul (base_measurable F χ i)

include hUV in
theorem omegaBase_ultraviolet (i : Fin 3) :
    Integrable (fun p => ‖omegaBase F χ i p‖ ^ 2) photonMeasure := by
  have h := ((Measure.measurePreserving_neg volume).integrable_comp_of_integrable
    ((carlemanUV_iff_integrable χ).mp hUV)).comp_fst (Measure.count : Measure (Fin 2))
  simp only [Function.comp_def, norm_neg] at h
  apply h.mono' ((omegaBase_measurable F χ i).norm.pow_const 2).aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change ‖(‖p.1‖ : ℂ) * base F χ i p‖ ^ 2 ≤ _
  rw [omega_mul_norm_sq]
  exact mul_le_mul_of_nonneg_left (base_norm_bound F χ i p) (sq_nonneg _)

include hUV in
theorem omegaBase_infrared (i : Fin 3) :
    Integrable (fun p => (1 / ‖p.1‖) * ‖omegaBase F χ i p‖ ^ 2) photonMeasure := by
  have h := ((Measure.measurePreserving_neg volume).integrable_comp_of_integrable
    ((uv_iff_integrable χ).mp (sqrtUV_of_carlemanUV χ hUV))).comp_fst
      (Measure.count : Measure (Fin 2))
  simp only [Function.comp_def, norm_neg] at h
  apply h.mono' (((measurable_fst.norm.const_div 1).mul
    ((omegaBase_measurable F χ i).norm.pow_const 2)).aestronglyMeasurable)
  filter_upwards with p
  change ‖(1 / ‖p.1‖) * ‖omegaBase F χ i p‖ ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (by positivity)]
  change (1 / ‖p.1‖) * ‖(‖p.1‖ : ℂ) * base F χ i p‖ ^ 2 ≤ _
  rw [omega_mul_norm_sq]
  have he : (1 / ‖p.1‖) * ‖p.1‖ ^ 2 = ‖p.1‖ := by
    by_cases hp : ‖p.1‖ = 0
    · simp [hp]
    · field_simp
  rw [← mul_assoc, he]
  exact mul_le_mul_of_nonneg_left (base_norm_bound F χ i p) (norm_nonneg _)

/-- Multiplying the physical field label by ω preserves its weighted
one-photon domain, exactly as needed for the radiation commutator. -/
def omegaFactors : FormFactors photonMeasure (Fin 3) where
  momentum := Prod.fst
  momentum_measurable := measurable_fst
  base := omegaBase F χ
  measurable := omegaBase_measurable F χ
  ultraviolet := omegaBase_ultraviolet F χ hUV
  infrared := omegaBase_infrared F χ hUV

def omegaKernel (i : Fin 3) (x : FieldSpace) : WeightedPhotonKernel :=
  PhysicalProfiles.momentumKernel (omegaFactors F χ hUV) rfl
    (LinearIsometryEquiv.refl ℝ _) (i, x)

theorem omegaKernel_continuous (i : Fin 3) : Continuous (omegaKernel F χ hUV i) :=
  (PhysicalProfiles.momentumKernel_continuous (omegaFactors F χ hUV) rfl
    (LinearIsometryEquiv.refl ℝ _)).comp (continuous_const.prodMk continuous_id)

theorem omegaKernel_uniform_bound (i : Fin 3) (x : FieldSpace) :
    ‖omegaKernel F χ hUV i x‖ ≤
      PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _) :=
  PhysicalProfiles.momentumKernel_bound (omegaFactors F χ hUV) rfl
    (LinearIsometryEquiv.refl ℝ _) (i, x)

/-- The ordinary component is the literal frequency multiplier of `G_i(x)`. -/
theorem omegaKernel_fst_ae (i : Fin 3) (x : FieldSpace) :
    (omegaKernel F χ hUV i x).val.1 =ᵐ[photonMeasure]
      fun p => (‖p.1‖ : ℂ) * (physicalKernel F χ i x).val.1 p := by
  rw [show (omegaKernel F χ hUV i x).val.1 = (omegaFactors F χ hUV).fourierKernel (i, x) from
    TransformationsKernelCovariance.momentumKernel_fst _ rfl _ _]
  have hphys := physicalKernel_component F χ false i x
  simp only [component_false, Nonattainment.weightedFieldKernel_false] at hphys
  rw [hphys]
  filter_upwards [momentumKernelL2_ae Prod.fst measurable_fst (omegaBase F χ i)
      (omegaBase_measurable F χ i) (omegaBase_ultraviolet F χ hUV i) x,
    momentumKernelL2_ae Prod.fst measurable_fst (base F χ i)
      (base_measurable F χ i) (base_ultraviolet F χ i) x] with p hp hq
  change (momentumKernelL2 Prod.fst measurable_fst (omegaBase F χ i)
    (omegaBase_measurable F χ i) (omegaBase_ultraviolet F χ hUV i) x : PhotonMode → ℂ) p = _
  rw [hp]
  change _ = (‖p.1‖ : ℂ) * (momentumKernelL2 Prod.fst measurable_fst (base F χ i)
    (base_measurable F χ i) (base_ultraviolet F χ i) x : PhotonMode → ℂ) p
  rw [hq]
  simp only [momentumKernel, omegaBase]
  ring

end PfHk.PhysicalFieldRegularity
