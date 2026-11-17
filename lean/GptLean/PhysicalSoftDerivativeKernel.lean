import GptLean.PhysicalPolarizationFrame
import GptLean.PhysicalWeightedKernelSplit
import GptLean.PhysicalFockPhysicalProfiles
import GptLean.Gaussian.SpatialField

/-!
Actual weighted soft derivative labels for the article form factors.
Both L² components are constructed from their explicit momentum kernels.
Every inverse-frequency derivative moment follows from the infrared
cutoff moment and the sharp soft momentum bound.
-/

noncomputable section

namespace GptLean.PhysicalPolarization

open MeasureTheory Gaussian PhysicalFock PhotonLocalizationPhysicalKernels
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable (F : Frame) (χ : ArticleCutoff) {κ : ℝ} (hκ : 0 ≤ κ)

theorem derivativeKernel_measurable (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    Measurable (softDerivativeKernel Prod.fst ds κ x (base F χ i)) :=
  (measurable_softDerivativeKernel Prod.fst measurable_fst ds κ _
    (base_measurable F χ i)).comp (measurable_const.prodMk measurable_id)

include hκ in
theorem derivativeKernel_infrared (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    Integrable (fun p : PhotonMode =>
      (1 / ‖p.1‖) * ‖softDerivativeKernel Prod.fst ds κ x (base F χ i) p‖ ^ 2)
      photonMeasure := by
  have hb := softBase_weighted_integrable Prod.fst measurable_fst κ (base F χ i)
    (fun p => 1 / ‖p.1‖) (base_infrared F χ i)
  exact (softDerivativeKernel_moment Prod.fst ds hκ x (base F χ i)
    (fun p => 1 / ‖p.1‖) (fun _ => by positivity) hb
    (((measurable_fst.norm.const_div 1).mul
      ((derivativeKernel_measurable F χ i ds x).norm.pow_const 2)).aestronglyMeasurable)).1

include hκ in
theorem inverseDerivativeKernel_memLp (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    MemLp (infraredBase Prod.fst (softDerivativeKernel Prod.fst ds κ x (base F χ i)))
      2 photonMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    ((measurable_infraredBase Prod.fst measurable_fst _
      (derivativeKernel_measurable F χ i ds x)).aestronglyMeasurable)).mpr
  exact infraredBase_integrable Prod.fst _ (derivativeKernel_infrared F χ hκ i ds x)

/-- The physical soft derivative, including its inverse-frequency component. -/
def derivativeKernel (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) : WeightedPhotonKernel :=
  ⟨(softKernelL2 Prod.fst measurable_fst ds hκ (base F χ i)
      (base_measurable F χ i) (base_ultraviolet F χ i) x,
    (inverseDerivativeKernel_memLp F χ hκ i ds x).toLp _), by
    have hn : ∀ᵐ p ∂photonMeasure, p.1 ≠ (0 : FieldSpace) :=
      (Measure.quasiMeasurePreserving_fst (ν := (Measure.count : Measure (Fin 2)))).ae
        (volume.ae_ne 0)
    filter_upwards [(softDerivativeKernel_memLp Prod.fst measurable_fst ds hκ x
        (base F χ i) (base_measurable F χ i) (base_ultraviolet F χ i)).coeFn_toLp,
      (inverseDerivativeKernel_memLp F χ hκ i ds x).coeFn_toLp, hn] with p h₁ h₂ hp
    change softKernelL2 Prod.fst measurable_fst ds hκ (base F χ i)
        (base_measurable F χ i) (base_ultraviolet F χ i) x p =
      (Real.sqrt ‖p.1‖ : ℂ) *
        (inverseDerivativeKernel_memLp F χ hκ i ds x).toLp _ p
    change softKernelL2 Prod.fst measurable_fst ds hκ (base F χ i)
      (base_measurable F χ i) (base_ultraviolet F χ i) x p =
        softDerivativeKernel Prod.fst ds κ x (base F χ i) p at h₁
    rw [h₁, h₂]
    change _ = (Real.sqrt ‖p.1‖ : ℂ) *
      ((((Real.sqrt ‖p.1‖)⁻¹ : ℝ) : ℂ) * _)
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀
      (ne_of_gt (Real.sqrt_pos.mpr (norm_pos_iff.mpr hp))), Complex.ofReal_one, one_mul]⟩

@[simp] theorem derivativeKernel_fst (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    (derivativeKernel F χ hκ i ds x).val.1 =
      softKernelL2 Prod.fst measurable_fst ds hκ (base F χ i)
        (base_measurable F χ i) (base_ultraviolet F χ i) x := rfl

theorem derivativeKernel_fst_ae (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    (derivativeKernel F χ hκ i ds x).val.1 =ᵐ[photonMeasure]
      softDerivativeKernel Prod.fst ds κ x (base F χ i) :=
  (softDerivativeKernel_memLp Prod.fst measurable_fst ds hκ x (base F χ i)
    (base_measurable F χ i) (base_ultraviolet F χ i)).coeFn_toLp

theorem derivativeKernel_snd_ae (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    (derivativeKernel F χ hκ i ds x).val.2 =ᵐ[photonMeasure]
      infraredBase Prod.fst (softDerivativeKernel Prod.fst ds κ x (base F χ i)) :=
  (inverseDerivativeKernel_memLp F χ hκ i ds x).coeFn_toLp

theorem derivativeKernel_fst_norm_sq (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    ‖(derivativeKernel F χ hκ i ds x).val.1‖ ^ 2 =
      ∫ p, ‖softDerivativeKernel Prod.fst ds κ x (base F χ i) p‖ ^ 2 ∂photonMeasure := by
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [derivativeKernel_fst_ae F χ hκ i ds x] with p hp
  rw [hp]

theorem derivativeKernel_snd_norm_sq (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    ‖(derivativeKernel F χ hκ i ds x).val.2‖ ^ 2 =
      ∫ p : PhotonMode, (1 / ‖p.1‖) *
        ‖softDerivativeKernel Prod.fst ds κ x (base F χ i) p‖ ^ 2 ∂photonMeasure := by
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [derivativeKernel_snd_ae F χ hκ i ds x] with p hp
  rw [hp, infraredBase_norm_sq]

theorem derivativeKernel_snd_norm (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    ‖(derivativeKernel F χ hκ i ds x).val.2‖ =
      Real.sqrt (∫ p : PhotonMode, (1 / ‖p.1‖) *
        ‖softDerivativeKernel Prod.fst ds κ x (base F χ i) p‖ ^ 2 ∂photonMeasure) := by
  rw [← derivativeKernel_snd_norm_sq F χ hκ i ds x, Real.sqrt_sq (norm_nonneg _)]

theorem derivativeKernel_fst_mem (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    (derivativeKernel F χ hκ i ds x).val.1 ∈ softOnePhoton κ := by
  apply (MomentumSplit.mem_supported_iff photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ) _).mpr
  filter_upwards [derivativeKernel_fst_ae F χ hκ i ds x] with p hp
  intro hs
  rw [hp]
  change ¬‖p.1‖ < κ at hs
  simp only [softDerivativeKernel, softBase, hs, ↓reduceIte, mul_zero]

private theorem originalKernel_fst (i : Fin 3) (x : FieldSpace) :
    (PhysicalProfiles.momentumKernel (formFactors F χ) rfl
      (LinearIsometryEquiv.refl ℝ _) (i, x)).val.1 =
      (formFactors F χ).fourierKernel (i, x) := by
  change PhysicalOnePhotonFourier.fourier
    (PhysicalOnePhotonFourier.fourier.symm ((formFactors F χ).fourierKernel (i, x))) = _
  exact PhysicalOnePhotonFourier.fourier.apply_symm_apply _

theorem derivativeKernel_nil (i : Fin 3) (x : FieldSpace) :
    derivativeKernel F χ hκ i [] x = WeightedPhotonKernel.soft κ
      (PhysicalProfiles.momentumKernel (formFactors F χ) rfl
        (LinearIsometryEquiv.refl ℝ _) (i, x)) := by
  apply WeightedPhotonKernel.ext_fst
  rw [WeightedPhotonKernel.soft_fst, originalKernel_fst]
  apply Lp.ext
  filter_upwards [derivativeKernel_fst_ae F χ hκ i [] x,
    MomentumSplit.projection_ae photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) ((formFactors F χ).fourierKernel (i, x)),
    momentumKernelL2_ae Prod.fst measurable_fst (base F χ i)
      (base_measurable F χ i) (base_ultraviolet F χ i) x] with p h₁ h₂ h₃
  rw [h₁, h₂]
  change (formFactors F χ).fourierKernel (i, x) p = _ at h₃
  by_cases hp : ‖p.1‖ < κ
  · simp only [softDerivativeKernel, derivativeFactor, one_mul, softBase, hp, ↓reduceIte]
    rw [Set.indicator_of_mem (show p ∈ softMomentumSet κ from hp), h₃]
    rfl
  · simp only [softDerivativeKernel, derivativeFactor, one_mul, softBase, hp, ↓reduceIte,
      mul_zero]
    rw [Set.indicator_of_notMem (show p ∉ softMomentumSet κ from hp)]

end GptLean.PhysicalPolarization
