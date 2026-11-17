import GptLean.TransformationsFockPointwise
import GptLean.PhysicalFockPhysicalProfiles
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Covariance of the physical one-photon kernel under photon translations and
the time-reversal reflection.

The physical weighted kernel is the pair of Fourier form factors
`k ↦ e^{-i k·y} G_a(k)` and `k ↦ e^{-i k·y} |k|^{-1/2} G_a(k)`. Translation
by `b` multiplies a photon wave function by `e^{-i k·b}`. It is a pointwise
unitary which preserves `|k|`, and it moves the electron coordinate of the
kernel from `y - b` to `y`. The reflection `(k, λ) ↦ (-k, λ)` with a constant
unimodular weight `s` preserves `|k|` as well. When the form factors satisfy
the reality condition `conj (G_a(-k, λ)) = G_a(k, λ)`, its antiunitary maps
the kernel at `y` to `s` times itself.
-/

noncomputable section

namespace GptLean.TransformationsKernelCovariance

open MeasureTheory
open GptLean.PhysicalFock GptLean.TransformationsFock GptLean.Gaussian
  GptLean.PhotonLocalizationPhysicalKernels
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

section Phase

/-- Phases at the same momentum multiply by adding the positions. -/
theorem fieldPhase_mul (p x x' : FieldSpace) :
    fieldPhase p x * fieldPhase p x' = fieldPhase p (x + x') := by
  unfold fieldPhase
  rw [← Complex.exp_add, inner_add_right]
  congr 1
  push_cast
  ring

/-- Reversing the momentum conjugates the phase. -/
theorem conj_fieldPhase_neg (p x : FieldSpace) :
    starRingEnd ℂ (fieldPhase (-p) x) = fieldPhase p x := by
  unfold fieldPhase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, inner_neg_left]
  congr 1
  push_cast
  ring

end Phase

section Kernel

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  (F : FormFactors photonMeasure (Fin 3)) (hF : F.momentum = Prod.fst)
  (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] S)

/-- The L² component of the physical kernel is the Fourier form factor. -/
theorem momentumKernel_fst (z : Fin 3 × FieldSpace) :
    (PhysicalProfiles.momentumKernel F hF J z).val.1 = F.fourierKernel z := by
  change PhysicalOnePhotonFourier.fourier
    (PhysicalOnePhotonFourier.fourier.symm (F.fourierKernel z)) = _
  exact PhysicalOnePhotonFourier.fourier.apply_symm_apply _

/-- The inverse-frequency component of the physical kernel is the weighted
Fourier form factor. -/
theorem momentumKernel_snd (z : Fin 3 × FieldSpace) :
    (PhysicalProfiles.momentumKernel F hF J z).val.2 = F.weightedFourierKernel z := by
  change J.symm (J (F.weightedFourierKernel z)) = _
  exact J.symm_apply_apply _

/-- The physical kernel is the pair of Fourier form factors. -/
theorem momentumKernel_val (z : Fin 3 × FieldSpace) :
    (PhysicalProfiles.momentumKernel F hF J z).val =
      (F.fourierKernel z, F.weightedFourierKernel z) :=
  Prod.ext (momentumKernel_fst F hF J z) (momentumKernel_snd F hF J z)

include hF in
/-- The Fourier form factor at the electron position `x`. -/
theorem fourierKernel_ae (a : Fin 3) (x : FieldSpace) :
    F.fourierKernel (a, x) =ᵐ[photonMeasure] fun p => fieldPhase p.1 x * F.base a p := by
  filter_upwards [momentumKernelL2_ae F.momentum F.momentum_measurable (F.base a)
    (F.measurable a) (F.ultraviolet a) x] with p hp
  exact hp.trans
    (congrArg (fun m : PhotonMode → FieldSpace => fieldPhase (m p) x * F.base a p) hF)

include hF in
/-- The weighted Fourier form factor at the electron position `x`. -/
theorem weightedFourierKernel_ae (a : Fin 3) (x : FieldSpace) :
    F.weightedFourierKernel (a, x) =ᵐ[photonMeasure] fun p =>
      fieldPhase p.1 x * infraredBase (Prod.fst : PhotonMode → FieldSpace) (F.base a) p := by
  filter_upwards [momentumKernelL2_ae F.momentum F.momentum_measurable
    (infraredBase F.momentum (F.base a))
    (measurable_infraredBase F.momentum F.momentum_measurable _ (F.measurable a))
    (infraredBase_integrable F.momentum _ (F.infrared a)) x] with p hp
  exact hp.trans (congrArg (fun m : PhotonMode → FieldSpace =>
    fieldPhase (m p) x * infraredBase m (F.base a) p) hF)

end Kernel

section Translation

theorem measurable_translationWeight (b : FieldSpace) :
    Measurable (fun p : PhotonMode => fieldPhase p.1 b) := by
  have hf : Measurable (fun p : PhotonMode => (p.1, b)) := measurable_fst.prodMk measurable_const
  have hg : Measurable (fun z : FieldSpace × FieldSpace => fieldPhase z.1 z.2) :=
    continuous_fieldPhase.measurable
  have h := hg.comp hf
  exact h

/-- Translation of the photon by `b`, `(t_b f)(k, λ) = e^{-i k·b} f(k, λ)`. -/
def photonTranslation (b : FieldSpace) : PointwiseUnitary photonMeasure where
  map := MeasurableEquiv.refl PhotonMode
  preserving := MeasurePreserving.id photonMeasure
  weight p := fieldPhase p.1 b
  measurable_weight := measurable_translationWeight b
  norm_weight p := norm_fieldPhase p.1 b

/-- Translations do not move the momentum. -/
theorem photonTranslation_dispersion (b : FieldSpace) :
    ∀ p, ‖((photonTranslation b).map p).1‖ = ‖p.1‖ := fun _ => rfl

/-- Translation moves a phased form factor from `y - b` to `y`. -/
theorem oneParticle_translation (b y : FieldSpace) {g : PhotonMode → ℂ}
    {u v : Lp ℂ 2 photonMeasure}
    (hu : u =ᵐ[photonMeasure] fun p => fieldPhase p.1 (y - b) * g p)
    (hv : v =ᵐ[photonMeasure] fun p => fieldPhase p.1 y * g p) :
    oneParticle (photonTranslation b) u = v := by
  apply Lp.ext
  filter_upwards [oneParticle_ae (photonTranslation b) u, hu, hv] with p h₁ h₂ h₃
  rw [h₁, h₃]
  change fieldPhase p.1 b * u p = _
  rw [h₂, ← mul_assoc, fieldPhase_mul, add_sub_cancel]

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  (F : FormFactors photonMeasure (Fin 3)) (hF : F.momentum = Prod.fst)
  (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] S)

/-- Translation covariance of the physical kernel: the photon translation by
`b` maps the kernel at the electron position `y - b` to the kernel at `y`. -/
theorem kernelMap_translation (b : FieldSpace) (a : Fin 3) (y : FieldSpace) :
    kernelMap (photonTranslation b) (photonTranslation_dispersion b)
        (PhysicalProfiles.momentumKernel F hF J (a, y - b)) =
      PhysicalProfiles.momentumKernel F hF J (a, y) := by
  apply Subtype.ext
  apply Prod.ext
  · rw [kernelMap_fst, momentumKernel_fst, momentumKernel_fst]
    exact oneParticle_translation b y (fourierKernel_ae F hF a (y - b))
      (fourierKernel_ae F hF a y)
  · rw [kernelMap_snd, momentumKernel_snd, momentumKernel_snd]
    exact oneParticle_translation b y (weightedFourierKernel_ae F hF a (y - b))
      (weightedFourierKernel_ae F hF a y)

end Translation

section Reflection

theorem measurable_reflect : Measurable (fun p : PhotonMode => (-p.1, p.2)) :=
  measurable_fst.neg.prodMk measurable_snd

/-- The momentum reflection `(k, λ) ↦ (-k, λ)`. -/
def reflectionMap : PhotonMode ≃ᵐ PhotonMode where
  toFun p := (-p.1, p.2)
  invFun p := (-p.1, p.2)
  left_inv p := Prod.ext (neg_neg p.1) rfl
  right_inv p := Prod.ext (neg_neg p.1) rfl
  measurable_toFun := measurable_reflect
  measurable_invFun := measurable_reflect

@[simp] theorem reflectionMap_apply (p : PhotonMode) : reflectionMap p = (-p.1, p.2) := rfl

/-- The momentum reflection preserves the photon measure. -/
theorem reflectionMap_preserving : MeasurePreserving reflectionMap photonMeasure photonMeasure := by
  have h₁ := (LinearIsometryEquiv.neg ℝ : FieldSpace ≃ₗᵢ[ℝ] FieldSpace).measurePreserving
  rw [LinearIsometryEquiv.coe_neg] at h₁
  have h₂ := h₁.prod (MeasurePreserving.id (Measure.count : Measure (Fin 2)))
  have he : (reflectionMap : PhotonMode → PhotonMode) =
      Prod.map (fun k : FieldSpace => -k) id := rfl
  rw [he]
  exact h₂

/-- The reflection `(R f)(k, λ) = s f(-k, λ)` with a unimodular constant `s`. -/
def photonReflection (s : ℂ) (hs : ‖s‖ = 1) : PointwiseUnitary photonMeasure where
  map := reflectionMap
  preserving := reflectionMap_preserving
  weight _ := s
  measurable_weight := measurable_const
  norm_weight _ := hs

/-- The reflection preserves `|k|`. -/
theorem photonReflection_dispersion (s : ℂ) (hs : ‖s‖ = 1) :
    ∀ p, ‖((photonReflection s hs).map p).1‖ = ‖p.1‖ := fun p => norm_neg p.1

/-- The inverse-frequency component of the antiunitary kernel map. -/
theorem kernelAnti_snd (U : PointwiseUnitary photonMeasure) (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖)
    (k : WeightedPhotonKernel) : (kernelAnti U hU k).val.2 = antiParticle U k.val.2 := rfl

theorem smul_val_fst (c : ℂ) (k : WeightedPhotonKernel) : (c • k).val.1 = c • k.val.1 := rfl

theorem smul_val_snd (c : ℂ) (k : WeightedPhotonKernel) : (c • k).val.2 = c • k.val.2 := rfl

/-- A phased form factor whose profile is real under momentum reversal is an
eigenvector of the reflection antiunitary with eigenvalue `s`. -/
theorem antiParticle_reflection (s : ℂ) (hs : ‖s‖ = 1) (y : FieldSpace) {g : PhotonMode → ℂ}
    (hg : ∀ p : PhotonMode, starRingEnd ℂ (g (-p.1, p.2)) = g p)
    {u : Lp ℂ 2 photonMeasure} (hu : u =ᵐ[photonMeasure] fun p => fieldPhase p.1 y * g p) :
    antiParticle (photonReflection s hs) u = s • u := by
  apply Lp.ext
  filter_upwards [antiParticle_ae (photonReflection s hs) u, Lp.coeFn_smul s u, hu,
    (photonReflection s hs).preserving.quasiMeasurePreserving.ae hu] with p h₁ h₂ h₃ h₄
  rw [h₁, h₄, h₂, Pi.smul_apply, smul_eq_mul, h₃]
  change s * starRingEnd ℂ (fieldPhase (-p.1) y * g (-p.1, p.2)) =
    s * (fieldPhase p.1 y * g p)
  rw [map_mul, conj_fieldPhase_neg, hg]

/-- The reality condition passes to the inverse-frequency profile, since
`|-k| = |k|`. -/
theorem conj_infraredBase {g : PhotonMode → ℂ}
    (hg : ∀ p : PhotonMode, starRingEnd ℂ (g (-p.1, p.2)) = g p) (p : PhotonMode) :
    starRingEnd ℂ (infraredBase (Prod.fst : PhotonMode → FieldSpace) g (-p.1, p.2)) =
      infraredBase (Prod.fst : PhotonMode → FieldSpace) g p := by
  change starRingEnd ℂ ((Real.sqrt ‖-p.1‖)⁻¹ • g (-p.1, p.2)) = (Real.sqrt ‖p.1‖)⁻¹ • g p
  rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal, norm_neg, hg]

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  (F : FormFactors photonMeasure (Fin 3)) (hF : F.momentum = Prod.fst)
  (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] S)

/-- Time-reversal covariance of the physical kernel: under the reality
condition `conj (G_a(-k, λ)) = G_a(k, λ)` the reflection antiunitary maps the
kernel at every electron position to `s` times itself. -/
theorem kernelAnti_reflection (s : ℂ) (hs : ‖s‖ = 1)
    (hpar : ∀ a (p : PhotonMode), starRingEnd ℂ (F.base a (-p.1, p.2)) = F.base a p)
    (a : Fin 3) (y : FieldSpace) :
    kernelAnti (photonReflection s hs) (photonReflection_dispersion s hs)
        (PhysicalProfiles.momentumKernel F hF J (a, y)) =
      s • PhysicalProfiles.momentumKernel F hF J (a, y) := by
  apply Subtype.ext
  apply Prod.ext
  · rw [kernelAnti_fst, smul_val_fst, momentumKernel_fst]
    exact antiParticle_reflection s hs y (hpar a) (fourierKernel_ae F hF a y)
  · rw [kernelAnti_snd, smul_val_snd, momentumKernel_snd]
    exact antiParticle_reflection s hs y (conj_infraredBase (hpar a))
      (weightedFourierKernel_ae F hF a y)

end Reflection

end GptLean.TransformationsKernelCovariance
