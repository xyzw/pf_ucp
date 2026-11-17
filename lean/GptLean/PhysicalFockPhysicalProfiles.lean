import GptLean.PhysicalFockChannelProfiles
import GptLean.PhysicalFockRadiationLocalization
import GptLean.PhysicalFockFieldPermutation

/-!
The physical original and cutoff profiles use the very same one-photon
Fourier map as the Fock channel. All small parameters are the proved
compact-uniform errors of the actual form factors.
-/

noncomputable section
namespace GptLean.PhysicalFock.PhysicalProfiles

open MeasureTheory Gaussian PhotonLocalizationPhysicalKernels PhotonLocalizationKernelCutoffs
  SymmetricLift
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000
set_option Elab.async false

def positionCoordinates : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] PhysicalOnePhotonFourier.PositionSpace where
  toLinearEquiv := PhysicalOnePhotonFourier.fourier.symm.toLinearEquiv.restrictScalars ℝ
  norm_map' := PhysicalOnePhotonFourier.fourier.symm.norm_map

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  (F : FormFactors photonMeasure (Fin 3)) (hF : F.momentum = Prod.fst)
  (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] S)

def profile : SpatialKernelProfile physicalRadiationCoordinates J (Fin 3) :=
  F.profile physicalRadiationCoordinates J positionCoordinates J hF
    (fun f => PhysicalOnePhotonFourier.fourier.apply_symm_apply f)
    (fun f => J.symm_apply_apply f)

def momentumKernel : Fin 3 × FieldSpace → WeightedPhotonKernel :=
  profileMomentumKernel physicalRadiationCoordinates J rfl (profile F hF J)

theorem momentumKernel_continuous : Continuous (momentumKernel F hF J) :=
  profileMomentumKernel_continuous physicalRadiationCoordinates J rfl (profile F hF J)

def kernelBound : ℝ := profileKernelBound physicalRadiationCoordinates J (profile F hF J)

theorem momentumKernel_bound (z : Fin 3 × FieldSpace) :
    ‖momentumKernel F hF J z‖ ≤ kernelBound F hF J :=
  profileMomentumKernel_bound physicalRadiationCoordinates J rfl (profile F hF J) z

def particleKernel (N : ℕ) (i : Fin N × Fin 3) (x : Configuration N) : WeightedPhotonKernel :=
  momentumKernel F hF J (i.2, particle x i.1)

theorem particleKernel_measurable (N : ℕ) (i : Fin N × Fin 3) :
    AEStronglyMeasurable (particleKernel F hF J N i) volume :=
  ((momentumKernel_continuous F hF J).comp
    (continuous_const.prodMk (particleLinear i.1).continuous_of_finiteDimensional)).aestronglyMeasurable

theorem particleKernel_bound (N : ℕ) (i : Fin N × Fin 3) :
    ∀ᵐ x ∂volume, ‖particleKernel F hF J N i x‖ ≤ kernelBound F hF J :=
  ae_of_all _ fun x => momentumKernel_bound F hF J (i.2, particle x i.1)

variable (B : SobolevMultiplierBackground S)
  (hmult : ∀ (χ : FieldSpace → ℝ) (_hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (_hc : HasCompactSupport χ)
    (hχm : AEStronglyMeasurable χ (volume : Measure FieldSpace))
    (hb : ∀ᵐ y ∂(volume : Measure FieldSpace), |χ y| ≤ 1) a w,
    physicalRadiationCoordinates.representative J a w →
    physicalRadiationCoordinates.representative J
      (PhotonKernelLocalization.l2Multiplier χ hχm hb a) (B.multiplier χ w))

def tailProfile (m : ℕ) : SpatialKernelProfile physicalRadiationCoordinates J (Fin 3) :=
  F.tailProfile physicalRadiationCoordinates J positionCoordinates J hF
    (fun f => PhysicalOnePhotonFourier.fourier.apply_symm_apply f)
    (fun f => J.symm_apply_apply f) B hmult m

theorem tailProfile_l2 (m : ℕ) (z : Fin 3 × FieldSpace) :
    (tailProfile F hF J B hmult m).l2 z =
      (profile F hF J).l2 z - retainedOperator (radius m) ((profile F hF J).l2 z) :=
  tailOperator_eq_sub_retained m _

def cutoffError (l m : ℕ) : ℝ := (F.cutoffFamily positionCoordinates J B).error l m

theorem cutoffError_nonneg (l m : ℕ) : 0 ≤ cutoffError F J B l m :=
  (F.cutoffFamily positionCoordinates J B).error_nonneg l m

theorem cutoffError_zero (l : ℕ) :
    Filter.Tendsto (cutoffError F J B l) Filter.atTop (nhds 0) :=
  F.cutoff_error_zero positionCoordinates J B l

theorem cutoff_components (l m : ℕ) (z : Fin 3 × FieldSpace) (hz : ‖z.2‖ ≤ l) :
    ‖(tailProfile F hF J B hmult m).l2 z‖ ≤ cutoffError F J B l m ∧
    ‖(tailProfile F hF J B hmult m).negative z‖ ≤ cutoffError F J B l m ∧
    ‖discardedOperator (radius m) ((profile F hF J).l2 z)‖ ≤ cutoffError F J B l m :=
  F.cutoff_component_bounds positionCoordinates J B hz

end GptLean.PhysicalFock.PhysicalProfiles
