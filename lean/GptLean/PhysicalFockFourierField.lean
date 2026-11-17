import GptLean.PhysicalFockSpatialField
import GptLean.PhotonLocalizationKernelDilation

/-!
The existing physical Fourier profiles feed the constructed Fock field.

The common Fourier coordinates identify the position-space L² kernel
and its negative-Sobolev representative with a weighted kernel in the
actual momentum/polarization one-photon space. This bridge applies to
both the original form-factor profile and every actual cutoff tail.
The position-dependent field then acts on electronic L² of the same
radiation graph.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory Gaussian PhotonLocalizationPhysicalKernels
open scoped ENNReal InnerProductSpace

variable {E V S ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [TopologicalSpace ι]
  {μ : Measure FieldSpace}
  (C : FourierRadiationCoordinates (E := E) (V := V) (μ := μ) (ν := photonMeasure))
  (J : V ≃ₗᵢ[ℝ] S) (hdispersion : C.momentum = Prod.fst)

/-- Both Fourier representatives belong to one actual weighted kernel. -/
def profileMomentumKernel (p : SpatialKernelProfile C J ι) (z : ι × FieldSpace) :
    WeightedPhotonKernel :=
  ⟨(C.fourier (p.l2 z), C.energyFourier (J.symm (p.negative z))), by
    filter_upwards [p.represents z, C.nonzero] with k hk hn
    change C.fourier (p.l2 z) k = (Real.sqrt ‖k.1‖ : ℂ) *
      C.energyFourier (J.symm (p.negative z)) k
    change C.energyFourier (J.symm (p.negative z)) k =
      (Real.sqrt ‖C.momentum k‖)⁻¹ • C.fourier (p.l2 z) k at hk
    rw [hdispersion] at hk hn
    rw [hk]
    change C.fourier (p.l2 z) k = (Real.sqrt ‖k.1‖ : ℂ) *
      ((((Real.sqrt ‖k.1‖)⁻¹ : ℝ) : ℂ) * C.fourier (p.l2 z) k)
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀
      (ne_of_gt (Real.sqrt_pos.mpr (norm_pos_iff.mpr hn))), Complex.ofReal_one, one_mul]⟩

theorem profileMomentumKernel_continuous (p : SpatialKernelProfile C J ι) :
    Continuous (profileMomentumKernel C J hdispersion p) := by
  exact ((C.fourier.continuous.comp p.continuous_l2).prodMk
    (C.energyFourier.continuous.comp (J.symm.continuous.comp p.continuous_negative))).subtype_mk _

@[simp] theorem profileMomentumKernel_l2_norm (p : SpatialKernelProfile C J ι)
    (z : ι × FieldSpace) :
    ‖(profileMomentumKernel C J hdispersion p z).val.1‖ = ‖p.l2 z‖ :=
  C.fourier.norm_map _

@[simp] theorem profileMomentumKernel_negative_norm (p : SpatialKernelProfile C J ι)
    (z : ι × FieldSpace) :
    ‖(profileMomentumKernel C J hdispersion p z).val.2‖ = ‖p.negative z‖ := by
  change ‖C.energyFourier (J.symm (p.negative z))‖ = _
  rw [C.energyFourier.norm_map, J.symm.norm_map]

def profileKernelBound (p : SpatialKernelProfile C J ι) : ℝ :=
  max p.bounded_l2.choose p.bounded_negative.choose

theorem profileMomentumKernel_bound (p : SpatialKernelProfile C J ι) (z : ι × FieldSpace) :
    ‖profileMomentumKernel C J hdispersion p z‖ ≤ profileKernelBound C J p := by
  change max ‖(profileMomentumKernel C J hdispersion p z).val.1‖
    ‖(profileMomentumKernel C J hdispersion p z).val.2‖ ≤ _
  rw [profileMomentumKernel_l2_norm, profileMomentumKernel_negative_norm]
  exact max_le_max (p.bounded_l2.choose_spec z) (p.bounded_negative.choose_spec z)

section Electronic

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)
  (CCR : CanonicalSectorCCR photonMeasure) (p : SpatialKernelProfile C J ι)
  (position : X → ι × FieldSpace) (hposition : AEStronglyMeasurable position ν)

def profileSpatialField : SpatialRadiationGraph ν →L[ℂ] SpatialPhotonSpace ν :=
  spatialField ν CCR (fun x => profileMomentumKernel C J hdispersion p (position x))
    ((profileMomentumKernel_continuous C J hdispersion p).comp_aestronglyMeasurable hposition)
    (profileKernelBound C J p)
    (ae_of_all _ fun x => profileMomentumKernel_bound C J hdispersion p (position x))

theorem profileSpatialField_ae (u : SpatialRadiationGraph ν) :
    profileSpatialField C J hdispersion ν CCR p position hposition u =ᵐ[ν]
      fun x => kernelField CCR (profileMomentumKernel C J hdispersion p (position x)) (u x) :=
  spatialField_ae ν CCR _ _ _ _ u

/-- The original and tail profiles inherit the proved physical field estimate. -/
theorem profileSpatialField_radiation_bound (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hnegative : ∀ᵐ x ∂ν, ‖p.negative (position x)‖ ≤ A)
    (hl2 : ∀ᵐ x ∂ν, ‖p.l2 (position x)‖ ≤ B) (u : SpatialRadiationGraph ν) :
    ‖profileSpatialField C J hdispersion ν CCR p position hposition u‖ ^ 2 ≤
      8 * A ^ 2 * ‖spatialRadiationDerivative ν u‖ ^ 2 +
        2 * B ^ 2 * ‖spatialRadiationInclusion ν u‖ ^ 2 := by
  apply spatialField_radiation_bound ν CCR _ _ _ _ A B hA hB
  · simpa only [profileMomentumKernel_negative_norm] using hnegative
  · simpa only [profileMomentumKernel_l2_norm] using hl2

end Electronic

end GptLean.PhysicalFock
