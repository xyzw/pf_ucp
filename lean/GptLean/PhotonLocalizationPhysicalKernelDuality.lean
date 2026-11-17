import GptLean.PhotonLocalizationPhysicalKernels
import GptLean.PhotonLocalizationSharpRadiation

/-!
The radiation duality witness is derived from the universal Fourier
pairing and multiplier compatibility on L² intersected with homogeneous
negative half-Sobolev space. The retained multiplier is moved across the
actual L² inner product. Only the original, unlocalized modes need to be
identified with their Sobolev representatives.
-/

noncomputable section

namespace GptLean.PhotonLocalizationPhysicalKernels

open MeasureTheory
open scoped ENNReal InnerProductSpace
open Gaussian PhotonLocalization PhotonLocalizationKernelCutoffs
open PhotonLocalizationFockChannel

variable {E S V : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {μ : Measure FieldSpace}

omit [SMulCommClass ℝ ℂ E] in
/-- The Fourier pairing between inverse-frequency and positive-frequency
coordinates follows from pointwise cancellation of their square roots. -/
theorem weightedL2_pairing {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (weight : Ω → ℝ) (hw : ∀ᵐ p ∂ν, weight p ≠ 0)
    (a aMinus u uPlus : Lp E 2 ν)
    (ha : aMinus =ᵐ[ν] fun p => (weight p)⁻¹ • a p)
    (hu : uPlus =ᵐ[ν] fun p => weight p • u p) :
    ⟪aMinus, uPlus⟫_ℂ = ⟪a, u⟫_ℂ := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hw, ha, hu] with p hp hap hup
  rw [hap, hup, inner_smul_left_eq_smul, inner_smul_right_eq_smul,
    smul_smul, inv_mul_cancel₀ hp, one_smul]

omit [SMulCommClass ℝ ℂ E] in
theorem l2Multiplier_inner (χ : FieldSpace → ℝ)
    (hχ : AEStronglyMeasurable χ μ) (hb : ∀ᵐ y ∂μ, |χ y| ≤ 1)
    (u v : Lp E 2 μ) :
    ⟪u, PhotonKernelLocalization.l2Multiplier χ hχ hb v⟫_ℂ =
      ⟪PhotonKernelLocalization.l2Multiplier χ hχ hb u, v⟫_ℂ := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [PhotonKernelLocalization.l2Multiplier_apply_ae χ hχ hb u,
    PhotonKernelLocalization.l2Multiplier_apply_ae χ hχ hb v] with y hu hv
  rw [hu, hv, inner_smul_left_eq_smul, inner_smul_right_eq_smul]

/-- Universal compatibility of the L² and negative Sobolev realizations.
The predicates are the radiation square-root graph and the Fourier
identification on the intersection of the two spaces. Its identities
range over all vectors and all smooth compactly supported multipliers. -/
structure RadiationDualityBackground (B : SobolevMultiplierBackground S)
    (J : V ≃ₗᵢ[ℝ] S) where
  radiationGraph : Lp E 2 μ → V → Prop
  representative : Lp E 2 μ → S → Prop
  pairing : ∀ a w u z, representative a w → radiationGraph u z →
    ⟪a, u⟫_ℂ = ⟪J.symm w, z⟫_ℂ
  multiplier : ∀ (χ : FieldSpace → ℝ) (_hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (_hc : HasCompactSupport χ)
    (hχm : AEStronglyMeasurable χ μ) (hb : ∀ᵐ y ∂μ, |χ y| ≤ 1) a w,
    representative a w →
    representative (PhotonKernelLocalization.l2Multiplier χ hχm hb a)
      (B.multiplier χ w)

section FourierCoordinates

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- The universal Fourier coordinate maps for the one-photon space and
the radiation energy space. The physical dispersion is the momentum norm. -/
structure FourierRadiationCoordinates where
  momentum : Ω → FieldSpace
  nonzero : ∀ᵐ p ∂ν, momentum p ≠ 0
  fourier : Lp E 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν
  energyFourier : V ≃ₗᵢ[ℂ] Lp ℂ 2 ν

namespace FourierRadiationCoordinates

variable (C : FourierRadiationCoordinates (E := E) (V := V) (μ := μ) (ν := ν))

def radiationGraph (u : Lp E 2 μ) (z : V) : Prop :=
  C.energyFourier z =ᵐ[ν] fun p => Real.sqrt ‖C.momentum p‖ • C.fourier u p

def representative (J : V ≃ₗᵢ[ℝ] S) (a : Lp E 2 μ) (w : S) : Prop :=
  C.energyFourier (J.symm w) =ᵐ[ν] fun p =>
    (Real.sqrt ‖C.momentum p‖)⁻¹ • C.fourier a p

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E] in
theorem pairing (J : V ≃ₗᵢ[ℝ] S) {a : Lp E 2 μ} {w : S} {u : Lp E 2 μ} {z : V}
    (ha : C.representative J a w) (hu : C.radiationGraph u z) :
    ⟪a, u⟫_ℂ = ⟪J.symm w, z⟫_ℂ := by
  rw [← C.fourier.inner_map_map, ← C.energyFourier.inner_map_map]
  symm
  apply weightedL2_pairing (fun p => Real.sqrt ‖C.momentum p‖) _ _ _ _ _ ha hu
  filter_upwards [C.nonzero] with p hp
  exact ne_of_gt (Real.sqrt_pos.mpr (norm_pos_iff.mpr hp))

omit [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E] in
/-- When the universal Fourier maps agree, the two constructed physical
form-factor families satisfy the actual common-representative relation. -/
theorem formFactors_representative {ι : Type*} (F : FormFactors ν ι)
    (hdispersion : F.momentum = C.momentum)
    (U : Lp ℂ 2 ν ≃ₗᵢ[ℝ] Lp E 2 μ) (W : Lp ℂ 2 ν ≃ₗᵢ[ℝ] S)
    (J : V ≃ₗᵢ[ℝ] S)
    (hU : ∀ f, C.fourier (U f) = f)
    (hW : ∀ f, C.energyFourier (J.symm (W f)) = f) (z : ι × FieldSpace) :
    C.representative J (F.positionKernel U z) (F.sobolevKernel W z) := by
  unfold representative FormFactors.positionKernel FormFactors.sobolevKernel
  rw [hU, hW]
  simpa only [hdispersion] using F.weightedFourierKernel_ae z

/-- Fourier coordinates prove the weighted pairing field. The sole
compatibility input is the universal distributional multiplier identity
on the intersection of L² and negative Sobolev space. -/
def dualityBackground (B : SobolevMultiplierBackground S) (J : V ≃ₗᵢ[ℝ] S)
    (hmultiplier : ∀ (χ : FieldSpace → ℝ) (_hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
      (_hc : HasCompactSupport χ)
      (hχm : AEStronglyMeasurable χ μ) (hb : ∀ᵐ y ∂μ, |χ y| ≤ 1) a w,
      C.representative J a w →
      C.representative J (PhotonKernelLocalization.l2Multiplier χ hχm hb a)
        (B.multiplier χ w)) : RadiationDualityBackground (E := E) (μ := μ) B J where
  radiationGraph := C.radiationGraph
  representative := C.representative J
  pairing _ _ _ _ := C.pairing J
  multiplier := hmultiplier

end FourierRadiationCoordinates

end FourierCoordinates

namespace RadiationDualityBackground

variable {B : SobolevMultiplierBackground S} {J : V ≃ₗᵢ[ℝ] S}
  (W : RadiationDualityBackground (E := E) (μ := μ) B J)

omit [SMulCommClass ℝ ℂ E] in
theorem retained_pairing {R : ℝ} (hR : 0 < R) {a : Lp E 2 μ} {w : S}
    {u : Lp E 2 μ} {z : V}
    (ha : W.representative a w) (hu : W.radiationGraph u z) :
    ⟪a, retainedOperator R u⟫_ℂ = ⟪J.symm (B.multiplier (retained R) w), z⟫_ℂ := by
  rw [retainedOperator, l2Multiplier_inner]
  exact W.pairing _ _ _ _
    (W.multiplier (retained R) (retained_smooth R) (retained_compact hR)
      (retained_measurable R)
      (Filter.Eventually.of_forall (retained_abs_le_one R)) _ _ ha) hu

/-- The finite-rank localized pairing is a consequence of the original
mode representation and the universal Fourier/radiation graph calculus. -/
theorem radiation_duality (value : Lp E 2 μ → ℝ≥0∞)
    (hgraph : ∀ u, value u < ⊤ → ∃ z,
      W.radiationGraph u z ∧ value u = ENNReal.ofReal (‖z‖ ^ 2))
    (basis : (k : ℕ) → Fin k → V) (horth : ∀ k, Orthonormal ℂ (basis k))
    (modes : (k : ℕ) → Fin k → Lp E 2 μ)
    (hmodes : ∀ k i, W.representative (modes k i) (J (basis k i)))
    (k n : ℕ) (u : Lp E 2 μ) (hu : value u < ⊤) :
    ∃ z : V, value u = ENNReal.ofReal (‖z‖ ^ 2) ∧ ∀ i,
      ⟪modes k i, retainedMap (complexOnePhotonIsometry (radius n)) u⟫_ℂ =
        ⟪(B.radiationFamily J basis horth).localized k n i, z⟫_ℂ := by
  obtain ⟨z, hz, hvalue⟩ := hgraph u hu
  refine ⟨z, hvalue, fun i => ?_⟩
  rw [B.radiationFamily_localized J basis horth]
  exact W.retained_pairing (radius_pos n) (hmodes k i) hz

end RadiationDualityBackground

end GptLean.PhotonLocalizationPhysicalKernels
