import GptLean.PhysicalFockRadiationFrame
import GptLean.PhysicalFockPhysicalForms
import GptLean.PhotonLocalizationPhysicalKernelDuality
import GptLean.PhysicalOnePhotonFourier

/-!
The concrete shell frame supplies the radiation modes used by the sharp
localization bound. The modes, their finite-rank quadratic forms and their
inverse-frequency representatives are constructed on the same photon
space. Only the universal Fourier and homogeneous Sobolev multiplier
compatibility remains as analytic background.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory Gaussian PhotonLocalization PhotonLocalizationKernelCutoffs
  PhotonLocalizationPhysicalKernels PhotonLocalizationFockChannel
  PhotonLocalizationFormBounds PhysicalNormalTrace
  PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false

variable {E S V : Type} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {μ : Measure FieldSpace}
  (C : FourierRadiationCoordinates (E := E) (V := V) (μ := μ) (ν := photonMeasure))

def radiationLocalizationBasis (k : ℕ) (i : Fin k) : V :=
  C.energyFourier.symm (radiationFrame i)

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E] in
theorem radiationLocalizationBasis_bessel (k : ℕ) (z : V) :
    ∑ i, ‖⟪radiationLocalizationBasis C k i, z⟫_ℂ‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  have he (i : Fin k) : ⟪radiationLocalizationBasis C k i, z⟫_ℂ =
      ⟪radiationFrame i, C.energyFourier z⟫_ℂ := by
    rw [← C.energyFourier.inner_map_map]
    simp only [radiationLocalizationBasis, C.energyFourier.apply_symm_apply]
  simpa only [he, C.energyFourier.norm_map] using radiationFrame_bessel k (C.energyFourier z)

def radiationLocalizationModes (k : ℕ) (i : Fin k) : Lp E 2 μ :=
  C.fourier.symm (radiationFamily i)

def radiationLocalizationFamily (B : SobolevMultiplierBackground S)
    (J : V ≃ₗᵢ[ℝ] S) : PhotonLocalization.RadiationFamily V :=
  PhotonLocalization.RadiationFamily.ofStrongBesselError
    (radiationLocalizationBasis C) (radiationLocalizationBasis_bessel C)
    (B.radiationError J) (B.radiationError_zero J)

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E] in
theorem radiationLocalizationFamily_localized (B : SobolevMultiplierBackground S)
    (J : V ≃ₗᵢ[ℝ] S) (k m : ℕ) (i : Fin k) :
    (radiationLocalizationFamily C B J).localized k m i =
      J.symm (B.multiplier (retained (radius m)) (J (radiationLocalizationBasis C k i))) := by
  change radiationLocalizationBasis C k i -
    J.symm (J (radiationLocalizationBasis C k i) -
      B.multiplier (retained (radius m)) (J (radiationLocalizationBasis C k i))) = _
  rw [map_sub, J.symm_apply_apply]
  abel

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E] in
theorem radiationLocalizationModes_representative
    (hdispersion : C.momentum = Prod.fst) (J : V ≃ₗᵢ[ℝ] S) (k : ℕ) (i : Fin k) :
    C.representative J (radiationLocalizationModes C k i)
      (J (radiationLocalizationBasis C k i)) := by
  unfold FourierRadiationCoordinates.representative radiationLocalizationModes
    radiationLocalizationBasis
  rw [J.symm_apply_apply, C.energyFourier.apply_symm_apply, C.fourier.apply_symm_apply]
  filter_upwards [radiationFamily_weighted i, C.nonzero] with p hp hn
  have hn' : Real.sqrt ‖p.1‖ ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (norm_pos_iff.mpr (by simpa only [hdispersion] using hn)))
  rw [hdispersion, hp, Complex.real_smul]
  simp only [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀
    (Complex.ofReal_ne_zero.mpr hn'), one_mul]

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E] in
theorem radiationLocalization_root (hdispersion : C.momentum = Prod.fst)
    (u : Lp E 2 μ) (hu : onePhotonFamilyValue radiationFamily (C.fourier u) < ⊤) :
    ∃ z : V, C.radiationGraph u z ∧
      onePhotonFamilyValue radiationFamily (C.fourier u) = ENNReal.ofReal (‖z‖ ^ 2) := by
  obtain ⟨z, he, hz⟩ := exists_photonRadiationRoot (C.fourier u) hu
  refine ⟨C.energyFourier.symm z, ?_, ?_⟩
  · unfold FourierRadiationCoordinates.radiationGraph
    filter_upwards [hz] with p hp
    simpa only [C.energyFourier.apply_symm_apply, hdispersion, Complex.real_smul] using hp
  · simpa only [C.energyFourier.symm.norm_map] using he

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E] in
theorem radiationLocalization_truncation (k : ℕ) (u : Lp E 2 μ) :
    onePhotonFamilyValue (finiteFamily radiationFamily k) (C.fourier u) =
      ENNReal.ofReal (∑ i, ‖⟪radiationLocalizationModes C k i, u⟫_ℂ‖ ^ 2) := by
  rw [finiteFamily_value_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : ⟪radiationLocalizationModes C k i, u⟫_ℂ =
      ⟪radiationFamily i, C.fourier u⟫_ℂ := by
    rw [← C.fourier.inner_map_map]
    simp only [radiationLocalizationModes, C.fourier.apply_symm_apply]
  rw [he]

variable (B : SobolevMultiplierBackground S) (J : V ≃ₗᵢ[ℝ] S)
  (hmultiplier : ∀ (χ : FieldSpace → ℝ) (_hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (_hc : HasCompactSupport χ)
    (hχm : AEStronglyMeasurable χ μ) (hb : ∀ᵐ y ∂μ, |χ y| ≤ 1) a w,
    C.representative J a w →
    C.representative J (PhotonKernelLocalization.l2Multiplier χ hχm hb a)
      (B.multiplier χ w))

include hmultiplier in
theorem radiationLocalization_duality (hdispersion : C.momentum = Prod.fst)
    (k m : ℕ) (u : Lp E 2 μ)
    (hu : onePhotonFamilyValue radiationFamily (C.fourier u) < ⊤) :
    ∃ z : V,
      onePhotonFamilyValue radiationFamily (C.fourier u) = ENNReal.ofReal (‖z‖ ^ 2) ∧
      ∀ i, ⟪radiationLocalizationModes C k i,
          retainedMap (complexOnePhotonIsometry (radius m)) u⟫_ℂ =
        ⟪(radiationLocalizationFamily C B J).localized k m i, z⟫_ℂ := by
  obtain ⟨z, hz, he⟩ := radiationLocalization_root C hdispersion u hu
  refine ⟨z, he, fun i => ?_⟩
  rw [radiationLocalizationFamily_localized]
  exact (C.dualityBackground B J hmultiplier).retained_pairing (radius_pos m)
    (radiationLocalizationModes_representative C hdispersion J k i) hz

include hmultiplier in
/-- The actual full normal channel satisfies the sharp radiation bound.
The root duality and finite-rank form are proved from the physical frame. -/
theorem fullFormCalculus_sharp_radiation
    (BF : StandardSymmetricFockExponential) (CCR : CanonicalSectorCCR photonMeasure)
    (BT : StandardNormalTraceBackground) (N k m : ℕ)
    (hdispersion : C.momentum = Prod.fst) {x : BT.FullTrace N}
    (hx : x ∈ (BT.realization (FullHilbert N)).rank.positive) :
    ((fullFormCalculus BF CCR BT C.fourier N).observable (finiteFamily radiationFamily k)).expectation
      (BT.normal.extend ((fullFactorization BF C.fourier N).factor
        (complexOnePhotonIsometry (radius m))) x) ≤
      ENNReal.ofReal (1 + (radiationLocalizationFamily C B J).error k m) *
        ((fullFormCalculus BF CCR BT C.fourier N).observable radiationFamily).expectation x := by
  exact sharp_channel_radiation_bound (fullFormCalculus BF CCR BT C.fourier N)
    BT.normal (fun _ hx => hx) (radiationLocalizationFamily C B J)
    radiationFamily (finiteFamily radiationFamily) m k (complexOnePhotonIsometry (radius m))
    (radiationLocalizationModes C k) (radiationLocalization_truncation C k)
    (fun u hu => radiationLocalization_duality C B J hmultiplier hdispersion k m u hu) hx

section PhysicalCoordinates

/-- The energy coordinate is the same momentum L2 space as the actual shell frame. -/
def physicalRadiationCoordinates : FourierRadiationCoordinates
    (E := PhysicalOnePhotonFourier.Polarization) (V := Lp ℂ 2 photonMeasure)
    (μ := (volume : Measure FieldSpace)) (ν := photonMeasure) :=
  PhysicalOnePhotonFourier.coordinates (LinearIsometryEquiv.refl ℂ (Lp ℂ 2 photonMeasure))

def physicalRadiationFamily (B : SobolevMultiplierBackground S)
    (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] S) : PhotonLocalization.RadiationFamily (Lp ℂ 2 photonMeasure) :=
  radiationLocalizationFamily physicalRadiationCoordinates B J

/-- Sharp radiation localization on the actual Fourier map shared with local compactness. -/
theorem physical_channel_radiation_bound
    (B : SobolevMultiplierBackground S) (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] S)
    (hmult : ∀ (χ : FieldSpace → ℝ) (_hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
      (_hc : HasCompactSupport χ)
      (hχm : AEStronglyMeasurable χ (volume : Measure FieldSpace))
      (hb : ∀ᵐ y ∂(volume : Measure FieldSpace), |χ y| ≤ 1) a w,
      physicalRadiationCoordinates.representative J a w →
      physicalRadiationCoordinates.representative J
        (PhotonKernelLocalization.l2Multiplier χ hχm hb a) (B.multiplier χ w))
    (BF : StandardSymmetricFockExponential) (CCR : CanonicalSectorCCR photonMeasure)
    (BT : StandardNormalTraceBackground) (N k m : ℕ) {x : BT.FullTrace N}
    (hx : x ∈ (BT.realization (FullHilbert N)).rank.positive) :
    ((fullFormCalculus BF CCR BT PhysicalOnePhotonFourier.fourier N).observable
      (finiteFamily radiationFamily k)).expectation
      (BT.normal.extend ((fullFactorization BF PhysicalOnePhotonFourier.fourier N).factor
        (complexOnePhotonIsometry (radius m))) x) ≤
      ENNReal.ofReal (1 + (physicalRadiationFamily B J).error k m) *
        ((fullFormCalculus BF CCR BT PhysicalOnePhotonFourier.fourier N).observable
          radiationFamily).expectation x :=
  fullFormCalculus_sharp_radiation physicalRadiationCoordinates B J hmult BF CCR BT N k m rfl hx

end PhysicalCoordinates

end GptLean.PhysicalFock
