import GptLean.PhysicalFockSoftRadiation
import GptLean.PhysicalFockRadiationSlices
import GptLean.PhysicalFockChannelAnnihilation

/-!
The orthogonal soft projection carries exactly the soft momentum energy.
The bounded one-photon soft square root commutes with actual Fubini slices.
Parseval and the full additive-form pullback identify the sum of retained
radiation forms and give the sharper soft annihilation estimate.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhysicalL2HilbertSum PhotonLocalizationFormBounds
open PhotonLocalizationChannel PhysicalNormalTrace PhotonLocalizationFockChannel
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

theorem softFrequency_le_max (κ : ℝ) (p : PhotonMode) : softFrequency κ p ≤ max κ 0 := by
  classical
  by_cases hp : p ∈ softMomentumSet κ
  · rw [softFrequency, Set.indicator_of_mem hp]
    exact (le_of_lt hp).trans (le_max_left _ _)
  · rw [softFrequency, Set.indicator_of_notMem hp]
    exact le_max_right _ _

def softFrequencyRoot (κ : ℝ) : Lp ℂ 2 photonMeasure →L[ℂ] Lp ℂ 2 photonMeasure :=
  PhotonLocalization.realL2Multiplier (fun p => Real.sqrt (softFrequency κ p))
    (softFrequency_measurable κ).sqrt.aestronglyMeasurable (Real.sqrt (max κ 0))
    (ae_of_all _ fun p => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (softFrequency_le_max κ p))

theorem softFrequencyRoot_ae (κ : ℝ) (v : Lp ℂ 2 photonMeasure) :
    softFrequencyRoot κ v =ᵐ[photonMeasure] fun p => Real.sqrt (softFrequency κ p) • v p :=
  PhotonLocalization.realL2Multiplier_apply _ _ _ _ v

theorem softFrequencyRoot_norm_integral (κ : ℝ) (v : Lp ℂ 2 photonMeasure) :
    ENNReal.ofReal (‖softFrequencyRoot κ v‖ ^ 2) =
      ∫⁻ p, NormalPhoton.softWeight κ p * ENNReal.ofReal (‖v p‖ ^ 2) ∂photonMeasure := by
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral,
    ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
      (ae_of_all _ fun p => sq_nonneg _)]
  apply lintegral_congr_ae
  filter_upwards [softFrequencyRoot_ae κ v] with p hp
  rw [hp, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (softFrequency_nonneg κ p),
    ENNReal.ofReal_mul (softFrequency_nonneg κ p), ofReal_softFrequency]

theorem radiationFamily_soft_projection (κ : ℝ) (v : Lp ℂ 2 photonMeasure) :
    onePhotonFamilyValue radiationFamily
      (MomentumSplit.projection photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ) v) =
        ENNReal.ofReal (‖softFrequencyRoot κ v‖ ^ 2) := by
  rw [radiationFamily_value, softFrequencyRoot_norm_integral]
  apply lintegral_congr_ae
  filter_upwards [MomentumSplit.projection_ae photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ) v] with p hp
  rw [hp]
  classical
  by_cases hm : p ∈ softMomentumSet κ
  · simp only [Set.indicator_of_mem hm]
    change NormalPhoton.frequency p < κ at hm
    rw [NormalPhoton.softWeight,
      Set.indicator_of_mem (s := {p : PhotonMode | NormalPhoton.frequency p < κ})
        (a := p) hm]
    rfl
  · simp only [Set.indicator_of_notMem hm, norm_zero, zero_pow (by decide : 2 ≠ 0),
      ENNReal.ofReal_zero, mul_zero]
    change ¬ NormalPhoton.frequency p < κ at hm
    rw [NormalPhoton.softWeight,
      Set.indicator_of_notMem (s := {p : PhotonMode | NormalPhoton.frequency p < κ})
        (a := p) hm, zero_mul]

def headSoftRoot (κ : ℝ) (n : ℕ) :
    FullSector photonMeasure (n + 1) →L[ℂ] FullSector photonMeasure (n + 1) :=
  PhotonLocalization.realL2Multiplier (fun k => Real.sqrt (softFrequency κ (k 0)))
    ((softFrequency_measurable κ).comp (measurable_pi_apply 0)).sqrt.aestronglyMeasurable
    (Real.sqrt (max κ 0)) (ae_of_all _ fun k => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (softFrequency_le_max κ (k 0)))

theorem headSoftRoot_ae (κ : ℝ) (n : ℕ) (u : FullSector photonMeasure (n + 1)) :
    headSoftRoot κ n u =ᵐ[SectorMeasure photonMeasure (n + 1)]
      fun k => Real.sqrt (softFrequency κ (k 0)) • u k :=
  PhotonLocalization.realL2Multiplier_apply _ _ _ _ u

theorem headSoftRoot_sections (κ : ℝ) (n : ℕ) (u : FullSector photonMeasure (n + 1)) :
    onePhotonSections n (headSoftRoot κ n u) =
      (softFrequencyRoot κ).compLpL 2 (SectorMeasure photonMeasure n) (onePhotonSections n u) := by
  let P : FullSector photonMeasure (n + 1) →ₗᵢ[ℂ]
      Lp ℂ 2 ((SectorMeasure photonMeasure n).prod photonMeasure) :=
    Lp.compMeasurePreservingₗᵢ ℂ (tailHeadCoordinates n) (tailHeadCoordinates_measurePreserving n)
  have hp : P (headSoftRoot κ n u) =ᵐ[(SectorMeasure photonMeasure n).prod photonMeasure]
      fun z => Real.sqrt (softFrequency κ z.2) • P u z := by
    filter_upwards [Lp.coeFn_compMeasurePreserving (headSoftRoot κ n u)
      (tailHeadCoordinates_measurePreserving n),
      Lp.coeFn_compMeasurePreserving u (tailHeadCoordinates_measurePreserving n),
      (tailHeadCoordinates_measurePreserving n).quasiMeasurePreserving.ae
        (headSoftRoot_ae κ n u)] with z hv hu ht
    have hhead : (tailHeadCoordinates n z) 0 = z.2 := by
      simp [tailHeadCoordinates, MeasurableEquiv.prodComm,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    exact hv.trans (ht.trans ((congrArg (fun p : PhotonMode =>
      Real.sqrt (softFrequency κ p) • u (tailHeadCoordinates n z)) hhead).trans
      (congrArg (Real.sqrt (softFrequency κ z.2) • ·) hu.symm)))
  have hcV := PhysicalSourceFubini.curryEquiv_represents_ae (P (headSoftRoot κ n u))
  have hcU := PhysicalSourceFubini.curryEquiv_represents_ae (P u)
  have hcB := (softFrequencyRoot κ).coeFn_compLpL (onePhotonSections n u)
  apply Lp.ext
  filter_upwards [hcV, hcU, Measure.ae_ae_of_ae_prod hp, hcB] with x hv hu ht hb
  change PhysicalSourceFubini.curryEquiv (P (headSoftRoot κ n u)) x = _
  rw [hb]
  apply Lp.ext
  filter_upwards [hv, hu, ht, softFrequencyRoot_ae κ (onePhotonSections n u x)]
    with p hV hU hT hB
  exact hV.trans (hT.trans ((congrArg (Real.sqrt (softFrequency κ p) • ·) hU.symm).trans hB.symm))

theorem onePhotonSlices_softRoot_norm_sum (κ : ℝ) (n : ℕ)
    (u : Sector photonMeasure (n + 1)) :
    (∑' a, ENNReal.ofReal (‖softFrequencyRoot κ (onePhotonSlices n u a)‖ ^ 2)) =
      ENNReal.ofReal (‖headSoftRoot κ n u.val‖ ^ 2) := by
  let W := spatialCoefficients (SectorMeasure photonMeasure n) (Lp ℂ 2 photonMeasure)
  let v := (softFrequencyRoot κ).compLpL 2 (SectorMeasure photonMeasure n) (onePhotonSections n u.val)
  have hcoord (a : ℕ) : W v a = softFrequencyRoot κ (onePhotonSlices n u a) :=
    spatialCoefficients_compLpL (SectorMeasure photonMeasure n) (Lp ℂ 2 photonMeasure)
      (softFrequencyRoot κ) (onePhotonSections n u.val) a
  have hs := coordinate_mass_hasSum (fun _ : ℕ => Lp ℂ 2 photonMeasure) (W v)
  have hn : ‖W v‖ = ‖headSoftRoot κ n u.val‖ :=
    (W.norm_map v).trans ((congrArg norm (headSoftRoot_sections κ n u.val).symm).trans
      ((onePhotonSections n).norm_map (headSoftRoot κ n u.val)))
  calc
    _ = ∑' a, ENNReal.ofReal (‖W v a‖ ^ 2) :=
      tsum_congr fun a => congrArg (fun t : Lp ℂ 2 photonMeasure => ENNReal.ofReal (‖t‖ ^ 2)) (hcoord a).symm
    _ = ENNReal.ofReal (‖W v‖ ^ 2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun a => sq_nonneg _) hs.summable).symm.trans
        (congrArg ENNReal.ofReal hs.tsum_eq)
    _ = _ := congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) hn

theorem headSoftRoot_norm_moment (κ : ℝ) (n : ℕ) (u : Sector photonMeasure (n + 1)) :
    ENNReal.ofReal (‖headSoftRoot κ n u.val‖ ^ 2) =
      coordinatePhotonMoment (NormalPhoton.softWeight κ) (0 : Fin (n + 1)) u := by
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral,
    ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
      (ae_of_all _ fun k => sq_nonneg _)]
  unfold coordinatePhotonMoment
  apply lintegral_congr_ae
  filter_upwards [headSoftRoot_ae κ n u.val] with k hk
  rw [hk, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (softFrequency_nonneg κ (k 0)),
    ENNReal.ofReal_mul (softFrequency_nonneg κ (k 0)), ofReal_softFrequency]

theorem fockSlices_softRadiation (κ : ℝ) (u : PhotonFock) :
    fockForm (fun v => onePhotonFamilyValue radiationFamily
      (MomentumSplit.projection photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ) v))
      (fockSlices u) = photonMoment (NormalPhoton.softWeight κ) u := by
  unfold fockForm sectorForm photonMoment
  apply tsum_congr
  intro n
  cases n with
  | zero => simp [sectorPhotonMoment]
  | succ n =>
    simp only [fockSlices, radiationFamily_soft_projection, onePhotonSlices_softRoot_norm_sum,
      headSoftRoot_norm_moment, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    exact (sectorPhotonMoment_eq_coordinate _ (NormalPhoton.softWeight_measurable κ)
      (0 : Fin (n + 1)) (u (n + 1))).symm

section Normal

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData PhotonFock T}
  (normal : NormalTraceData R) (F : NormalFunctionalData R)
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)

include normal F C in
/-- The actual soft split carries exactly the source soft radiation moment. -/
theorem softSplit_radiation_sum (κ : ℝ) (u : PhotonFock) :
    (∑' a, radiationForm ((photonFactorization BF).factor
      (MomentumSplit.split photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ)) u a)) =
        photonMoment (NormalPhoton.softWeight κ) u := by
  have h := familyObservable_pullback normal F BF C
    (MomentumSplit.split photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ))
    radiationFamily u
  simp only [radiationObservable_rankOne, MomentumSplit.retained_split] at h
  exact h.trans (fockSlices_softRadiation κ u)

include normal F BF C in
/-- Soft annihilation is controlled by soft energy alone. -/
theorem kernelAnnihilation_soft_bound (κ : ℝ) (k : WeightedPhotonKernel)
    (hk : k.val.1 ∈ softOnePhoton κ) (q : RadiationGraphSpace) :
    ‖kernelAnnihilation k q‖ ≤ ‖k.val.2‖ * ‖softRadiationRoot κ q‖ := by
  let j := MomentumSplit.split photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ)
  let u := radiationGraphInclusion q
  have hs := softSplit_radiation_sum normal F BF C κ u
  have hfinite (a : ℕ) : radiationForm ((photonFactorization BF).factor j u a) < ⊤ := by
    apply (ENNReal.le_tsum a).trans_lt
    exact hs.symm ▸ softRadiation_finite κ q
  have hadj : (retainedMap j).adjoint k.val.1 = k.val.1 := by
    change (MomentumSplit.projection photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ)).adjoint k.val.1 = _
    rw [MomentumSplit.projection_adjoint]
    exact MomentumSplit.projection_of_supported _ _ _ ⟨k.val.1, hk⟩
  have hann := photonFactorization_annihilationForm BF C j k.val.1 u
  rw [hadj] at hann
  have hb : annihilationForm photonMeasure k.val.1 u ≤
      ENNReal.ofReal (‖k.val.2‖ ^ 2) * photonMoment (NormalPhoton.softWeight κ) u := by
    rw [← hann, ← hs, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun a =>
      annihilation_sector_tsum_bound k.val.1 k.val.2 k.property _ (hfinite a)
  have hm : annihilationForm photonMeasure k.val.1 u =
      ENNReal.ofReal (‖kernelAnnihilation k q‖ ^ 2) := by
    change (∑' n, ENNReal.ofReal (‖kernelAnnihilation k q n‖ ^ 2)) = _
    simpa only [weightedForm, one_mul] using
      massForm_eq (Sector photonMeasure) (kernelAnnihilation k q)
  rw [hm, softRadiationRoot_energy, ← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow] at hb
  have he := (ENNReal.ofReal_le_ofReal_iff
    (sq_nonneg (‖k.val.2‖ * ‖softRadiationRoot κ q‖))).mp hb
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp he

end Normal
end GptLean.PhysicalFock
