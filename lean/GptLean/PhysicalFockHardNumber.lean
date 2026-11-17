import GptLean.PhysicalFockSoftRadiationBound

/-!
The retained complement channel carries exactly the original hard photon
number. Bounded momentum projections, actual Fubini slices and Parseval
prove the vector identity. Normal channel extension then proves it for
every positive normal state, without a finite-number assumption.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory PhysicalL2HilbertSum PhotonLocalizationFormBounds
open PhotonLocalizationChannel PhysicalNormalTrace PhotonLocalizationFockChannel
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

def hardCutoff (κ : ℝ) : PhotonMode → ℝ :=
  MomentumSplit.weight (softMomentumSet κ)ᶜ

theorem hardCutoff_measurable (κ : ℝ) : Measurable (hardCutoff κ) :=
  MomentumSplit.weight_measurable _ (softMomentumSet_measurable κ).compl

theorem hardCutoff_bound (κ : ℝ) (p : PhotonMode) : |hardCutoff κ p| ≤ 1 :=
  MomentumSplit.weight_bound _ p

theorem hardCutoff_norm_sq (κ : ℝ) (p : PhotonMode) (z : ℂ) :
    ENNReal.ofReal (‖hardCutoff κ p • z‖ ^ 2) =
      NormalPhoton.hardWeight κ p * ENNReal.ofReal (‖z‖ ^ 2) := by
  classical
  by_cases hp : κ ≤ NormalPhoton.frequency p <;>
    simp [hardCutoff, MomentumSplit.weight, softMomentumSet, NormalPhoton.hardWeight,
      not_lt, hp]

def hardNumberRoot (κ : ℝ) : Lp ℂ 2 photonMeasure →L[ℂ] Lp ℂ 2 photonMeasure :=
  MomentumSplit.projection photonMeasure (softMomentumSet κ)ᶜ
    (softMomentumSet_measurable κ).compl

theorem hardNumberRoot_ae (κ : ℝ) (u : Lp ℂ 2 photonMeasure) :
    hardNumberRoot κ u =ᵐ[photonMeasure] fun p => hardCutoff κ p • u p :=
  PhotonLocalization.realL2Multiplier_apply
    (MomentumSplit.weight (softMomentumSet κ)ᶜ)
    (MomentumSplit.weight_measurable (softMomentumSet κ)ᶜ
      (softMomentumSet_measurable κ).compl).aestronglyMeasurable
    1 (ae_of_all _ (MomentumSplit.weight_bound (softMomentumSet κ)ᶜ)) u

theorem hardNumberRoot_norm_integral (κ : ℝ) (u : Lp ℂ 2 photonMeasure) :
    ENNReal.ofReal (‖hardNumberRoot κ u‖ ^ 2) =
      ∫⁻ p, NormalPhoton.hardWeight κ p * ENNReal.ofReal (‖u p‖ ^ 2) ∂photonMeasure := by
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral,
    ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
      (ae_of_all _ fun _ => sq_nonneg _)]
  apply lintegral_congr_ae
  filter_upwards [hardNumberRoot_ae κ u] with p hp
  exact (congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)) hp).trans
    (hardCutoff_norm_sq κ p (u p))

def headHardNumberRoot (κ : ℝ) (n : ℕ) :
    FullSector photonMeasure (n + 1) →L[ℂ] FullSector photonMeasure (n + 1) :=
  PhotonLocalization.realL2Multiplier (fun k => hardCutoff κ (k 0))
    ((hardCutoff_measurable κ).comp (measurable_pi_apply 0)).aestronglyMeasurable
    1 (ae_of_all _ fun k => hardCutoff_bound κ (k 0))

theorem headHardNumberRoot_ae (κ : ℝ) (n : ℕ) (u : FullSector photonMeasure (n + 1)) :
    headHardNumberRoot κ n u =ᵐ[SectorMeasure photonMeasure (n + 1)]
      fun k => hardCutoff κ (k 0) • u k :=
  PhotonLocalization.realL2Multiplier_apply _ _ _ _ u

theorem headHardNumberRoot_sections (κ : ℝ) (n : ℕ) (u : FullSector photonMeasure (n + 1)) :
    onePhotonSections n (headHardNumberRoot κ n u) =
      (hardNumberRoot κ).compLpL 2 (SectorMeasure photonMeasure n) (onePhotonSections n u) := by
  let P : FullSector photonMeasure (n + 1) →ₗᵢ[ℂ]
      Lp ℂ 2 ((SectorMeasure photonMeasure n).prod photonMeasure) :=
    Lp.compMeasurePreservingₗᵢ ℂ (tailHeadCoordinates n) (tailHeadCoordinates_measurePreserving n)
  have hp : P (headHardNumberRoot κ n u) =ᵐ[(SectorMeasure photonMeasure n).prod photonMeasure]
      fun z => hardCutoff κ z.2 • P u z := by
    filter_upwards [Lp.coeFn_compMeasurePreserving (headHardNumberRoot κ n u)
      (tailHeadCoordinates_measurePreserving n),
      Lp.coeFn_compMeasurePreserving u (tailHeadCoordinates_measurePreserving n),
      (tailHeadCoordinates_measurePreserving n).quasiMeasurePreserving.ae
        (headHardNumberRoot_ae κ n u)] with z hv hu ht
    have hhead : (tailHeadCoordinates n z) 0 = z.2 := by
      simp [tailHeadCoordinates, MeasurableEquiv.prodComm,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    exact hv.trans (ht.trans ((congrArg (fun p : PhotonMode =>
      hardCutoff κ p • u (tailHeadCoordinates n z)) hhead).trans
        (congrArg (hardCutoff κ z.2 • ·) hu.symm)))
  have hcV := PhysicalSourceFubini.curryEquiv_represents_ae (P (headHardNumberRoot κ n u))
  have hcU := PhysicalSourceFubini.curryEquiv_represents_ae (P u)
  have hcB := (hardNumberRoot κ).coeFn_compLpL (onePhotonSections n u)
  apply Lp.ext
  filter_upwards [hcV, hcU, Measure.ae_ae_of_ae_prod hp, hcB] with x hv hu ht hb
  change PhysicalSourceFubini.curryEquiv (P (headHardNumberRoot κ n u)) x = _
  rw [hb]
  apply Lp.ext
  filter_upwards [hv, hu, ht, hardNumberRoot_ae κ (onePhotonSections n u x)]
    with p hV hU hT hB
  exact hV.trans (hT.trans ((congrArg (hardCutoff κ p • ·) hU.symm).trans hB.symm))

theorem onePhotonSlices_hardNumberRoot_norm_sum (κ : ℝ) (n : ℕ)
    (u : Sector photonMeasure (n + 1)) :
    (∑' a, ENNReal.ofReal (‖hardNumberRoot κ (onePhotonSlices n u a)‖ ^ 2)) =
      ENNReal.ofReal (‖headHardNumberRoot κ n u.val‖ ^ 2) := by
  let W := spatialCoefficients (SectorMeasure photonMeasure n) (Lp ℂ 2 photonMeasure)
  let v := (hardNumberRoot κ).compLpL 2 (SectorMeasure photonMeasure n) (onePhotonSections n u.val)
  have hcoord (a : ℕ) : W v a = hardNumberRoot κ (onePhotonSlices n u a) :=
    spatialCoefficients_compLpL (SectorMeasure photonMeasure n) (Lp ℂ 2 photonMeasure)
      (hardNumberRoot κ) (onePhotonSections n u.val) a
  have hs := coordinate_mass_hasSum (fun _ : ℕ => Lp ℂ 2 photonMeasure) (W v)
  have hn : ‖W v‖ = ‖headHardNumberRoot κ n u.val‖ :=
    (W.norm_map v).trans ((congrArg norm (headHardNumberRoot_sections κ n u.val).symm).trans
      ((onePhotonSections n).norm_map (headHardNumberRoot κ n u.val)))
  calc
    _ = ∑' a, ENNReal.ofReal (‖W v a‖ ^ 2) :=
      tsum_congr fun a => congrArg (fun t : Lp ℂ 2 photonMeasure => ENNReal.ofReal (‖t‖ ^ 2))
        (hcoord a).symm
    _ = ENNReal.ofReal (‖W v‖ ^ 2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun a => sq_nonneg _) hs.summable).symm.trans
        (congrArg ENNReal.ofReal hs.tsum_eq)
    _ = _ := congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) hn

theorem headHardNumberRoot_norm_moment (κ : ℝ) (n : ℕ) (u : Sector photonMeasure (n + 1)) :
    ENNReal.ofReal (‖headHardNumberRoot κ n u.val‖ ^ 2) =
      coordinatePhotonMoment (NormalPhoton.hardWeight κ) (0 : Fin (n + 1)) u := by
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral,
    ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
      (ae_of_all _ fun _ => sq_nonneg _)]
  apply lintegral_congr_ae
  filter_upwards [headHardNumberRoot_ae κ n u.val] with k hk
  exact (congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)) hk).trans
    (hardCutoff_norm_sq κ (k 0) (u.val k))

theorem fockSlices_hardNumber (κ : ℝ) (u : PhotonFock) :
    fockForm (fun v => onePhotonFamilyValue numberFamily
      (MomentumSplit.projection photonMeasure (softMomentumSet κ)ᶜ
        (softMomentumSet_measurable κ).compl v)) (fockSlices u) =
          photonMoment (NormalPhoton.hardWeight κ) u := by
  unfold fockForm sectorForm photonMoment
  apply tsum_congr
  intro n
  cases n with
  | zero => simp [sectorPhotonMoment]
  | succ n =>
    simp only [fockSlices, numberFamily_value]
    change (∑ _ : Fin (n + 1), ∑' a,
      ENNReal.ofReal (‖hardNumberRoot κ (onePhotonSlices n (u (n + 1)) a)‖ ^ 2)) = _
    rw [onePhotonSlices_hardNumberRoot_norm_sum, headHardNumberRoot_norm_moment]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    exact (sectorPhotonMoment_eq_coordinate _ (NormalPhoton.hardWeight_measurable κ)
      (0 : Fin (n + 1)) (u (n + 1))).symm

section Normal

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData PhotonFock T}
  (normal : NormalTraceData R) (F : NormalFunctionalData R)
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)

include normal F C in
theorem hardSplit_number_sum (κ : ℝ) (u : PhotonFock) :
    (∑' a, photonNumberForm photonMeasure ((photonFactorization BF).factor
      (MomentumSplit.split photonMeasure (softMomentumSet κ)ᶜ
        (softMomentumSet_measurable κ).compl) u a)) =
          photonMoment (NormalPhoton.hardWeight κ) u := by
  have h := familyObservable_pullback normal F BF C
    (MomentumSplit.split photonMeasure (softMomentumSet κ)ᶜ
      (softMomentumSet_measurable κ).compl) numberFamily u
  simp only [numberObservable_rankOne, MomentumSplit.retained_split] at h
  exact h.trans (fockSlices_hardNumber κ u)

include C in
/-- The retained hard number is the original hard-number moment on the same normal state. -/
theorem hardSplit_number_expectation (κ : ℝ) (x : T) (hx : x ∈ R.positive) :
    (NormalPhoton.numberForm normal F).expectation
      (normal.extend ((photonFactorization BF).factor
        (MomentumSplit.split photonMeasure (softMomentumSet κ)ᶜ
          (softMomentumSet_measurable κ).compl)) x) =
            (NormalPhoton.hardNumberForm normal F κ).expectation x := by
  apply channel_form_eq normal (NormalPhoton.numberForm normal F)
    (NormalPhoton.hardNumberForm normal F κ) (fun _ h => h) _ _ hx
  intro u
  simp only [NormalPhoton.numberForm_rankOne, NormalPhoton.hardNumberForm,
    secondQuantizedPositiveForm_rankOne]
  exact hardSplit_number_sum normal F BF C κ u

end Normal
end GptLean.PhysicalFock
