import GptLean.PhysicalFockRadiationFamily
import GptLean.PhysicalFockSectorEnergy

/-!
The constructed radiation kernel family gives exactly the physical Fock
momentum energy. Bounded shell multiplication commutes with the actual
Fubini and tail-basis maps. Nonnegative shell sums then identify the full
form, including infinite radiation energy.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhysicalL2HilbertSum PhotonLocalizationFormBounds
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false

def headDispersion (n : ℕ) (k : Fin (n + 1) → PhotonMode) : ℝ := ‖(k 0).1‖

theorem headDispersion_measurable (n : ℕ) : Measurable (headDispersion n) := by
  unfold headDispersion
  fun_prop

def headRadiationShell (n M : ℕ) : FullSector photonMeasure (n + 1) →L[ℂ]
    FullSector photonMeasure (n + 1) :=
  RadiationShells.multiplier (SectorMeasure photonMeasure (n + 1))
    (headDispersion n) (headDispersion_measurable n) M

theorem headShell_sections (n M : ℕ) (u : FullSector photonMeasure (n + 1)) :
    onePhotonSections n (headRadiationShell n M u) =
      (photonRadiationShell M).compLpL 2 (SectorMeasure photonMeasure n) (onePhotonSections n u) := by
  let P : FullSector photonMeasure (n + 1) →ₗᵢ[ℂ]
      Lp ℂ 2 ((SectorMeasure photonMeasure n).prod photonMeasure) :=
    Lp.compMeasurePreservingₗᵢ ℂ (tailHeadCoordinates n) (tailHeadCoordinates_measurePreserving n)
  have hp : P (headRadiationShell n M u) =ᵐ[(SectorMeasure photonMeasure n).prod photonMeasure]
      fun z => RadiationShells.weight photonDispersion M z.2 • P u z := by
    filter_upwards [Lp.coeFn_compMeasurePreserving (headRadiationShell n M u)
      (tailHeadCoordinates_measurePreserving n),
      Lp.coeFn_compMeasurePreserving u (tailHeadCoordinates_measurePreserving n),
      (tailHeadCoordinates_measurePreserving n).quasiMeasurePreserving.ae
        (RadiationShells.multiplier_ae (SectorMeasure photonMeasure (n + 1))
          (headDispersion n) (headDispersion_measurable n) M u)] with z hv hu ht
    have hhead : RadiationShells.weight (headDispersion n) M (tailHeadCoordinates n z) =
        RadiationShells.weight photonDispersion M z.2 := by
      simp [RadiationShells.weight, photonDispersion, headDispersion, tailHeadCoordinates,
        MeasurableEquiv.prodComm, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    exact hv.trans (ht.trans ((congrArg (fun c : ℝ => c • u (tailHeadCoordinates n z)) hhead).trans
      (congrArg (RadiationShells.weight photonDispersion M z.2 • ·) hu.symm)))
  have hcV := PhysicalSourceFubini.curryEquiv_represents_ae (P (headRadiationShell n M u))
  have hcU := PhysicalSourceFubini.curryEquiv_represents_ae (P u)
  have hcB := (photonRadiationShell M).coeFn_compLpL (onePhotonSections n u)
  apply Lp.ext
  filter_upwards [hcV, hcU, Measure.ae_ae_of_ae_prod hp, hcB] with x hv hu ht hb
  change PhysicalSourceFubini.curryEquiv (P (headRadiationShell n M u)) x = _
  rw [hb]
  apply Lp.ext
  filter_upwards [hv, hu, ht,
    RadiationShells.multiplier_ae photonMeasure photonDispersion photonDispersion_measurable
      M (onePhotonSections n u x)] with p hV hU hT hB
  exact hV.trans (hT.trans ((congrArg (RadiationShells.weight photonDispersion M p • ·) hU.symm).trans hB.symm))

theorem onePhotonSlices_shell_norm_sum (n M : ℕ) (u : Sector photonMeasure (n + 1)) :
    (∑' a, ENNReal.ofReal (‖photonRadiationShell M (onePhotonSlices n u a)‖ ^ 2)) =
      ENNReal.ofReal (‖headRadiationShell n M u.val‖ ^ 2) := by
  let W := spatialCoefficients (SectorMeasure photonMeasure n) (Lp ℂ 2 photonMeasure)
  let v := (photonRadiationShell M).compLpL 2 (SectorMeasure photonMeasure n) (onePhotonSections n u.val)
  have hcoord (a : ℕ) : W v a = photonRadiationShell M (onePhotonSlices n u a) :=
    spatialCoefficients_compLpL (SectorMeasure photonMeasure n) (Lp ℂ 2 photonMeasure)
      (photonRadiationShell M) (onePhotonSections n u.val) a
  have hs := coordinate_mass_hasSum (fun _ : ℕ => Lp ℂ 2 photonMeasure) (W v)
  have hn : ‖W v‖ = ‖headRadiationShell n M u.val‖ :=
    (W.norm_map v).trans ((congrArg norm (headShell_sections n M u.val).symm).trans
      ((onePhotonSections n).norm_map (headRadiationShell n M u.val)))
  calc
    _ = ∑' a, ENNReal.ofReal (‖W v a‖ ^ 2) :=
      tsum_congr (fun a => congrArg (fun q : Lp ℂ 2 photonMeasure => ENNReal.ofReal (‖q‖ ^ 2)) (hcoord a).symm)
    _ = ENNReal.ofReal (‖W v‖ ^ 2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun a => sq_nonneg _) hs.summable).symm.trans
        (congrArg ENNReal.ofReal hs.tsum_eq)
    _ = _ := congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) hn

theorem onePhotonSlices_radiation (n : ℕ) (u : Sector photonMeasure (n + 1)) :
    (∑' a, onePhotonFamilyValue radiationFamily (onePhotonSlices n u a)) =
      coordinateRadiationForm (0 : Fin (n + 1)) u := by
  have hval (v : Lp ℂ 2 photonMeasure) : onePhotonFamilyValue radiationFamily v =
      ∑' M, ENNReal.ofReal (‖photonRadiationShell M v‖ ^ 2) :=
    (radiationFamily_value v).trans
      (RadiationShells.multiplier_norm_sum photonMeasure photonDispersion photonDispersion_measurable
        (fun p => norm_nonneg p.1) v).symm
  calc
    _ = ∑' a, ∑' M, ENNReal.ofReal (‖photonRadiationShell M (onePhotonSlices n u a)‖ ^ 2) :=
      tsum_congr (fun a => hval (onePhotonSlices n u a))
    _ = ∑' M, ∑' a, ENNReal.ofReal (‖photonRadiationShell M (onePhotonSlices n u a)‖ ^ 2) :=
      ENNReal.tsum_comm
    _ = ∑' M, ENNReal.ofReal (‖headRadiationShell n M u.val‖ ^ 2) :=
      tsum_congr (fun M => onePhotonSlices_shell_norm_sum n M u)
    _ = _ := RadiationShells.multiplier_norm_sum (SectorMeasure photonMeasure (n + 1))
      (headDispersion n) (headDispersion_measurable n) (fun k => norm_nonneg (k 0).1) u.val

theorem fockSlices_radiationForm (u : PhotonFock) :
    fockForm (onePhotonFamilyValue radiationFamily) (fockSlices u) = radiationForm u := by
  unfold fockForm sectorForm radiationForm
  apply tsum_congr
  intro n
  cases n with
  | zero =>
    rw [sectorRadiationForm_sum_coordinates]
    simp
  | succ n =>
    simp only [fockSlices, onePhotonSlices_radiation, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Fintype.card_fin]
    exact (sectorRadiationForm_eq_coordinate (0 : Fin (n + 1)) (u (n + 1))).symm

section Normal
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData PhotonFock T}
  (normal : PhotonLocalizationChannel.NormalTraceData R)
  (F : PhotonLocalizationChannel.NormalFunctionalData R)

theorem radiationObservable_rankOne (u : PhotonFock) :
    (familyObservable normal F radiationFamily).expectation (R.rankOne u) = radiationForm u :=
  (familyObservable_slices normal F radiationFamily u).trans (fockSlices_radiationForm u)

end Normal
end GptLean.PhysicalFock
