import GptLean.PhysicalFockSeparable
import GptLean.PhysicalL2Countable
import GptLean.PhotonLocalizationFormBoundsLifting

/-!
Actual one-photon slices of the symmetric momentum-space sectors.

The head/tail coordinate equivalence and L² Fubini identify a sector with
an L² family of one-photon wave functions. Expanding the tail in its
countable Hilbert basis gives concrete slices and their exact Parseval
identity. No additive-Fock form identity is assumed for these slices.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal

instance photonMeasureSeparable : IsSeparable photonMeasure := by
  have : MeasurableSpace.CountablyGenerated PhotonMode := inferInstance
  infer_instance

instance photonSectorMeasureSeparable (n : ℕ) : IsSeparable (SectorMeasure photonMeasure n) := by
  have : MeasurableSpace.CountablyGenerated (Fin n → PhotonMode) := inferInstance
  infer_instance

/-- The actual coordinate map from tail/head variables back to the original photon labels. -/
def tailHeadCoordinates (n : ℕ) : ((Fin n → PhotonMode) × PhotonMode) ≃ᵐ
    (Fin (n + 1) → PhotonMode) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => PhotonMode) 0).symm

theorem tailHeadCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (tailHeadCoordinates n)
      ((SectorMeasure photonMeasure n).prod photonMeasure) (SectorMeasure photonMeasure (n + 1)) :=
  (MeasurePreserving.symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => PhotonMode) 0)
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => photonMeasure) 0)).comp
      Measure.measurePreserving_swap

/-- Sector wave functions as an L² family of actual one-photon L² vectors. -/
def onePhotonSections (n : ℕ) : FullSector photonMeasure (n + 1) →ₗᵢ[ℂ]
    Lp (Lp ℂ 2 photonMeasure) 2 (SectorMeasure photonMeasure n) :=
  PhysicalSourceFubini.curryIsometry.comp
    (Lp.compMeasurePreservingₗᵢ ℂ (tailHeadCoordinates n) (tailHeadCoordinates_measurePreserving n))

/-- The countable slices used for additive one-photon observables. -/
def onePhotonSlices (n : ℕ) : Sector photonMeasure (n + 1) →ₗᵢ[ℂ]
    lp (fun _ : ℕ => Lp ℂ 2 photonMeasure) 2 :=
  (PhysicalL2HilbertSum.spatialCoefficients (SectorMeasure photonMeasure n) (Lp ℂ 2 photonMeasure)).comp
    ((onePhotonSections n).comp (sectorInclusion photonMeasure (n + 1)))

theorem onePhotonSlices_mass (n : ℕ) (u : Sector photonMeasure (n + 1)) :
    HasSum (fun a => ‖onePhotonSlices n u a‖ ^ 2) (‖u‖ ^ 2) := by
  simpa only [(onePhotonSlices n).norm_map] using
    coordinate_mass_hasSum (fun _ : ℕ => Lp ℂ 2 photonMeasure) (onePhotonSlices n u)

/-- Symmetry permits the same head-coordinate expansion for each labelled photon. -/
def fockSlices (u : PhotonFock) : (m : ℕ) → Fin m → ℕ → Lp ℂ 2 photonMeasure
  | 0, i => Fin.elim0 i
  | n + 1, _ => onePhotonSlices n (u (n + 1))

theorem fockSlices_number (u : PhotonFock) :
    PhotonLocalizationFormBounds.fockForm (fun f : Lp ℂ 2 photonMeasure => ENNReal.ofReal (‖f‖ ^ 2))
      (fockSlices u) = photonNumberForm photonMeasure u := by
  unfold PhotonLocalizationFormBounds.fockForm PhotonLocalizationFormBounds.sectorForm
    photonNumberForm numberForm weightedForm
  apply tsum_congr
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have hm : (∑' a, ENNReal.ofReal (‖onePhotonSlices n (u (n + 1)) a‖ ^ 2)) =
        ENNReal.ofReal (‖u (n + 1)‖ ^ 2) := by
      simpa only [weightedForm, one_mul, (onePhotonSlices n).norm_map] using
        massForm_eq (fun _ : ℕ => Lp ℂ 2 photonMeasure) (onePhotonSlices n (u (n + 1)))
    simp only [fockSlices, hm, Finset.sum_const, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity)]
    norm_num [ENNReal.ofReal_add]

end GptLean.PhysicalFock
