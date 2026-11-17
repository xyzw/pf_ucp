import GptLean.PhysicalFockSectors
import GptLean.PhotonKernelLocalization
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
The actual momentum radiation form on the constructed bosonic Fock space.

In the n-photon sector the dispersion is the sum of the n momentum
lengths. The quadratic form is its nonnegative integral against the
wave-function density, with infinity retained. The full form is the
sum over number sectors. Hard momentum support gives the number bound
by a pointwise inequality, rather than a supplied form estimate.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal

def sectorDispersion (n : ℕ) (k : Fin n → PhotonMode) : ℝ :=
  ∑ i, ‖(k i).1‖

theorem sectorDispersion_nonneg (n : ℕ) (k : Fin n → PhotonMode) :
    0 ≤ sectorDispersion n k := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem sectorDispersion_measurable (n : ℕ) : Measurable (sectorDispersion n) := by
  unfold sectorDispersion
  fun_prop

theorem sectorDispersion_lower {κ : ℝ} (n : ℕ) (k : Fin n → PhotonMode)
    (hk : ∀ i, κ ≤ ‖(k i).1‖) : (n : ℝ) * κ ≤ sectorDispersion n k := by
  calc (n : ℝ) * κ = ∑ _ : Fin n, κ := by simp
       _ ≤ sectorDispersion n k := Finset.sum_le_sum fun i _ => hk i

/-- The physical radiation form in one symmetric momentum sector. -/
def sectorRadiationForm (n : ℕ) (u : Sector photonMeasure n) : ℝ≥0∞ :=
  ∫⁻ k, ENNReal.ofReal (sectorDispersion n k) * ENNReal.ofReal (‖u.val k‖ ^ 2)
    ∂SectorMeasure photonMeasure n

theorem sectorRadiationForm_integral (n : ℕ) (u : Sector photonMeasure n)
    (hi : Integrable (fun k => sectorDispersion n k * ‖u.val k‖ ^ 2)
      (SectorMeasure photonMeasure n)) :
    sectorRadiationForm n u =
      ENNReal.ofReal (∫ k, sectorDispersion n k * ‖u.val k‖ ^ 2
        ∂SectorMeasure photonMeasure n) := by
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun k => mul_nonneg (sectorDispersion_nonneg n k) (sq_nonneg _))]
  unfold sectorRadiationForm
  congr 1
  ext k
  exact (ENNReal.ofReal_mul (sectorDispersion_nonneg n k)).symm

theorem sector_mass_lintegral (n : ℕ) (u : Sector photonMeasure n) :
    (∫⁻ k, ENNReal.ofReal (‖u.val k‖ ^ 2) ∂SectorMeasure photonMeasure n) =
      ENNReal.ofReal (‖u‖ ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u.val)).mp (Lp.memLp u.val))
    (ae_of_all _ fun k => sq_nonneg _), ← PhotonKernelLocalization.l2_norm_sq_eq_integral]
  rfl

/-- The wave function vanishes whenever at least one photon momentum is soft. -/
def SectorHardSupported (κ : ℝ) (n : ℕ) (u : Sector photonMeasure n) : Prop :=
  ∀ᵐ k ∂SectorMeasure photonMeasure n, u.val k ≠ 0 → ∀ i, κ ≤ ‖(k i).1‖

theorem sectorRadiationForm_hard_lower {κ : ℝ} (n : ℕ) (u : Sector photonMeasure n)
    (hu : SectorHardSupported κ n u) :
    ENNReal.ofReal ((n : ℝ) * κ) * ENNReal.ofReal (‖u‖ ^ 2) ≤
      sectorRadiationForm n u := by
  rw [← sector_mass_lintegral n u,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hu] with k hk
  by_cases hz : u.val k = 0
  · simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, ENNReal.ofReal_zero, mul_zero, le_refl]
  · gcongr
    exact sectorDispersion_lower n k (hk hz)

/-- Radiation energy is summed over all symmetric photon sectors. -/
def radiationForm (u : PhotonFock) : ℝ≥0∞ := ∑' n, sectorRadiationForm n (u n)

def HardSupported (κ : ℝ) (u : PhotonFock) : Prop :=
  ∀ n, SectorHardSupported κ n (u n)

theorem radiationForm_hard_lower {κ : ℝ} (u : PhotonFock)
    (hu : HardSupported κ u) :
    ENNReal.ofReal κ * photonNumberForm photonMeasure u ≤ radiationForm u := by
  change ENNReal.ofReal κ * (∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * ‖u n‖ ^ 2)) ≤
    ∑' n, sectorRadiationForm n (u n)
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  have he : ENNReal.ofReal κ * ENNReal.ofReal ((n : ℝ) * ‖u n‖ ^ 2) =
      ENNReal.ofReal ((n : ℝ) * κ) * ENNReal.ofReal (‖u n‖ ^ 2) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n),
      ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    ac_rfl
  rw [he]
  exact sectorRadiationForm_hard_lower n (u n) (hu n)

/-- The usual infrared number control is proved on the actual momentum model. -/
theorem number_le_inv_mul_radiation {κ : ℝ} (hκ : 0 < κ) (u : PhotonFock)
    (hu : HardSupported κ u) :
    photonNumberForm photonMeasure u ≤ ENNReal.ofReal κ⁻¹ * radiationForm u := by
  have h : (ENNReal.ofReal κ)⁻¹ *
      (ENNReal.ofReal κ * photonNumberForm photonMeasure u) ≤
      (ENNReal.ofReal κ)⁻¹ * radiationForm u := by
    gcongr
    exact radiationForm_hard_lower u hu
  rw [ENNReal.inv_mul_cancel_left (ENNReal.ofReal_ne_zero_iff.mpr hκ) ENNReal.ofReal_ne_top] at h
  simpa only [ENNReal.ofReal_inv_of_pos hκ] using h

theorem number_finite_of_hard_radiation {κ : ℝ} (hκ : 0 < κ) (u : PhotonFock)
    (hu : HardSupported κ u) (hE : radiationForm u < ⊤) :
    photonNumberForm photonMeasure u < ⊤ :=
  (number_le_inv_mul_radiation hκ u hu).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE)

@[simp] theorem sectorRadiationForm_zero (n : ℕ) : sectorRadiationForm n 0 = 0 := by
  unfold sectorRadiationForm
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [Lp.coeFn_zero ℂ 2 (SectorMeasure photonMeasure n)] with k hk
  change ENNReal.ofReal (sectorDispersion n k) * ENNReal.ofReal (‖(0 : FullSector photonMeasure n) k‖ ^ 2) = 0
  simp only [hk, Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, ENNReal.ofReal_zero, mul_zero]

theorem radiationForm_sector (n : ℕ) (u : PhotonFock) :
    radiationForm (photonSector photonMeasure n u) = sectorRadiationForm n (u n) := by
  unfold radiationForm photonSector
  rw [tsum_eq_single n]
  · rw [sector_coordinate]
  · intro m hmn
    rw [sector_coordinate_ne _ n m hmn, sectorRadiationForm_zero]

end GptLean.PhysicalFock
