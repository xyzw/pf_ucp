import GptLean.PhysicalFockMomentumSupport
import GptLean.PhysicalFockHardSoftVacuum

/-!
The hard-vacuum embedding has actual hard momentum support. Its soft
momentum energy vanishes, and its number form is bounded by the actual
radiation form with the inverse frequency cutoff. The same statements
hold for the actual normal rank-one momentum forms.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationChannel PhysicalNormalTrace RemovalState
open Filter Topology
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

theorem sectorPhotonMoment_softWeight_eq_zero (κ : ℝ) (n : ℕ)
    (u : Sector photonMeasure n) (hu : SectorHardSupported κ n u) :
    sectorPhotonMoment (NormalPhoton.softWeight κ) n u = 0 := by
  unfold sectorPhotonMoment
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hu] with k hk
  by_cases hz : u.val k = 0
  · simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero, mul_zero, Pi.zero_apply]
  · have hsum : (∑ i : Fin n, NormalPhoton.softWeight κ (k i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi : ¬NormalPhoton.frequency (k i) < κ := not_lt.mpr (hk hz i)
      simp [NormalPhoton.softWeight, hi]
    simp only [hsum, zero_mul, Pi.zero_apply]

/-- A hard-supported Fock vector has zero actual soft momentum energy. -/
theorem photonMoment_softWeight_eq_zero (κ : ℝ) (u : PhotonFock)
    (hu : HardSupported κ u) : photonMoment (NormalPhoton.softWeight κ) u = 0 := by
  unfold photonMoment
  exact ENNReal.tsum_eq_zero.mpr fun n => sectorPhotonMoment_softWeight_eq_zero κ n (u n) (hu n)

/-- The constructed inverse split with soft vacuum lands in actual hard support. -/
theorem hardPhotonVacuumEmbedding_hardSupported
    (BF : StandardSymmetricFockExponential) (κ : ℝ)
    (u : generatedFockSubspace (hardOnePhoton κ)) :
    HardSupported κ (hardPhotonVacuumEmbedding BF κ u) := by
  rw [hardPhotonVacuumEmbedding_apply]
  exact hardSupported_of_mem_generated κ u.val u.property

theorem hardPhotonVacuumEmbedding_softEnergy
    (BF : StandardSymmetricFockExponential) (κ : ℝ)
    (u : generatedFockSubspace (hardOnePhoton κ)) :
    photonMoment (NormalPhoton.softWeight κ) (hardPhotonVacuumEmbedding BF κ u) = 0 :=
  photonMoment_softWeight_eq_zero κ _ (hardPhotonVacuumEmbedding_hardSupported BF κ u)

/-- The number bound applies to the actual radiation form of the inserted vector. -/
theorem hardPhotonVacuumEmbedding_number_le
    (BF : StandardSymmetricFockExponential) {κ : ℝ} (hκ : 0 < κ)
    (u : generatedFockSubspace (hardOnePhoton κ)) :
    photonNumberForm photonMeasure (hardPhotonVacuumEmbedding BF κ u) ≤
      ENNReal.ofReal κ⁻¹ * radiationForm (hardPhotonVacuumEmbedding BF κ u) :=
  number_le_inv_mul_radiation hκ _ (hardPhotonVacuumEmbedding_hardSupported BF κ u)

theorem hardPhotonVacuumEmbedding_number_finite
    (BF : StandardSymmetricFockExponential) {κ : ℝ} (hκ : 0 < κ)
    (u : generatedFockSubspace (hardOnePhoton κ))
    (hE : radiationForm (hardPhotonVacuumEmbedding BF κ u) < ⊤) :
    photonNumberForm photonMeasure (hardPhotonVacuumEmbedding BF κ u) < ⊤ :=
  number_finite_of_hard_radiation hκ _
    (hardPhotonVacuumEmbedding_hardSupported BF κ u) hE

section NormalForms

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData PhotonFock T}
  (normal : NormalTraceData R) (F : NormalFunctionalData R)

theorem hardSupported_normal_softEnergy (κ : ℝ) (u : PhotonFock)
    (hu : HardSupported κ u) :
    (NormalPhoton.softEnergyForm normal F κ).expectation (R.rankOne u) = 0 := by
  rw [NormalPhoton.softEnergyForm, secondQuantizedPositiveForm_rankOne]
  exact photonMoment_softWeight_eq_zero κ u hu

theorem hardSupported_normal_number_le {κ : ℝ} (hκ : 0 < κ) (u : PhotonFock)
    (hu : HardSupported κ u) :
    (NormalPhoton.numberForm normal F).expectation (R.rankOne u) ≤
      ENNReal.ofReal κ⁻¹ * (NormalPhoton.radiationForm normal F).expectation (R.rankOne u) := by
  rw [NormalPhoton.numberForm_rankOne, NormalPhoton.radiationForm_rankOne]
  exact number_le_inv_mul_radiation hκ u hu

theorem hardPhotonVacuumEmbedding_normal_softEnergy
    (BF : StandardSymmetricFockExponential) (κ : ℝ)
    (u : generatedFockSubspace (hardOnePhoton κ)) :
    (NormalPhoton.softEnergyForm normal F κ).expectation
      (R.rankOne (hardPhotonVacuumEmbedding BF κ u)) = 0 := by
  rw [NormalPhoton.softEnergyForm, secondQuantizedPositiveForm_rankOne]
  exact hardPhotonVacuumEmbedding_softEnergy BF κ u

theorem hardPhotonVacuumEmbedding_normal_number_le
    (BF : StandardSymmetricFockExponential) {κ : ℝ} (hκ : 0 < κ)
    (u : generatedFockSubspace (hardOnePhoton κ)) :
    (NormalPhoton.numberForm normal F).expectation
        (R.rankOne (hardPhotonVacuumEmbedding BF κ u)) ≤
      ENNReal.ofReal κ⁻¹ * (NormalPhoton.radiationForm normal F).expectation
        (R.rankOne (hardPhotonVacuumEmbedding BF κ u)) := by
  rw [NormalPhoton.numberForm_rankOne, NormalPhoton.radiationForm_rankOne]
  exact hardPhotonVacuumEmbedding_number_le BF hκ u

end NormalForms

end GptLean.PhysicalFock
