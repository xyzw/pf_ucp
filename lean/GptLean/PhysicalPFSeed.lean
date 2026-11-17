import GptLean.PhysicalFermionicSeed
import GptLean.PhysicalPFForm
import GptLean.PhysicalNormalSpectral
import GptLean.PhysicalPhotonMarginalMoments

/-!
A normalized finite-energy fermionic pure state and its normal rank-one
state, constructed from the compact electronic alternant and the actual
photon vacuum. No initial-state nonemptiness is an input.
-/

noncomputable section

namespace GptLean.PhysicalPFSeed

open MeasureTheory PhysicalFock PhysicalNormalTrace PhysicalClosedForms
  PhotonLocalizationChannel PhysicalPhotonMarginal
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true

abbrev Index (N : ℕ) := Fin N × Fin 3

variable (N : ℕ) (c : ℝ) (hc : 0 ≤ c)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : Index N → EuclideanSpace ℝ (Index N) → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

abbrev energy := PhysicalPFReference.normalEnergy (Index N)
  (fun x => c * PhysicalCoulombH1.potential N x) C κ hκ M hbound B S e

include hc in
theorem wave_energy_finite :
    (energy N c C κ hκ M hbound B S e).expectation
      ((B.realization (PhysicalPFReference.WaveSpace (Index N))).rank.rankOne
        (PhysicalFermionicSeed.wave N)) < ⊤ := by
  have hrep := congrArg
    (fun w : PhysicalPFReference.WaveSpace (Index N) =>
      (energy N c C κ hκ M hbound B S e).expectation
        ((B.realization (PhysicalPFReference.WaveSpace (Index N))).rank.rankOne w))
    (PhysicalFermionicSeed.reference_value N c hc)
  exact (hrep.symm.trans (PhysicalPFReference.normalEnergy_rankOne (Index N)
    (fun x => c * PhysicalCoulombH1.potential N x) C κ hκ M hbound B S e
      (PhysicalFermionicSeed.reference N c hc))).trans_lt ENNReal.ofReal_lt_top

def pure : PhysicalNormalStates.Pure (energy N c C κ hκ M hbound B S e)
    (PhysicalElectronicFermions.projection N PhotonFock) :=
  PhysicalNormalSpectral.normalize (energy N c C κ hκ M hbound B S e)
    (PhysicalElectronicFermions.projection N PhotonFock) (PhysicalFermionicSeed.wave N)
    (PhysicalFermionicSeed.wave_projection N)
    (wave_energy_finite N c hc C κ hκ M hbound B S e)
    (PhysicalFermionicSeed.wave_ne_zero N)

def mixed : PhysicalNormalStates.Mixed (energy N c C κ hκ M hbound B S e)
    B.conjugation (PhysicalElectronicFermions.projection N PhotonFock) :=
  PhysicalNormalStates.pureToMixed (energy N c C κ hκ M hbound B S e) B.conjugation
    (PhysicalElectronicFermions.projection N PhotonFock) (pure N c hc C κ hκ M hbound B S e)

theorem wave_number_zero :
    (fullForm B (volume : Measure (SymmetricLift.Configuration N))
      (NormalPhoton.numberForm B.normal (B.realization PhotonFock).functional)).expectation
      ((B.realization (PhysicalPFReference.WaveSpace (Index N))).rank.rankOne
        (PhysicalFermionicSeed.wave N)) = 0 := by
  refine (fullNumberForm_rankOne B (volume : Measure (SymmetricLift.Configuration N))
    (PhysicalFermionicSeed.wave N)).trans ?_
  have he : (fun x => photonNumberForm photonMeasure (PhysicalFermionicSeed.wave N x)) =ᵐ[volume]
      (fun _ => (0 : ℝ≥0∞)) := by
    filter_upwards [PhysicalFermionicSeed.wave_ae N] with x hx
    rw [hx, PhysicalFermionicSeed.scalar_vacuum_number]
  rw [lintegral_congr_ae he, lintegral_zero]

theorem pure_number_zero :
    (fullForm B (volume : Measure (SymmetricLift.Configuration N))
      (NormalPhoton.numberForm B.normal (B.realization PhotonFock).functional)).expectation
      ((B.realization (PhysicalPFReference.WaveSpace (Index N))).rank.rankOne
        (pure N c hc C κ hκ M hbound B S e).val) = 0 := by
  change (fullForm B (volume : Measure (SymmetricLift.Configuration N))
      (NormalPhoton.numberForm B.normal (B.realization PhotonFock).functional)).expectation
    ((B.realization (PhysicalPFReference.WaveSpace (Index N))).rank.rankOne
      (((‖PhysicalFermionicSeed.wave N‖⁻¹ : ℝ) : ℂ) • PhysicalFermionicSeed.wave N)) = 0
  rw [rankOne_real_smul (B.realization (PhysicalPFReference.WaveSpace (Index N))).functional,
    PhysicalNormalStates.expectation_smul _ (sq_nonneg _), wave_number_zero, mul_zero]

theorem mixed_number_zero :
    (NormalPhoton.numberForm B.normal (B.realization PhotonFock).functional).expectation
      (marginal B (volume : Measure (SymmetricLift.Configuration N))
        (mixed N c hc C κ hκ M hbound B S e).val.val) = 0 :=
  pure_number_zero N c hc C κ hκ M hbound B S e

end GptLean.PhysicalPFSeed
