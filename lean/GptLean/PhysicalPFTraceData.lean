import GptLean.PhysicalFockLocalizationData
import GptLean.PhysicalPFEnergyTruncation
import GptLean.PhysicalPFElectronicCutoff
import GptLean.PhysicalPFSmoothTests

/-!
The physical trace-limit data use the constructed fermionic channel,
actual number form, actual PF energy truncations, and tested density and
current traces. The ambient energy is the truncation supremum, with its
physical energy identification proved on the positive cone.
-/

noncomputable section
namespace GptLean.PhysicalPFLocalization

open MeasureTheory Filter Topology PhysicalFock PhysicalPFReference PhysicalPFSource
  PhysicalPFStates PhysicalPairSpace PhysicalNormalTrace PhysicalClosedForms PhotonLocalization
  PhotonLocalizationCurrent
open PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
set_option Elab.async false

variable {N : ℕ} (i : Fin N) (BF : StandardSymmetricFockExponential)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground)
  (κ : (Fin N × Fin 3) → PhysicalPFReference.Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ x ∂volume, ‖κ q x‖ ≤ M) (e : ℝ)

def traceData : PhotonLoss.TraceData
    (localizationData BF C B PhysicalOnePhotonFourier.fourier N) SmoothPairTest where
  energy := PhysicalPFEnergyTruncation.ambientEnergy N B S BF C κ hκ M hbound e
  number := (fullNumberForm B N).expectation
  energy_lsc := PhysicalPFEnergyTruncation.ambientEnergy_lsc N B S BF C κ hκ M hbound e
  number_lsc := expectation_lowerSemicontinuous (fullNumberForm B N)
  number_decrease := number_decrease BF C B PhysicalOnePhotonFourier.fourier N
  tail_markov := tail_markov BF C B PhysicalOnePhotonFourier.fourier N
  cutoff l := B.push
    ((PhysicalElectronicScalars.branch N l (PhysicalElectronicScalars.selected N)).multiplier
      (H := PhotonFock))
  cutoff_cont l := (B.push
    ((PhysicalElectronicScalars.branch N l (PhysicalElectronicScalars.selected N)).multiplier
      (H := PhotonFock))).continuous
  cutoff_tendsto x hx := PhysicalNormalCompression.push_tendsto (H := FullHilbert N) B
    (fun l => (PhysicalElectronicScalars.branch N l (PhysicalElectronicScalars.selected N)).multiplier
      (H := PhotonFock))
    (fun l v => PhysicalElectronicScalars.multiplier_contraction N (H := PhotonFock) l
      (PhysicalElectronicScalars.selected N) v)
    (PhysicalElectronicScalars.selected_strong N (H := PhotonFock))
    (show x ∈ (B.realization (FullHilbert N)).rank.positive from hx.1)
  truncatedEnergy := PhysicalPFEnergyTruncation.truncatedEnergy N B S BF C κ hκ M hbound e
  truncated_lsc := PhysicalPFEnergyTruncation.truncatedEnergy_lsc N B S BF C κ hκ M hbound e
  energy_eq_iSup := PhysicalPFEnergyTruncation.ambientEnergy_eq_iSup N B S BF C κ hκ M hbound e
  test := normalTest i (PhysicalCovariantKinetic.potential N) C κ hκ M hbound B S e
  test_passage u x E hu hE hlim t := by
    apply normalTest_passage i (PhysicalCovariantKinetic.potential N) C κ hκ M hbound B S e t u x
      (fun n => (hu n).1) hlim E 1
    · intro n
      exact (PhysicalPFEnergyTruncation.ambientEnergy_eq_physical N B S BF C κ hκ M hbound e
        (hu n).1).symm.le.trans (hE n)
    · intro n
      exact le_of_eq (hu n).2.1

theorem traceData_energy_match {x : B.Trace (FullHilbert N)}
    (hx : x ∈ (B.realization (FullHilbert N)).rank.positive) :
    (traceData i BF C B S κ hκ M hbound e).energy x =
      (normalEnergy (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
        C κ hκ M hbound B S e).expectation x :=
  PhysicalPFEnergyTruncation.ambientEnergy_eq_physical N B S BF C κ hκ M hbound e hx

end GptLean.PhysicalPFLocalization
