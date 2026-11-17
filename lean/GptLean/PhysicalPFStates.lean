import GptLean.PhysicalPFPair
import GptLean.PhysicalElectronicFermions

/-!
The density-current map and pure/mixed constrained-search models on the
actual spatial photon Fock space. The spectral choice is made only after
proving that every reference source gives the same physical pair.
-/

noncomputable section

namespace GptLean.PhysicalPFStates

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalPFSource PhysicalNormalStates
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

abbrev Index (N : ℕ) := Fin N × Fin 3

variable {N : ℕ} (i : Fin N) (V : Position (Index N) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : Index N → Position (Index N) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ x ∂volume, ‖κ q x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

abbrev energy := normalEnergy (Index N) V C κ hκ M hbound B S e

def source (x : B.Trace (WaveSpace (Index N)))
    (hx : x ∈ (B.realization (WaveSpace (Index N))).rank.positive)
    (he : (energy V C κ hκ M hbound B S e).expectation x < ⊤) : Source (Index N) V B x :=
  Classical.choice (source_exists (Index N) V C κ hκ M hbound B S e hx he)

def pair (x : B.Trace (WaveSpace (Index N)))
    (hx : x ∈ (B.realization (WaveSpace (Index N))).rank.positive)
    (he : (energy V C κ hκ M hbound B S e).expectation x < ⊤) : PhysicalPairSpace.Pair :=
  (source V C κ hκ M hbound B S e x hx he).pair C M S e i V κ hκ hbound he

theorem pair_eq_source (x : B.Trace (WaveSpace (Index N)))
    (hx : x ∈ (B.realization (WaveSpace (Index N))).rank.positive)
    (he : (energy V C κ hκ M hbound B S e).expectation x < ⊤)
    (s : Source (Index N) V B x) :
    pair i V C κ hκ M hbound B S e x hx he = s.pair C M S e i V κ hκ hbound he :=
  (source V C κ hκ M hbound B S e x hx he).pair_independent
    C M S e i V κ hκ hbound s he

def statePair (x : (energy V C κ hκ M hbound B S e).State) : PhysicalPairSpace.Pair :=
  pair i V C κ hκ M hbound B S e x.val x.property.1 x.property.2.2

theorem statePair_mass (x : (energy V C κ hκ M hbound B S e).State) :
    (∫ z, PhysicalPairSpace.densityL1 (statePair i V C κ hκ M hbound B S e x) z) = N := by
  have h := (source V C κ hκ M hbound B S e x.val x.property.1 x.property.2.2).pair_mass
    C M S e i V κ hκ hbound x.property.2.2
  exact h.trans ((congrArg (fun r : ℝ => (N : ℝ) * r) x.property.2.1).trans (mul_one _))

abbrev PureState := Pure (energy V C κ hκ M hbound B S e)
  (PhysicalElectronicFermions.projection N PhotonFock)

abbrev MixedState := Mixed (energy V C κ hκ M hbound B S e)
  B.conjugation (PhysicalElectronicFermions.projection N PhotonFock)

def mixedPair (x : MixedState V C κ hκ M hbound B S e) : PhysicalPairSpace.Pair :=
  statePair i V C κ hκ M hbound B S e x.val

def mixedModel : DFT.StateModel (MixedState V C κ hκ M hbound B S e) PhysicalPairSpace.Pair :=
  PhysicalNormalStates.mixedModel (energy V C κ hκ M hbound B S e) B.conjugation
    (PhysicalElectronicFermions.projection N PhotonFock) (mixedPair i V C κ hκ M hbound B S e)

def pureModel : DFT.StateModel (PureState V C κ hκ M hbound B S e) PhysicalPairSpace.Pair :=
  PhysicalNormalStates.pureModel (energy V C κ hκ M hbound B S e) B.conjugation
    (PhysicalElectronicFermions.projection N PhotonFock) (mixedPair i V C κ hκ M hbound B S e)

def pureEmbedding : DFT.PureEmbedding (pureModel i V C κ hκ M hbound B S e)
    (mixedModel i V C κ hκ M hbound B S e) :=
  PhysicalNormalStates.pureEmbedding (energy V C κ hκ M hbound B S e) B.conjugation
    (PhysicalElectronicFermions.projection N PhotonFock) (mixedPair i V C κ hκ M hbound B S e)

end GptLean.PhysicalPFStates
