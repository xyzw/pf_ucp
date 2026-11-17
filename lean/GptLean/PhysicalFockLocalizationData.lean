import GptLean.PhysicalFockFullNumberLaw
import GptLean.PhysicalFockCutoffComposition
import GptLean.PhysicalFockChannelMoments

/-!
The localization data on the actual fermionic electronic/photon normal
state space. Composition is proved from the matched exponential map and
the actual multiplier identities. The joint number law and gentle bound
are constructed on that same channel, including its electronic factor.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationKernelCutoffs PhotonLocalizationFockChannel
open PhysicalNormalTrace PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true

variable {P E : Type} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [MeasurableSpace P] [BorelSpace P] {μ : Measure P}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E]
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (BT : StandardNormalTraceBackground)
  (e : Lp E 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 photonMeasure) (N : ℕ)

omit [CompleteSpace E] [IsScalarTower ℝ ℂ E] in
private theorem transport_discarded (r : ℝ) (u : Lp ℂ 2 photonMeasure) :
    discardedMap photonMeasure (transportSplit e (complexOnePhotonIsometry r)) u =
      e (CutoffComposition.discardMap r (e.symm u)) := rfl

omit [CompleteSpace E] [IsScalarTower ℝ ℂ E] in
theorem fullChannel_cutoff_comp {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : 2 * r ≤ s)
    {x : BT.FullTrace N} (hx : x ∈ (BT.realization (FullHilbert N)).rank.positive) :
    fullChannel BF BT e N (complexOnePhotonIsometry r)
      (fullChannel BF BT e N (complexOnePhotonIsometry s) x) =
        fullChannel BF BT e N (complexOnePhotonIsometry r) x := by
  apply ElectronicComposition.channel_comp BF BT
    (transportSplit e (complexOnePhotonIsometry r))
    (transportSplit e (complexOnePhotonIsometry s)) _ _ _ hx
  · intro f
    simp only [transportSplit_retained, e.symm_apply_apply]
    exact congrArg e (CutoffComposition.three_components hr hs hrs (e.symm f)).1
  · intro f
    simp only [transport_discarded, transportSplit_retained, e.symm_apply_apply]
    exact congrArg e (CutoffComposition.three_components hr hs hrs (e.symm f)).2.1
  · intro f
    simp only [transport_discarded, e.symm_apply_apply]
    exact congrArg e (CutoffComposition.three_components hr hs hrs (e.symm f)).2.2

private theorem radius_separated {m l : ℕ} (hml : m < l) : 2 * radius m ≤ radius l := by
  unfold radius
  calc
    2 * (3 : ℝ) ^ (m + 1) ≤ 3 * (3 : ℝ) ^ (m + 1) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = (3 : ℝ) ^ (m + 2) := by
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
      ring
    _ ≤ (3 : ℝ) ^ (l + 1) := pow_le_pow_right₀ (by norm_num) (by omega)

def localizationData : PhotonLoss.LocalizationData (BT.FullTrace N) where
  states := BT.fermionicStates N
  states_closed := BT.fermionicStates_closed N
  localize m := fullChannel BF BT e N (complexOnePhotonIsometry (radius m))
  localize_cont m := (fullChannel BF BT e N (complexOnePhotonIsometry (radius m))).continuous
  localize_state _m _ hx := fullChannel_fermionic BF BT e N _ hx
  localize_comp m l hml _ hx := fullChannel_cutoff_comp BF BT e N
    (radius_pos m) (radius_pos l) (radius_separated hml) hx.1
  tail M x := FullNumberLaw.tail (volume : Measure (SymmetricLift.Configuration N)) BT M x
  tail_cont M := (FullNumberLaw.tail (volume : Measure (SymmetricLift.Configuration N)) BT M).continuous
  weight x := FullNumberLaw.weight (volume : Measure (SymmetricLift.Configuration N)) BT x
  number_law m _ hx := ⟨FullNumberLaw.numberLaw
    (volume : Measure (SymmetricLift.Configuration N)) BF BT
    (transportSplit e (complexOnePhotonIsometry (radius m)))
    (photonVacuum_positive BF C e (radius m)) hx.1 hx.2.1⟩

@[simp] theorem localizationData_states :
    (localizationData BF C BT e N).states = BT.fermionicStates N := rfl

@[simp] theorem localizationData_localize (m : ℕ) (x : BT.FullTrace N) :
    (localizationData BF C BT e N).localize m x =
      fullChannel BF BT e N (complexOnePhotonIsometry (radius m)) x := rfl

theorem states_positive {x : BT.FullTrace N}
    (hx : x ∈ (localizationData BF C BT e N).states) :
    x ∈ (BT.realization (FullHilbert N)).rank.positive := hx.1

theorem trace_one {x : BT.FullTrace N}
    (hx : x ∈ (localizationData BF C BT e N).states) :
    (BT.realization (FullHilbert N)).rank.trace x = 1 := hx.2.1

theorem number_decrease (m : ℕ) (x : BT.FullTrace N)
    (hx : x ∈ (localizationData BF C BT e N).states) :
    (fullNumberForm BT N).expectation ((localizationData BF C BT e N).localize m x) ≤
      (fullNumberForm BT N).expectation x :=
  ChannelMoments.number_decrease (volume : Measure (SymmetricLift.Configuration N)) BF BT
    (transportSplit e (complexOnePhotonIsometry (radius m))) (states_positive BF C BT e N hx)

theorem tail_markov (M : ℕ) (x : BT.FullTrace N)
    (hx : x ∈ (localizationData BF C BT e N).states)
    (hfinite : (fullNumberForm BT N).expectation x < ⊤) :
    (localizationData BF C BT e N).tail M x ≤
      ((fullNumberForm BT N).expectation x).toReal / ((M : ℝ) + 1) :=
  ChannelMoments.tail_markov (volume : Measure (SymmetricLift.Configuration N)) BT M
    (states_positive BF C BT e N hx) hfinite

end GptLean.PhysicalFock
