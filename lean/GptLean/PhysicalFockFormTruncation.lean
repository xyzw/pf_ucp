import GptLean.PhysicalFockFormCalculus
import GptLean.PhotonLocalizationRadiationTruncation

/-!
Finite ranks of one fixed countable physical form family.
These are the actual prefixes used by the sharp radiation estimate.
Their supremum recovers the normal form expectation, including infinity.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationChannel PhysicalNormalTrace RemovalState
  PhotonLocalizationFormBounds
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false

def finiteFamily (q : OnePhotonFormFamily) (k n : ℕ) : Lp ℂ 2 photonMeasure :=
  if n < k then q n else 0

theorem finiteFamily_value (q : OnePhotonFormFamily) (k : ℕ) (u : Lp ℂ 2 photonMeasure) :
    onePhotonFamilyValue (finiteFamily q k) u =
      radiationPartial (fun i v => ⟪q i, v⟫_ℂ) k u := by
  unfold onePhotonFamilyValue radiationPartial
  rw [tsum_eq_sum (s := Finset.range k)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [finiteFamily, ite_eq_left (Finset.mem_range.mp hi)]
  · intro i hi
    rw [finiteFamily, ite_eq_right (fun h => hi (Finset.mem_range.mpr h)), inner_zero_left,
      norm_zero, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero]

theorem finiteFamily_value_fin (q : OnePhotonFormFamily) (k : ℕ) (u : Lp ℂ 2 photonMeasure) :
    onePhotonFamilyValue (finiteFamily q k) u =
      ENNReal.ofReal (∑ i : Fin k, ‖⟪q i, u⟫_ℂ‖ ^ 2) := by
  rw [finiteFamily_value, radiationPartial,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  exact (Fin.sum_univ_eq_sum_range (fun i => ENNReal.ofReal (‖⟪q i, u⟫_ℂ‖ ^ 2)) k).symm

section Normal
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData PhotonFock T} (normal : NormalTraceData R) (F : NormalFunctionalData R)

theorem familyObservable_eq_iSup (BF : StandardSymmetricFockExponential)
    (CCR : CanonicalSectorCCR photonMeasure) (q : OnePhotonFormFamily)
    {x : T} (hx : x ∈ R.positive) :
    (familyObservable normal F q).expectation x =
      ⨆ k, (familyObservable normal F (finiteFamily q k)).expectation x :=
  (photonFormCalculus normal F BF CCR).radiation_eq_iSup normal (fun _ hx => hx)
    q (finiteFamily q) (fun i v => ⟪q i, v⟫_ℂ) (fun _ => rfl)
    (finiteFamily_value q) hx

end Normal
end GptLean.PhysicalFock
