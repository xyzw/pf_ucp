import GptLean.PhysicalFockSectors
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
Separability of the concrete photon Fock model.

Finite-coordinate insertions have separable ranges. Their countable union
is dense by the already proved number-cutoff convergence. Each physical
symmetric L² sector is separable for the actual momentum/polarization
measure, so the full photon Fock space is separable as well.
-/

noncomputable section

namespace GptLean.PhysicalFock

open Filter Topology TopologicalSpace MeasureTheory
open scoped ENNReal

section DirectSum

variable (K : ℕ → Type*) [∀ n, NormedAddCommGroup (K n)]
  [∀ n, InnerProductSpace ℂ (K n)]

def finiteInsertion (M : ℕ) : ((i : Fin (M + 1)) → K i.val) →L[ℂ] Space K :=
  ∑ i : Fin (M + 1), (lp.singleContinuousLinearMap ℂ K 2 i.val).comp (ContinuousLinearMap.proj i)

theorem finiteInsertion_coordinates (M : ℕ) (u : Space K) :
    finiteInsertion K M (fun i => u i.val) = cutoff K M u := by
  simp only [finiteInsertion, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, cutoff, sector_apply]
  exact Fin.sum_univ_eq_sum_range (fun n => lp.single 2 n (u n)) (M + 1)

instance spaceSeparableSpace [∀ n, SeparableSpace (K n)] : SeparableSpace (Space K) := by
  let s : Set (Space K) := ⋃ M : ℕ, Set.range (finiteInsertion K M)
  have hs : IsSeparable s :=
    IsSeparable.iUnion fun M => isSeparable_range (finiteInsertion K M).continuous
  have hd : Dense s := by
    intro u
    apply mem_closure_of_tendsto (cutoff_tendsto K u)
    apply Eventually.of_forall
    intro M
    apply Set.mem_iUnion.mpr
    refine ⟨M, ?_⟩
    exact ⟨fun i => u i.val, finiteInsertion_coordinates K M u⟩
  apply isSeparable_univ_iff.mp
  rw [← hd.closure_eq]
  exact hs.closure

end DirectSum

/-- All separability hypotheses are supplied by the actual measures and sectors. -/
instance photonFockSeparableSpace : SeparableSpace PhotonFock := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : MeasurableSpace.CountablyGenerated PhotonMode := inferInstance
  have (n : ℕ) : MeasurableSpace.CountablyGenerated (Fin n → PhotonMode) := inferInstance
  have (n : ℕ) : IsSeparable (SectorMeasure photonMeasure n) := inferInstance
  have (n : ℕ) : SecondCountableTopology (FullSector photonMeasure n) := inferInstance
  have (n : ℕ) : SecondCountableTopology (Sector photonMeasure n) := inferInstance
  have (n : ℕ) : SeparableSpace (Sector photonMeasure n) := inferInstance
  exact spaceSeparableSpace (Sector photonMeasure)

theorem photonFock_separable : SeparableSpace PhotonFock := inferInstance

end GptLean.PhysicalFock
