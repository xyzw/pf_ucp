import GptLean.PhysicalFockRadiationGraph
import GptLean.PhotonLocalizationLocalFormsOperators

/-!
A concrete dense core for the radiation graph.

The reference Banach space is the closed graph of the actual square-root
momentum multiplier. Its two continuous coordinate maps are the physical
vector and its radiation derivative. Finite photon-number vectors form
a dense subspace in this graph Banach space. Both coordinates are
approximated by the same canonical number cutoff.
-/

noncomputable section

namespace GptLean.PhysicalFock

open Filter Topology

def finiteNumberSubspace : Submodule ℂ PhotonFock where
  carrier := {u | ∃ M : ℕ, ∀ n, M < n → u n = 0}
  zero_mem' := ⟨0, fun _ _ => rfl⟩
  add_mem' := by
    rintro u v ⟨M, hM⟩ ⟨L, hL⟩
    refine ⟨max M L, fun n hn => ?_⟩
    change u n + v n = 0
    rw [hM n ((le_max_left _ _).trans_lt hn), hL n ((le_max_right _ _).trans_lt hn), zero_add]
  smul_mem' := by
    rintro c u ⟨M, hM⟩
    exact ⟨M, fun n hn => by change c • u n = 0; rw [hM n hn, smul_zero]⟩

theorem cutoff_coordinate_zero (M n : ℕ) (hMn : M < n) (u : PhotonFock) :
    cutoff (Sector photonMeasure) M u n = 0 := by
  simp only [cutoff, sum_apply, lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  apply sector_coordinate_ne
  have hjM : j < M + 1 := Finset.mem_range.mp hj
  omega

theorem cutoff_finiteNumber (M : ℕ) (u : PhotonFock) :
    cutoff (Sector photonMeasure) M u ∈ finiteNumberSubspace :=
  ⟨M, fun n hn => cutoff_coordinate_zero M n hn u⟩

theorem cutoff_radiation_graph (M : ℕ) (u v : PhotonFock)
    (h : (u, v) ∈ radiationRoot.graph) :
    (cutoff (Sector photonMeasure) M u, cutoff (Sector photonMeasure) M v) ∈
      radiationRoot.graph :=
  PhotonLocalization.numberSectorCutoff_graph (photonSector photonMeasure)
    radiationRoot_sector_graph_of_mem M u v h

abbrev RadiationGraphSpace := ↥radiationRoot.graph

instance radiationGraphCompleteSpace : CompleteSpace RadiationGraphSpace :=
  radiationRoot_closed.isComplete.completeSpace_coe

def radiationGraphInclusion : RadiationGraphSpace →L[ℂ] PhotonFock :=
  (ContinuousLinearMap.fst ℂ PhotonFock PhotonFock).comp radiationRoot.graph.subtypeL

def radiationGraphDerivative : RadiationGraphSpace →L[ℂ] PhotonFock :=
  (ContinuousLinearMap.snd ℂ PhotonFock PhotonFock).comp radiationRoot.graph.subtypeL

theorem radiationGraph_pair (q : RadiationGraphSpace) :
    (radiationGraphInclusion q, radiationGraphDerivative q) ∈ radiationRoot.graph := q.property

def radiationGraphCore : Submodule ℂ RadiationGraphSpace :=
  finiteNumberSubspace.comap radiationGraphInclusion.toLinearMap

def radiationGraphApprox (M : ℕ) (q : RadiationGraphSpace) : RadiationGraphSpace :=
  ⟨(cutoff (Sector photonMeasure) M q.val.1, cutoff (Sector photonMeasure) M q.val.2),
    cutoff_radiation_graph M q.val.1 q.val.2 q.property⟩

theorem radiationGraphApprox_mem (M : ℕ) (q : RadiationGraphSpace) :
    radiationGraphApprox M q ∈ radiationGraphCore := cutoff_finiteNumber M q.val.1

theorem radiationGraphApprox_tendsto (q : RadiationGraphSpace) :
    Tendsto (fun M => radiationGraphApprox M q) atTop (𝓝 q) := by
  apply tendsto_subtype_rng.mpr
  exact (cutoff_tendsto (Sector photonMeasure) q.val.1).prodMk_nhds
    (cutoff_tendsto (Sector photonMeasure) q.val.2)

/-- Density is in the actual graph norm, so both coordinates converge. -/
theorem radiationGraphCore_dense : Dense (radiationGraphCore : Set RadiationGraphSpace) := by
  intro q
  exact mem_closure_of_tendsto (radiationGraphApprox_tendsto q)
    (Eventually.of_forall fun M => radiationGraphApprox_mem M q)

def radiationFiniteCore : Submodule ℂ PhotonFock := finiteNumberSubspace ⊓ radiationRoot.domain

/-- The same finite-sector subspace is an operator core in Mathlib's sense. -/
theorem radiationRoot_hasCore : radiationRoot.HasCore radiationFiniteCore := by
  refine ⟨inf_le_right, ?_⟩
  have hc : (radiationRoot.domRestrict radiationFiniteCore).IsClosable :=
    radiationRoot_closed.isClosable.leIsClosable LinearPMap.domRestrict_le
  apply LinearPMap.eq_of_eq_graph
  rw [← hc.graph_closure_eq_closure_graph]
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _
      (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le) radiationRoot_closed
  · intro z hz
    let q : RadiationGraphSpace := ⟨z, hz⟩
    apply mem_closure_of_tendsto
      ((continuous_subtype_val.tendsto q).comp (radiationGraphApprox_tendsto q))
    apply Eventually.of_forall
    intro M
    have hpair := (radiationGraphApprox M q).property
    obtain ⟨w, hw, hdw⟩ := radiationRoot.mem_graph_iff.mp hpair
    apply (radiationRoot.domRestrict radiationFiniteCore).mem_graph_iff.mpr
    have hwcore : w.val ∈ radiationFiniteCore :=
      ⟨hw.symm ▸ cutoff_finiteNumber M z.1, w.property⟩
    refine ⟨⟨w.val, hwcore, w.property⟩, hw, ?_⟩
    exact (LinearPMap.domRestrict_apply rfl).trans hdw

end GptLean.PhysicalFock
