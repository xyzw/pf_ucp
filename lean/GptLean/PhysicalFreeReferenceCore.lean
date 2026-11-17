import GptLean.PhysicalFockRadiationCutoff
import GptLean.ElectronicH1Map
import GptLean.ElectronicH1Reindex

/-!
The common electronic H1 and spatial radiation domain has a concrete
dense core. Bounded energy cutoffs first give radiation-graph-valued H1
functions. Smooth compact approximation in that stronger H1 space then
converges in both of the original graph norms.
-/

noncomputable section

namespace GptLean.PhysicalFreeReferenceCore

open MeasureTheory Filter Topology PhysicalFock ElectronicH1Complex
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

variable (I : Type*) [Fintype I] [DecidableEq I]

abbrev RadiationSource := Lp RadiationGraphSpace 2 (volume : Measure (EuclideanSpace ℝ I))
abbrev Ambient := ComplexH1 PhotonFock I × RadiationSource I

def matching : Ambient I →L[ℂ] ElectronicH1Space.L2 PhotonFock I :=
  value.comp (ContinuousLinearMap.fst ℂ _ _) -
    (radiationGraphInclusion.compLpL 2 volume).comp (ContinuousLinearMap.snd ℂ _ _)

def freeSubspace : Submodule ℂ (Ambient I) := (matching I).ker
abbrev FreeReference := ↥(freeSubspace I)

instance freeReferenceCompleteSpace : CompleteSpace (FreeReference I) :=
  (matching I).isClosed_ker.completeSpace_coe

def electronic : FreeReference I →L[ℂ] ComplexH1 PhotonFock I :=
  (ContinuousLinearMap.fst ℂ _ _).comp (freeSubspace I).subtypeL

def radiationSource : FreeReference I →L[ℂ] RadiationSource I :=
  (ContinuousLinearMap.snd ℂ _ _).comp (freeSubspace I).subtypeL

def inclusion : FreeReference I →L[ℂ] ElectronicH1Space.L2 PhotonFock I :=
  value.comp (electronic I)

theorem value_matching (q : FreeReference I) :
    value (electronic I q) = radiationGraphInclusion.compLpL 2 volume (radiationSource I q) := by
  have h := q.property
  change value (electronic I q) -
    radiationGraphInclusion.compLpL 2 volume (radiationSource I q) = 0 at h
  exact sub_eq_zero.mp h

/-- A graph-valued H1 function provides both matched reference coordinates. -/
def fromGraphH1 : ComplexH1 RadiationGraphSpace I →L[ℂ] FreeReference I :=
  ((ElectronicH1Map.map radiationGraphInclusion).prod value).codRestrict (freeSubspace I)
    (by intro u; change value (ElectronicH1Map.map radiationGraphInclusion u) -
          radiationGraphInclusion.compLpL 2 volume (value u) = 0
        exact sub_self _)

@[simp] theorem electronic_fromGraphH1 (u : ComplexH1 RadiationGraphSpace I) :
    electronic I (fromGraphH1 I u) = ElectronicH1Map.map radiationGraphInclusion u := rfl

@[simp] theorem radiationSource_fromGraphH1 (u : ComplexH1 RadiationGraphSpace I) :
    radiationSource I (fromGraphH1 I u) = value u := rfl

def energyApprox (q : FreeReference I) (M : ℕ) : FreeReference I :=
  fromGraphH1 I (ElectronicH1Map.map (radiationEnergyCutoff M) (electronic I q))

set_option backward.isDefEq.respectTransparency.types true in
theorem electronic_energyApprox (q : FreeReference I) (M : ℕ) :
    electronic I (energyApprox I q M) = ElectronicH1Map.map (energyCutoff M) (electronic I q) := by
  change ElectronicH1Map.map radiationGraphInclusion
    (ElectronicH1Map.map (radiationEnergyCutoff M) (electronic I q)) = _
  have h : radiationGraphInclusion.comp (radiationEnergyCutoff M) = energyCutoff M := by
    ext u
    rfl
  exact (ElectronicH1Map.map_comp (I := I) (E := PhotonFock)
    (F := RadiationGraphSpace) (G := PhotonFock) radiationGraphInclusion
    (radiationEnergyCutoff M) (electronic I q)).trans
      (congrArg (fun L : PhotonFock →L[ℂ] PhotonFock =>
        ElectronicH1Map.map (I := I) L (electronic I q)) h)

set_option backward.isDefEq.respectTransparency.types true in
theorem radiationSource_energyApprox (q : FreeReference I) (M : ℕ) :
    radiationSource I (energyApprox I q M) =
      (radiationGraphCutoff M).compLpL 2 volume (radiationSource I q) := by
  change (radiationEnergyCutoff M).compLpL 2 volume (value (electronic I q)) = _
  exact (congrArg (fun w : ElectronicH1Space.L2 PhotonFock I =>
      (radiationEnergyCutoff M).compLpL 2 volume w) (value_matching I q)).trans
    (ElectronicH1Map.compLpL_comp (E := RadiationGraphSpace) (F := PhotonFock)
      (G := RadiationGraphSpace) (radiationEnergyCutoff M)
      radiationGraphInclusion (radiationSource I q))

theorem energyApprox_tendsto (q : FreeReference I) :
    Tendsto (energyApprox I q) atTop (𝓝 q) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun M =>
    (electronic I (energyApprox I q M), radiationSource I (energyApprox I q M)))
      atTop (𝓝 (electronic I q, radiationSource I q))
  simp only [electronic_energyApprox, radiationSource_energyApprox]
  exact (ElectronicH1Map.map_tendsto energyCutoff energyCutoff_norm_le
    energyCutoff_tendsto (electronic I q)).prodMk_nhds
      (ElectronicH1Map.compLpL_tendsto radiationGraphCutoff radiationGraphCutoff_norm_le
        radiationGraphCutoff_tendsto (radiationSource I q))

theorem fromGraphH1_denseRange : DenseRange (fromGraphH1 I) := by
  intro q
  apply mem_closure_of_tendsto (energyApprox_tendsto I q)
  exact Eventually.of_forall fun M => ⟨_, rfl⟩

omit [DecidableEq I] in
theorem spatialRadiationInclusion_denseRange :
    DenseRange (radiationGraphInclusion.compLpL 2
      (volume : Measure (EuclideanSpace ℝ I))) := by
  intro u
  apply mem_closure_of_tendsto
    (ElectronicH1Map.compLpL_tendsto energyCutoff energyCutoff_norm_le energyCutoff_tendsto u)
  apply Eventually.of_forall
  intro M
  refine ⟨(radiationEnergyCutoff M).compLpL 2 volume u, ?_⟩
  have h : radiationGraphInclusion.comp (radiationEnergyCutoff M) = energyCutoff M := by
    ext v
    rfl
  simpa only [h] using ElectronicH1Map.compLpL_comp radiationGraphInclusion
    (radiationEnergyCutoff M) u

/-- The common graph is a dense form domain in the actual spatial Fock L2 space. -/
theorem inclusion_denseRange : DenseRange (inclusion I) := by
  have h := (spatialRadiationInclusion_denseRange I).comp
    (ElectronicH1Map.value_denseRange (E := RadiationGraphSpace) (I := I))
    (radiationGraphInclusion.compLpL 2
      (volume : Measure (EuclideanSpace ℝ I))).continuous
  apply h.mono
  rintro u ⟨v, rfl⟩
  exact ⟨fromGraphH1 I v, rfl⟩

def smoothCore : Set (FreeReference I) :=
  (fromGraphH1 I) '' ((realEquiv (E := RadiationGraphSpace) (I := I)) ⁻¹'
    ElectronicH1Reindex.genericSmoothCore RadiationGraphSpace I)

theorem dense_smoothCore : Dense (smoothCore I) := by
  have hd : Dense ((realEquiv (E := RadiationGraphSpace) (I := I)) ⁻¹'
      ElectronicH1Reindex.genericSmoothCore RadiationGraphSpace I) :=
    dense_preimage_realEquiv ElectronicH1Reindex.dense_genericSmoothCore
  intro q
  apply isClosed_closure.mem_of_tendsto (energyApprox_tendsto I q)
  apply Eventually.of_forall
  intro M
  apply image_closure_subset_closure_image (fromGraphH1 I).continuous
  exact ⟨_, hd _, rfl⟩

end GptLean.PhysicalFreeReferenceCore
