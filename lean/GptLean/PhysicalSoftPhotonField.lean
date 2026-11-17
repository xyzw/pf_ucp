import GptLean.PhysicalSoftSpatialField
import GptLean.PhysicalFermionicSeed

/-!
The actual photon Gaussian field interface uses the full radiation domain
and the soft radiation square root. Its labels are the same explicit
article kernels as the spatial interface. The vacuum statements follow
from its actual graph and the concrete creation and annihilation operators.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

/-- Apply a bounded map on the actual radiation graph, extended by zero
off the radiation domain. -/
def radiationGraphApply (L : RadiationGraphSpace →L[ℂ] PhotonFock)
    (u : PhotonFock) : PhotonFock := by
  classical
  exact if h : u ∈ radiationRoot.domain then
    L ⟨(u, radiationRoot ⟨u, h⟩), radiationRoot.mem_graph ⟨u, h⟩⟩ else 0

theorem radiationGraph_exists {u : PhotonFock} (h : u ∈ radiationRoot.domain) :
    ∃ q : RadiationGraphSpace, radiationGraphInclusion q = u :=
  ⟨⟨(u, radiationRoot ⟨u, h⟩), radiationRoot.mem_graph ⟨u, h⟩⟩, rfl⟩

theorem radiationGraphApply_of_graph (L : RadiationGraphSpace →L[ℂ] PhotonFock)
    (q : RadiationGraphSpace) : radiationGraphApply L (radiationGraphInclusion q) = L q := by
  obtain ⟨u, hu, hv⟩ := radiationRoot.mem_graph_iff.mp q.property
  have hd : radiationGraphInclusion q ∈ radiationRoot.domain := by
    change q.val.1 ∈ radiationRoot.domain
    exact hu ▸ u.property
  rw [radiationGraphApply, dite_eq_left hd]
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change radiationRoot ⟨radiationGraphInclusion q, hd⟩ = radiationGraphDerivative q
    have harg : (⟨radiationGraphInclusion q, hd⟩ : radiationRoot.domain) = u :=
      Subtype.ext hu.symm
    have hv' : radiationRoot u = radiationGraphDerivative q := hv
    exact (congrArg radiationRoot harg).trans hv'

theorem radiationGraphApply_add (L M : RadiationGraphSpace →L[ℂ] PhotonFock)
    (u : PhotonFock) :
    radiationGraphApply (L + M) u = radiationGraphApply L u + radiationGraphApply M u := by
  classical
  unfold radiationGraphApply
  split_ifs <;> simp only [add_apply, add_zero]

@[simp] theorem radiationGraphApply_soft (κ : ℝ) :
    radiationGraphApply (softRadiationRoot κ) = softRadiation κ := rfl

end GptLean.PhysicalFock

namespace GptLean.PhysicalPolarization

open MeasureTheory Gaussian PhysicalFock PhysicalNormalTrace PhotonLocalizationChannel
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable (F : Frame) (χ : ArticleCutoff) (κ : ℝ) (hκ : 0 ≤ κ)
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) (F.softRealStructure κ))

local instance softPhotonHardNormedAddCommGroup : NormedAddCommGroup (HardPhotonFock κ) :=
  Submodule.normedAddCommGroup (𝕜 := ℂ) (E := PhotonFock) (HardPhotonFock κ)

local instance softPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance softPhotonHardDirectInner : InnerProductSpace ℂ (HardPhotonFock κ) :=
  { (inferInstance : InnerProductSpace ℂ (HardPhotonFock κ)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (HardPhotonFock κ)) }

local instance softPhotonHardRealNormedSpace : NormedSpace ℝ (HardPhotonFock κ) :=
  NormedSpace.complexToReal (E := HardPhotonFock κ)

local instance softPhotonHardL2RealNormedSpace {X : Type*} [MeasurableSpace X]
    (ν : Measure X) : NormedSpace ℝ (Lp (HardPhotonFock κ) 2 ν) :=
  Lp.instNormedSpace (𝕜 := ℝ) (E := HardPhotonFock κ) (p := 2) (μ := ν)

attribute [local irreducible] photonGaussianUnitary

set_option backward.isDefEq.respectTransparency.types true in
/-- The photon field is the actual weighted-kernel field on its radiation graph. -/
def photonWienerSegal : WienerSegalData W.space.Q PhotonFock
    (HardPhotonFock κ) DerivativeLabel W.space.measure :=
  WienerSegalData.ofUnitary (Q := W.space.Q) (H := PhotonFock)
    (K := HardPhotonFock κ) (μ := W.space.measure) (G := DerivativeLabel)
    (photonGaussianUnitary BF κ W)
    (fun _ u => u ∈ radiationRoot.domain)
    (fun g => radiationGraphApply (kernelField C (labelKernel F χ κ hκ g)))
    (fun g => W.firstChaos (realLabel F χ κ hκ g)) (by
      intro g u hu
      obtain ⟨q, rfl⟩ := radiationGraph_exists hu
      rw [radiationGraphApply_of_graph]
      exact photonGaussianUnitary_field BF κ W C (realLabel F χ κ hκ g)
        (labelKernel F χ κ hκ g) (labelKernel_realLabel F χ κ hκ g) q)

theorem photonWienerSegal_field_of_graph (g : DerivativeLabel) (q : RadiationGraphSpace) :
    (photonWienerSegal F χ κ hκ BF C W).field g (radiationGraphInclusion q) =
      kernelField C (labelKernel F χ κ hκ g) q :=
  radiationGraphApply_of_graph _ q

theorem photonWienerSegal_coordinate (g : DerivativeLabel) :
    (photonWienerSegal F χ κ hκ BF C W).coordinate g =
      W.firstChaos (realLabel F χ κ hκ g) := rfl

theorem photonWienerSegal_coordinate_eq_spatial {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] [IsSeparable ν] (g : DerivativeLabel) :
    (photonWienerSegal F χ κ hκ BF C W).coordinate g =
      (spatialWienerSegal F χ κ hκ BF C W ν).coordinate g := rfl

set_option backward.isDefEq.respectTransparency.types true in
private theorem photon_creation_on_domain (g : DerivativeLabel) (u : PhotonFock)
    (hu : u ∈ radiationRoot.domain) :
    ‖radiationGraphApply (kernelCreation C (labelKernel F χ κ hκ g)) u‖ ^ 2 =
      ‖radiationGraphApply (kernelAnnihilation (labelKernel F χ κ hκ g)) u‖ ^ 2 +
        (∫ p : PhotonMode, ‖softDerivativeKernel Prod.fst g.derivatives κ g.position
          (base F χ g.component) p‖ ^ 2 ∂photonMeasure) * ‖u‖ ^ 2 := by
  obtain ⟨q, rfl⟩ := radiationGraph_exists hu
  have hc := congrArg (fun v : PhotonFock => ‖v‖ ^ 2)
    (radiationGraphApply_of_graph (kernelCreation C (labelKernel F χ κ hκ g)) q)
  have ha := congrArg (fun v : PhotonFock => ‖v‖ ^ 2)
    (radiationGraphApply_of_graph (kernelAnnihilation (labelKernel F χ κ hκ g)) q)
  have hk := derivativeKernel_fst_norm_sq F χ hκ g.component g.derivatives g.position
  calc
    _ = ‖kernelCreation C (labelKernel F χ κ hκ g) q‖ ^ 2 := hc
    _ = ‖kernelAnnihilation (labelKernel F χ κ hκ g) q‖ ^ 2 +
        ‖(labelKernel F χ κ hκ g).val.1‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 :=
      creationRadiation_norm_sq C (labelKernel F χ κ hκ g).val.1
        (labelKernel F χ κ hκ g).val.2 (labelKernel F χ κ hκ g).property q
    _ = _ := congrArg₂ (fun a b : ℝ => a + b * ‖radiationGraphInclusion q‖ ^ 2)
      ha.symm hk

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : RankOneData PhotonFock T} (normal : NormalTraceData R) (functional : NormalFunctionalData R)

set_option backward.isDefEq.respectTransparency.types true in
include BF C normal functional in
private theorem photon_annihilation_on_domain (g : DerivativeLabel) (u : PhotonFock)
    (hu : u ∈ radiationRoot.domain) :
    ‖radiationGraphApply (kernelAnnihilation (labelKernel F χ κ hκ g)) u‖ ≤
      Real.sqrt (∫ p : PhotonMode, (1 / ‖p.1‖) *
        ‖softDerivativeKernel Prod.fst g.derivatives κ g.position
          (base F χ g.component) p‖ ^ 2 ∂photonMeasure) * ‖softRadiation κ u‖ := by
  obtain ⟨q, rfl⟩ := radiationGraph_exists hu
  have ha := congrArg (fun v : PhotonFock => ‖v‖)
    (radiationGraphApply_of_graph (kernelAnnihilation (labelKernel F χ κ hκ g)) q)
  have hr := congrArg (fun v : PhotonFock => ‖v‖) (softRadiation_of_graph κ q)
  have hk := derivativeKernel_snd_norm F χ hκ g.component g.derivatives g.position
  calc
    _ = ‖kernelAnnihilation (labelKernel F χ κ hκ g) q‖ := ha
    _ ≤ ‖(labelKernel F χ κ hκ g).val.2‖ * ‖softRadiationRoot κ q‖ :=
      kernelAnnihilation_soft_bound normal functional BF C κ (labelKernel F χ κ hκ g)
        (derivativeKernel_fst_mem F χ hκ g.component g.derivatives g.position) q
    _ = _ := congrArg₂ (fun a b : ℝ => a * b) hk hr.symm

set_option backward.isDefEq.respectTransparency.types true in
/-- All field estimates use the actual source soft energy. -/
def photonKernelFieldData : KernelFieldData photonMeasure
    (photonWienerSegal F χ κ hκ BF C W) (fun p => 1 / ‖p.1‖) where
  kernel g := softDerivativeKernel Prod.fst g.derivatives κ g.position (base F χ g.component)
  weight_nonneg _ := by positivity
  radiationDomain u := u ∈ radiationRoot.domain
  radiation := softRadiation κ
  ann g := radiationGraphApply (kernelAnnihilation (labelKernel F χ κ hκ g))
  cre g := radiationGraphApply (kernelCreation C (labelKernel F χ κ hκ g))
  field_domain _ _ h _ _ := h
  field_eq g u _ := radiationGraphApply_add _ _ u
  annihilation_bound g u _ hu _ :=
    photon_annihilation_on_domain F χ κ hκ BF C normal functional g u hu
  creation_norm_sq g u hu _ := photon_creation_on_domain F χ κ hκ C g u hu

theorem photonKernelFieldData_kernel (g : DerivativeLabel) :
    (photonKernelFieldData F χ κ hκ BF C W normal functional).kernel g =
      softDerivativeKernel Prod.fst g.derivatives κ g.position (base F χ g.component) := rfl

theorem photonKernelFieldData_radiation :
    (photonKernelFieldData F χ κ hκ BF C W normal functional).radiation = softRadiation κ := rfl

/-- The photon and electronic interfaces use exactly the same explicit kernel. -/
theorem photonKernelFieldData_kernel_eq_spatial {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] [IsSeparable ν] (g : DerivativeLabel) :
    (photonKernelFieldData F χ κ hκ BF C W normal functional).kernel g =
      (spatialKernelFieldData F χ κ hκ BF C W ν normal functional).kernel g := rfl

section Vacuum

/-- The ordinary zero-photon vector, already constructed in the physical reference core. -/
abbrev photonVacuum : PhotonFock := PhysicalFermionicSeed.vacuum

theorem photonVacuum_norm : ‖photonVacuum‖ = 1 := PhysicalFermionicSeed.vacuum_norm

theorem photonVacuum_radiationDomain : photonVacuum ∈ radiationRoot.domain :=
  LinearPMap.mem_domain_iff.mpr ⟨0, PhysicalFermionicSeed.vacuum_radiation_graph⟩

theorem photonVacuum_softRadiation_zero : softRadiation κ photonVacuum = 0 := by
  change softRadiation κ (radiationGraphInclusion PhysicalFermionicSeed.vacuumGraph) = 0
  rw [softRadiation_of_graph]
  change (softRootRatioWeight κ).operator zero_le_one 0 = 0
  exact map_zero _

theorem photonVacuum_fieldDomain (g : DerivativeLabel) :
    (photonWienerSegal F χ κ hκ BF C W).fieldDomain g photonVacuum :=
  photonVacuum_radiationDomain

private theorem photonVacuum_mem_generated_bot :
    photonVacuum ∈ generatedFockSubspace (⊥ : Submodule ℂ (Lp ℂ 2 photonMeasure)) :=
  creationWord_mem_generated photonMeasure ⊥ [] (by simp)

private theorem weightedKernel_mem_bot_orthogonal (k : WeightedPhotonKernel) :
    k.val.1 ∈ (⊥ : Submodule ℂ (Lp ℂ 2 photonMeasure))ᗮ := by
  simp

/-- Every actual photon field has zero vacuum mean. -/
theorem photonVacuum_field_inner_zero (g : DerivativeLabel) :
    inner ℂ photonVacuum ((photonWienerSegal F χ κ hκ BF C W).field g photonVacuum) = 0 := by
  change inner ℂ photonVacuum
    ((photonWienerSegal F χ κ hκ BF C W).field g
      (radiationGraphInclusion PhysicalFermionicSeed.vacuumGraph)) = 0
  rw [photonWienerSegal_field_of_graph]
  exact kernelField_inner_eq_zero_of_orthogonal C ⊥ (labelKernel F χ κ hκ g)
    (weightedKernel_mem_bot_orthogonal _) PhysicalFermionicSeed.vacuumGraph
    photonVacuum_mem_generated_bot photonVacuum photonVacuum_mem_generated_bot

/-- Vacuum variance is the exact norm of the explicit article derivative kernel. -/
theorem photonVacuum_field_norm_sq (g : DerivativeLabel) :
    ‖(photonWienerSegal F χ κ hκ BF C W).field g photonVacuum‖ ^ 2 =
      ∫ p, ‖softDerivativeKernel Prod.fst g.derivatives κ g.position
        (base F χ g.component) p‖ ^ 2 ∂photonMeasure := by
  change ‖(photonWienerSegal F χ κ hκ BF C W).field g
    (radiationGraphInclusion PhysicalFermionicSeed.vacuumGraph)‖ ^ 2 = _
  rw [photonWienerSegal_field_of_graph]
  have h := kernelField_norm_sq_of_orthogonal C ⊥ (labelKernel F χ κ hκ g)
    (weightedKernel_mem_bot_orthogonal _) PhysicalFermionicSeed.vacuumGraph
    photonVacuum_mem_generated_bot
  change ‖kernelField C (labelKernel F χ κ hκ g) PhysicalFermionicSeed.vacuumGraph‖ ^ 2 =
    ‖(labelKernel F χ κ hκ g).val.1‖ ^ 2 * ‖photonVacuum‖ ^ 2 at h
  rw [photonVacuum_norm, one_pow, mul_one] at h
  exact h.trans (derivativeKernel_fst_norm_sq F χ hκ g.component g.derivatives g.position)

theorem photonVacuum_soft_field_variance (i : Fin 3) (x : FieldSpace) :
    ‖(photonWienerSegal F χ κ hκ BF C W).field ⟨i, [], x⟩ photonVacuum‖ ^ 2 =
      ∫ p, ‖softBase Prod.fst κ (base F χ i) p‖ ^ 2 ∂photonMeasure := by
  rw [photonVacuum_field_norm_sq]
  apply integral_congr_ae
  exact ae_of_all _ fun p => congrArg (fun r : ℝ => r ^ 2)
    (norm_softDerivativeKernel_nil Prod.fst κ x (base F χ i) p)

end Vacuum

end GptLean.PhysicalPolarization
