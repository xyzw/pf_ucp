import GptLean.PhysicalFockHardField
import GptLean.PhysicalFockFieldGraph
import GptLean.PhysicalPhotonHardSoft

/-!
Actual closed radiation and Segal field operators on the hard photon fiber.
Both input and output coordinates are restricted to the same generated Fock
subspace. The field graph is the maximal graph of its concrete sector actions.
On the radiation domain its action agrees with the constructed kernel field.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section Restriction

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def subspaceGraph (D : H →ₗ.[ℂ] H) (W : Submodule ℂ H) : Submodule ℂ (W × W) :=
  D.graph.comap (W.subtype.prodMap W.subtype)

private theorem subspaceGraph_fst_zero (D : H →ₗ.[ℂ] H) (W : Submodule ℂ H)
    (p : W × W) (hp : p ∈ subspaceGraph D W) (hzero : p.1 = 0) : p.2 = 0 := by
  apply Subtype.ext
  exact D.graph_fst_eq_zero_snd hp (congrArg Subtype.val hzero)

/-- Restriction of both coordinates of an actual operator graph. -/
def subspaceOperator (D : H →ₗ.[ℂ] H) (W : Submodule ℂ H) : W →ₗ.[ℂ] W :=
  (subspaceGraph D W).toLinearPMap

theorem subspaceOperator_graph (D : H →ₗ.[ℂ] H) (W : Submodule ℂ H) :
    (subspaceOperator D W).graph = subspaceGraph D W :=
  Submodule.toLinearPMap_graph_eq _ (subspaceGraph_fst_zero D W)

theorem subspaceOperator_graph_iff (D : H →ₗ.[ℂ] H) (W : Submodule ℂ H) (u v : W) :
    (u, v) ∈ (subspaceOperator D W).graph ↔ ((u : H), (v : H)) ∈ D.graph := by
  rw [subspaceOperator_graph]
  rfl

theorem subspaceOperator_closed (D : H →ₗ.[ℂ] H) (hD : D.IsClosed) (W : Submodule ℂ H) :
    (subspaceOperator D W).IsClosed := by
  change IsClosed ((subspaceOperator D W).graph : Set (W × W))
  rw [subspaceOperator_graph]
  exact hD.preimage ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))

end Restriction

section Rest

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The radiation and scalar-potential coordinates with their Hilbert sum norm. -/
def restGraph (D : H →ₗ.[ℂ] H) (a : ℂ) :
    Submodule ℂ (H × WithLp 2 (H × H)) where
  carrier := {p | (p.1, p.2.fst) ∈ D.graph ∧ p.2.snd = a • p.1}
  zero_mem' := ⟨D.graph.zero_mem, (smul_zero a).symm⟩
  add_mem' := by
    intro p q hp hq
    exact ⟨D.graph.add_mem hp.1 hq.1, by
      change p.2.snd + q.2.snd = a • (p.1 + q.1)
      rw [hp.2, hq.2, smul_add]⟩
  smul_mem' := by
    intro z p hp
    exact ⟨D.graph.smul_mem z hp.1, by
      change z • p.2.snd = a • (z • p.1)
      rw [hp.2, smul_comm]⟩

private theorem restGraph_fst_zero (D : H →ₗ.[ℂ] H) (a : ℂ)
    (p : H × WithLp 2 (H × H)) (hp : p ∈ restGraph D a) (hzero : p.1 = 0) :
    p.2 = 0 := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change p.2.fst = (0 : H)
    exact D.graph_fst_eq_zero_snd hp.1 hzero
  · change p.2.snd = (0 : H)
    exact hp.2.trans (by rw [hzero, smul_zero])

def restOperator (D : H →ₗ.[ℂ] H) (a : ℂ) : H →ₗ.[ℂ] WithLp 2 (H × H) :=
  (restGraph D a).toLinearPMap

theorem restOperator_graph (D : H →ₗ.[ℂ] H) (a : ℂ) :
    (restOperator D a).graph = restGraph D a :=
  Submodule.toLinearPMap_graph_eq _ (restGraph_fst_zero D a)

theorem restOperator_graph_iff (D : H →ₗ.[ℂ] H) (a : ℂ)
    (u : H) (v : WithLp 2 (H × H)) :
    (u, v) ∈ (restOperator D a).graph ↔
      (u, v.fst) ∈ D.graph ∧ v.snd = a • u := by
  rw [restOperator_graph]
  rfl

theorem restOperator_closed (D : H →ₗ.[ℂ] H) (hD : D.IsClosed) (a : ℂ) :
    (restOperator D a).IsClosed := by
  change IsClosed ((restOperator D a).graph : Set (H × WithLp 2 (H × H)))
  rw [restOperator_graph]
  have hfst : Continuous (fun v : WithLp 2 (H × H) => v.fst) := WithLp.continuous_fst 2 H H
  have hsnd : Continuous (fun v : WithLp 2 (H × H) => v.snd) := WithLp.continuous_snd 2 H H
  exact (hD.preimage (continuous_fst.prodMk
    (hfst.comp continuous_snd))).inter
      (isClosed_eq (hsnd.comp continuous_snd)
        (continuous_const.smul continuous_fst))

end Rest

section Segal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

def segalSubmodule (f : Lp ℂ 2 μ) : Submodule ℂ (Fock μ × Fock μ) where
  carrier := {p | SegalGraph μ f p.1 p.2}
  zero_mem' := by
    intro n
    exact (map_zero (segalCoordinate μ f n)).symm
  add_mem' := by
    intro u v hu hv n
    change (u.2 + v.2) n = segalCoordinate μ f n (u.1 + v.1)
    rw [lp.coeFn_add, Pi.add_apply, map_add, hu n, hv n]
  smul_mem' := by
    intro c u hu n
    change (c • u.2) n = segalCoordinate μ f n (c • u.1)
    rw [lp.coeFn_smul, Pi.smul_apply, map_smul, hu n]

private theorem segalSubmodule_fst_zero (f : Lp ℂ 2 μ) (p : Fock μ × Fock μ)
    (hp : p ∈ segalSubmodule μ f) (hzero : p.1 = 0) : p.2 = 0 := by
  apply lp.ext
  funext n
  have h := hp n
  rw [hzero, map_zero] at h
  exact h

/-- The ordinary maximal field operator is fixed by its sector graph. -/
def segalOperator (f : Lp ℂ 2 μ) : Fock μ →ₗ.[ℂ] Fock μ :=
  (segalSubmodule μ f).toLinearPMap

theorem segalOperator_graph (f : Lp ℂ 2 μ) :
    (segalOperator μ f).graph = segalSubmodule μ f :=
  Submodule.toLinearPMap_graph_eq _ (segalSubmodule_fst_zero μ f)

theorem segalOperator_graph_iff (f : Lp ℂ 2 μ) (u v : Fock μ) :
    (u, v) ∈ (segalOperator μ f).graph ↔ SegalGraph μ f u v := by
  rw [segalOperator_graph]
  rfl

theorem segalOperator_closed (f : Lp ℂ 2 μ) : (segalOperator μ f).IsClosed := by
  change IsClosed ((segalOperator μ f).graph : Set (Fock μ × Fock μ))
  rw [segalOperator_graph]
  exact segalGraph_closed μ f

end Segal

attribute [local irreducible] subspaceOperator restOperator segalOperator

section Hard

variable (c : ℝ)

def hardRadiationOperator :
    generatedFockSubspace (hardOnePhoton c) →ₗ.[ℂ] generatedFockSubspace (hardOnePhoton c) :=
  subspaceOperator radiationRoot (generatedFockSubspace (hardOnePhoton c))

theorem hardRadiationOperator_closed : (hardRadiationOperator c).IsClosed :=
  subspaceOperator_closed radiationRoot radiationRoot_closed _

theorem hardRadiationOperator_graph_iff
    (u v : generatedFockSubspace (hardOnePhoton c)) :
    (u, v) ∈ (hardRadiationOperator c).graph ↔ ((u : PhotonFock), (v : PhotonFock)) ∈ radiationRoot.graph :=
  subspaceOperator_graph_iff radiationRoot _ u v

theorem hardRadiationOperator_energy
    (u v : generatedFockSubspace (hardOnePhoton c))
    (h : (u, v) ∈ (hardRadiationOperator c).graph) :
    radiationForm (u : PhotonFock) = ENNReal.ofReal (‖v‖ ^ 2) := by
  obtain ⟨q, hq, hr⟩ := radiationRoot.mem_graph_iff.mp
    ((hardRadiationOperator_graph_iff c u v).mp h)
  have he := radiationRoot_energy q
  rw [hq, hr] at he
  exact he

def hardRestOperator (a : ℂ) :
    generatedFockSubspace (hardOnePhoton c) →ₗ.[ℂ]
      WithLp 2 (generatedFockSubspace (hardOnePhoton c) ×
        generatedFockSubspace (hardOnePhoton c)) :=
  restOperator (hardRadiationOperator c) a

theorem hardRestOperator_closed (a : ℂ) : (hardRestOperator c a).IsClosed :=
  restOperator_closed _ (hardRadiationOperator_closed c) a

theorem hardRestOperator_graph_iff (a : ℂ)
    (u : generatedFockSubspace (hardOnePhoton c))
    (v : WithLp 2 (generatedFockSubspace (hardOnePhoton c) ×
      generatedFockSubspace (hardOnePhoton c))) :
    (u, v) ∈ (hardRestOperator c a).graph ↔
      ((u : PhotonFock), (v.fst : PhotonFock)) ∈ radiationRoot.graph ∧ v.snd = a • u :=
  (restOperator_graph_iff (hardRadiationOperator c) a u v).trans
    (and_congr (hardRadiationOperator_graph_iff c u v.fst) Iff.rfl)

def hardFieldOperator (f : Lp ℂ 2 photonMeasure) :
    generatedFockSubspace (hardOnePhoton c) →ₗ.[ℂ] generatedFockSubspace (hardOnePhoton c) :=
  subspaceOperator (segalOperator photonMeasure f) (generatedFockSubspace (hardOnePhoton c))

theorem hardFieldOperator_closed (f : Lp ℂ 2 photonMeasure) :
    (hardFieldOperator c f).IsClosed :=
  subspaceOperator_closed (segalOperator photonMeasure f) (segalOperator_closed photonMeasure f) _

theorem hardFieldOperator_graph_iff (f : Lp ℂ 2 photonMeasure)
    (u v : generatedFockSubspace (hardOnePhoton c)) :
    (u, v) ∈ (hardFieldOperator c f).graph ↔ SegalGraph photonMeasure f u.val v.val :=
  (subspaceOperator_graph_iff (segalOperator photonMeasure f) _ u v).trans
    (segalOperator_graph_iff photonMeasure f u.val v.val)

/-- The hard graph contains the same concrete radiation-domain field action. -/
theorem hardFieldOperator_kernelField (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (hk : k.val.1 ∈ hardOnePhoton c)
    (q : RadiationGraphSpace)
    (hq : radiationGraphInclusion q ∈ generatedFockSubspace (hardOnePhoton c)) :
    (⟨radiationGraphInclusion q, hq⟩,
      ⟨kernelField C k q, kernelField_mem_generated C (hardOnePhoton c) k hk q hq⟩) ∈
        (hardFieldOperator c k.val.1).graph :=
  (hardFieldOperator_graph_iff c k.val.1 _ _).mpr (kernelField_segalGraph C k q)

/-- Simultaneous radiation and hard-field graph membership fixes the actual field value. -/
theorem hardFieldOperator_value (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (u v : generatedFockSubspace (hardOnePhoton c))
    (q : RadiationGraphSpace) (hq : radiationGraphInclusion q = u.val)
    (hv : (u, v) ∈ (hardFieldOperator c k.val.1).graph) :
    v.val = kernelField C k q := by
  apply segalGraph_unique photonMeasure k.val.1
    ((hardFieldOperator_graph_iff c k.val.1 u v).mp hv)
  exact hq ▸ kernelField_segalGraph C k q

end Hard

end GptLean.PhysicalFock
