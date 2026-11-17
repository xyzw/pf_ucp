import GptLean.PhysicalClosedForms
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
A dense symmetric family of first-order operators has a closed tuple
extension. Its graph is the actual closure of the joint graph. Testing
against the dense original domain proves that this closed relation is
single-valued, without assuming that the original restricted graph was
closed or describing the larger closure domain.
-/

noncomputable section

namespace GptLean.PhysicalSymmetricFamilyClosure

open scoped InnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency.types true

variable {E H I : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Fintype I]
  (value : E →L[ℂ] H) (A : I → E →L[ℂ] H)

def tupleOutput : E →L[ℂ] PiLp 2 (fun _ : I => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi A)

omit [Fintype I] in
@[simp] theorem tupleOutput_apply (u : E) (i : I) : tupleOutput A u i = A i u := rfl

def graphMap : E →L[ℂ] H × PiLp 2 (fun _ : I => H) := value.prod (tupleOutput A)

def closedGraph : Submodule ℂ (H × PiLp 2 (fun _ : I => H)) :=
  (graphMap value A).range.topologicalClosure

variable (hdense : DenseRange value)
  (hsym : ∀ i u v, inner ℂ (A i u) (value v) = inner ℂ (value u) (A i v))

include hsym in
/-- Symmetry identities persist on the joint graph closure. -/
theorem closedGraph_test (z : H × PiLp 2 (fun _ : I => H))
    (hz : z ∈ closedGraph value A) (i : I) (v : E) :
    inner ℂ (z.2 i) (value v) = inner ℂ z.1 (A i v) := by
  have hc : IsClosed {z : H × PiLp 2 (fun _ : I => H) |
      inner ℂ (z.2 i) (value v) = inner ℂ z.1 (A i v)} :=
    isClosed_eq (((PiLp.continuous_apply 2 _ i).comp continuous_snd).inner continuous_const)
      (continuous_fst.inner continuous_const)
  apply closure_minimal (t := {z : H × PiLp 2 (fun _ : I => H) |
      inner ℂ (z.2 i) (value v) = inner ℂ z.1 (A i v)}) _ hc hz
  rintro _ ⟨u, rfl⟩
  exact hsym i u v

include hdense hsym in
/-- The closed graph has no nonzero vector over zero. -/
theorem closedGraph_fst_zero (z : H × PiLp 2 (fun _ : I => H))
    (hz : z ∈ closedGraph value A) (hzero : z.1 = 0) : z.2 = 0 := by
  ext i
  change z.2 i = 0
  have hi : ∀ w : H, inner ℂ (z.2 i) w = 0 := by
    intro w
    refine (show Dense (Set.range value) from hdense).induction ?_ ?_ w
    · rintro _ ⟨v, rfl⟩
      have h := closedGraph_test value A hsym z hz i v
      simpa only [hzero, inner_zero_left] using h
    · exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
  exact inner_self_eq_zero.mp (hi (z.2 i))

/-- The single-valued closure of the symmetric first-order family. -/
def operator : H →ₗ.[ℂ] PiLp 2 (fun _ : I => H) := (closedGraph value A).toLinearPMap

include hdense hsym in
theorem operator_graph : (operator value A).graph = closedGraph value A :=
  Submodule.toLinearPMap_graph_eq _ (closedGraph_fst_zero value A hdense hsym)

include hdense hsym in
theorem operator_closed : (operator value A).IsClosed := by
  change IsClosed ((operator value A).graph : Set (H × PiLp 2 (fun _ : I => H)))
  rw [operator_graph value A hdense hsym]
  exact Submodule.isClosed_topologicalClosure _

include hdense hsym in
/-- Every original vector retains its exact covariant derivative tuple. -/
theorem original_mem_graph (u : E) :
    (value u, tupleOutput A u) ∈ (operator value A).graph := by
  rw [operator_graph value A hdense hsym]
  exact (graphMap value A).range.le_topologicalClosure ((graphMap value A).mem_range_self u)

include hdense hsym in
theorem original_domain (u : E) : value u ∈ (operator value A).domain :=
  LinearPMap.mem_domain_iff.mpr ⟨tupleOutput A u, original_mem_graph value A hdense hsym u⟩

include hdense hsym in
/-- The closure domain contains the original dense value range. -/
theorem operator_domain_dense : Dense ((operator value A).domain : Set H) := by
  apply hdense.mono
  rintro _ ⟨u, rfl⟩
  exact original_domain value A hdense hsym u

include hdense hsym in
theorem operator_original (u : E) :
    operator value A ⟨value u, original_domain value A hdense hsym u⟩ = tupleOutput A u :=
  (operator value A).mem_graph_snd_inj
    ((operator value A).mem_graph ⟨value u, original_domain value A hdense hsym u⟩)
    (original_mem_graph value A hdense hsym u) rfl

include hdense hsym in
/-- Pairing with every original test vector is valid on the full closed domain. -/
theorem operator_test (u : (operator value A).domain) (i : I) (v : E) :
    inner ℂ (operator value A u i) (value v) = inner ℂ (u : H) (A i v) := by
  apply closedGraph_test value A hsym (u, operator value A u) _ i v
  rw [← operator_graph value A hdense hsym]
  exact (operator value A).mem_graph u

theorem original_energy (u : E) : ‖tupleOutput A u‖ ^ 2 = ∑ i, ‖A i u‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

end GptLean.PhysicalSymmetricFamilyClosure
