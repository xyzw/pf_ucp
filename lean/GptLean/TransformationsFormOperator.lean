import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
The operator represented by a densely defined sesquilinear form, and its
unitary and antiunitary covariance. The operator is constructed from its
variational graph, so covariance includes equality of operator domains.
-/

noncomputable section

namespace GptLean.TransformationsFormOperator

open scoped InnerProductSpace

variable {Q H : Type*} [AddCommGroup Q] [Module ℂ Q]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A densely embedded form domain. No operator or covariance conclusion is
part of this data. -/
structure Form where
  inclusion : Q →ₗ[ℂ] H
  injective : Function.Injective inclusion
  dense : DenseRange inclusion
  value : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ

namespace Form

variable (F : Form (Q := Q) (H := H))

/-- The variational graph of the operator associated with the form. -/
def graph : Submodule ℂ (H × H) where
  carrier := {p | ∃ u : Q, F.inclusion u = p.1 ∧
    ∀ v : Q, F.value v u = ⟪F.inclusion v, p.2⟫_ℂ}
  zero_mem' := ⟨0, map_zero _, by simp⟩
  add_mem' := by
    rintro x y ⟨u, hu, hqu⟩ ⟨v, hv, hqv⟩
    refine ⟨u + v, ?_, ?_⟩
    · simp only [map_add, hu, hv, Prod.fst_add]
    · intro w
      simp only [map_add, hqu, hqv, Prod.snd_add, inner_add_right]
  smul_mem' := by
    rintro c x ⟨u, hu, hqu⟩
    refine ⟨c • u, ?_, ?_⟩
    · simp only [map_smul, hu, Prod.smul_fst]
    · intro w
      simp only [map_smul, hqu, Prod.smul_snd, inner_smul_right, smul_eq_mul]

theorem mem_graph (x y : H) :
    (x, y) ∈ F.graph ↔ ∃ u : Q, F.inclusion u = x ∧
      ∀ v : Q, F.value v u = ⟪F.inclusion v, y⟫_ℂ := Iff.rfl

theorem graph_zero (y : H) (hy : (0, y) ∈ F.graph) : y = 0 := by
  obtain ⟨u, hu, hqu⟩ := hy
  have hu0 : u = 0 := F.injective (hu.trans (map_zero F.inclusion).symm)
  subst u
  apply F.dense.eq_of_inner_right ℂ
  intro v
  simpa using (hqu v).symm

/-- The represented operator as an actual partially defined linear map. -/
def operator : H →ₗ.[ℂ] H := F.graph.toLinearPMap

theorem operator_graph : F.operator.graph = F.graph :=
  F.graph.toLinearPMap_graph_eq (fun p hp hzero => by
    rcases p with ⟨x, y⟩
    dsimp at hzero
    subst x
    exact F.graph_zero y hp)

theorem mem_operator_graph (x y : H) :
    (x, y) ∈ F.operator.graph ↔ ∃ u : Q, F.inclusion u = x ∧
      ∀ v : Q, F.value v u = ⟪F.inclusion v, y⟫_ℂ := by
  rw [F.operator_graph]
  rfl

theorem mem_operator_domain (x : H) :
    x ∈ F.operator.domain ↔ ∃ u : Q, F.inclusion u = x ∧
      ∃ y : H, ∀ v : Q, F.value v u = ⟪F.inclusion v, y⟫_ℂ := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨u, hu, hqu⟩ := (F.mem_operator_graph x y).mp hy
    exact ⟨u, hu, y, hqu⟩
  · rintro ⟨u, hu, y, hqu⟩
    exact ⟨y, (F.mem_operator_graph x y).mpr ⟨u, hu, hqu⟩⟩

end Form

end GptLean.TransformationsFormOperator
