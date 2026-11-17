import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.Normed.Operator.Basic

/-!
Extension of a multiplier product rule from a source core to a closed
covariant operator domain. The hypotheses are closedness of the actual
partially defined operator, convergence of source vectors and their
operator values, and bounded multiplier and commutator maps. The product
identity is assumed only on the approximating core, where the weak product
results in `CovariantProduct` can establish it.

The physical Pauli–Fierz covariant operator, its source core and the
identification of the multiplier and commutator operators are not
constructed here.
-/

namespace GptLean.Repair

open Filter
open scoped Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Closedness supplies both the multiplier's domain membership and the
covariant product identity at a limit of core vectors. The derivative
convergence of the multiplied sequence follows from the two bounded maps.
-/
theorem closed_covariant_product_of_graph_limit
    (D : E →ₗ.[𝕜] E) (hD : D.IsClosed)
    (M C : E →L[𝕜] E) {u du : E} (un : ℕ → D.domain)
    (hu : Tendsto (fun n => (un n : E)) atTop (𝓝 u))
    (hdu : Tendsto (fun n => D (un n)) atTop (𝓝 du))
    (hcore : ∀ n, ∃ v : D.domain,
      (v : E) = M (un n : E) ∧ D v = M (D (un n)) + C (un n : E)) :
    ∃ v : D.domain, (v : E) = M u ∧ D v = M du + C u := by
  have hvalues := (M.continuous.tendsto u).comp hu
  have hderivatives := ((M.continuous.tendsto du).comp hdu).add
    ((C.continuous.tendsto u).comp hu)
  have hgraph : ∀ n,
      (M (un n : E), M (D (un n)) + C (un n : E)) ∈ D.graph := by
    intro n
    exact (D.mem_graph_iff).mpr (hcore n)
  change IsClosed (D.graph : Set (E × E)) at hD
  exact (D.mem_graph_iff).mp
    (hD.mem_of_tendsto (hvalues.prodMk_nhds hderivatives)
      (Eventually.of_forall hgraph))

/-- A graph core is enough to extend its proved product rule to every
vector in the covariant operator domain. No product derivative or domain
preservation at the limiting vector is a premise. -/
theorem closed_covariant_product_of_graph_core
    (D : E →ₗ.[𝕜] E) (hD : D.IsClosed) (M C : E →L[𝕜] E)
    (core : Set E)
    (happrox : ∀ u : D.domain, ∃ un : ℕ → D.domain,
      (∀ n, (un n : E) ∈ core) ∧
      Tendsto (fun n => (un n : E)) atTop (𝓝 (u : E)) ∧
      Tendsto (fun n => D (un n)) atTop (𝓝 (D u)))
    (hcore : ∀ u : D.domain, (u : E) ∈ core → ∃ v : D.domain,
      (v : E) = M (u : E) ∧ D v = M (D u) + C (u : E)) :
    ∀ u : D.domain, ∃ v : D.domain,
      (v : E) = M (u : E) ∧ D v = M (D u) + C (u : E) := by
  intro u
  obtain ⟨un, hmem, hu, hdu⟩ := happrox u
  exact closed_covariant_product_of_graph_limit D hD M C un hu hdu
    (fun n => hcore (un n) (hmem n))

end GptLean.Repair
