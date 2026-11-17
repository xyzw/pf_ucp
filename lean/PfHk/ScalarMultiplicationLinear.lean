import GptLean.PhysicalMultiplicationGraph

/-! When scalar multiplication belongs to L2 on every vector of a linear
form domain, its actual L2 output is a linear map. The construction factors
through the existing maximal multiplication graph. -/

noncomputable section
namespace PfHk.ScalarMultiplicationLinear

open MeasureTheory GptLean
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types true

variable {X H Q : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [AddCommGroup Q] [Module ℂ Q]
  (μ : Measure X) (a : X → ℂ) (L : Q →ₗ[ℂ] Lp H 2 μ)
  (hm : ∀ u, MemLp (fun x => a x • L u x) 2 μ)

def graphLift : Q →ₗ[ℂ] PhysicalMultiplicationGraph.GraphSpace μ (H := H) a where
  toFun u := ⟨(L u, (hm u).toLp _), (hm u).coeFn_toLp⟩
  map_add' u v := by
    apply PhysicalMultiplicationGraph.inclusion_injective μ a
    change L (u + v) = L u + L v
    exact map_add L u v
  map_smul' c u := by
    apply PhysicalMultiplicationGraph.inclusion_injective μ a
    change L (c • u) = c • L u
    exact map_smul L c u

def multiplier : Q →ₗ[ℂ] Lp H 2 μ :=
  (PhysicalMultiplicationGraph.output μ a).toLinearMap.comp (graphLift μ a L hm)

@[simp] theorem multiplier_apply (u : Q) :
    multiplier μ a L hm u = (hm u).toLp (fun x => a x • L u x) := rfl

theorem multiplier_ae (u : Q) :
    (multiplier μ a L hm u : X → H) =ᵐ[μ] fun x => a x • L u x := (hm u).coeFn_toLp

/-- Lift given multiplication values to the maximal graph. This version
needs only their pointwise identity, with no change of Lp instances. -/
def graphLiftOfValues (R : Q → Lp H 2 μ)
    (hR : ∀ u, (R u : X → H) =ᵐ[μ] fun x => a x • L u x) :
    Q →ₗ[ℂ] PhysicalMultiplicationGraph.GraphSpace μ (H := H) a where
  toFun u := ⟨(L u, R u), hR u⟩
  map_add' u v := by
    apply PhysicalMultiplicationGraph.inclusion_injective μ a
    change L (u + v) = L u + L v
    exact map_add L u v
  map_smul' c u := by
    apply PhysicalMultiplicationGraph.inclusion_injective μ a
    change L (c • u) = c • L u
    exact map_smul L c u

def multiplierOfValues (R : Q → Lp H 2 μ)
    (hR : ∀ u, (R u : X → H) =ᵐ[μ] fun x => a x • L u x) :
    Q →ₗ[ℂ] Lp H 2 μ :=
  (PhysicalMultiplicationGraph.output μ a).toLinearMap.comp (graphLiftOfValues μ a L R hR)

@[simp] theorem multiplierOfValues_apply (R : Q → Lp H 2 μ)
    (hR : ∀ u, (R u : X → H) =ᵐ[μ] fun x => a x • L u x) (u : Q) :
    multiplierOfValues μ a L R hR u = R u := rfl

end PfHk.ScalarMultiplicationLinear
