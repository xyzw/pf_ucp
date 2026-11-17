import PfHk.PolarCalculus
import Mathlib.LinearAlgebra.LinearPMap

/-!
The ordinary sphere gradient graph is the closure of the span of the
actual C1 representative-gradient pairs in surface-measure L2. The sole
retained fact is its standard closability. This is ordinary operator
theory, universal in the Hilbert fiber, with no physical coefficient.
-/

noncomputable section
namespace PfHk.PolarCalculus

open MeasureTheory
open scoped ENNReal
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable (I : Type*) [Fintype I] [DecidableEq I]
  (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def smoothGradientPairs : Set (SphereHilbert I H × (I → SphereHilbert I H)) :=
  {p | ∃ f : UnitSphere I → H, SphereC1 f ∧ p.1 =ᵐ[sphereMeasure I] f ∧
    ∀ j, p.2 j =ᵐ[sphereMeasure I] sphereGradient f j}

def sphereGradientGraph : Submodule ℝ (SphereHilbert I H × (I → SphereHilbert I H)) :=
  (Submodule.span ℝ (smoothGradientPairs I H)).topologicalClosure

theorem sphereGradientGraph_closed :
    IsClosed (sphereGradientGraph I H : Set (SphereHilbert I H × (I → SphereHilbert I H))) :=
  (Submodule.span ℝ (smoothGradientPairs I H)).isClosed_topologicalClosure

theorem mem_sphereGradientGraph (u : SphereHilbert I H) (p : I → SphereHilbert I H)
    (f : UnitSphere I → H) (hf : SphereC1 f) (hu : u =ᵐ[sphereMeasure I] f)
    (hp : ∀ j, p j =ᵐ[sphereMeasure I] sphereGradient f j) :
    (u, p) ∈ sphereGradientGraph I H :=
  (Submodule.le_topologicalClosure _)
    (Submodule.subset_span (show (u, p) ∈ smoothGradientPairs I H from ⟨f, hf, hu, hp⟩))

/-- Standard closability of the ordinary gradient on a compact sphere.
The graph whose closability is asserted is explicitly constructed above. -/
structure StandardSphereGradient : Prop where
  closable : ∀ p ∈ sphereGradientGraph I H, p.1 = 0 → p.2 = 0

def sphereGradientOperator : SphereHilbert I H →ₗ.[ℝ] (I → SphereHilbert I H) :=
  (sphereGradientGraph I H).toLinearPMap

theorem sphereGradientOperator_graph (P : StandardSphereGradient I H) :
    (sphereGradientOperator I H).graph = sphereGradientGraph I H :=
  (sphereGradientGraph I H).toLinearPMap_graph_eq P.closable

end PfHk.PolarCalculus
