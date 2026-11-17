import PfHk.PhysicalOperatorCore
import PfHk.L2OperatorDerivative

/-!
The standard Weyl smooth-vector regularity input used for graph-core
transport. It is universal in the finite-dimensional parameter space and
in the one-photon displacement labels. The graph action is the already
constructed `weylWeightedGraph`, not an unspecified operator family.

The two retained facts are ordinary C1 regularity of Weyl action on a
uniform finite-particle core, and C1 regularity in the square-root radiation
graph when the original curve is C1 in the full radiation graph and the
displacement is C1 together with its square-root-frequency weight.

No physical kernel, spatial center, polar-coordinate identity, angular
operator, Carleman estimate, or unique-continuation conclusion is a field
of this standard operator-theory background. All those specializations
must be proved separately.
-/

noncomputable section
namespace PfHk.WeylGraphC1Calculus

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalWeyl
  GptLean.Representability GptLean.SymmetricLift PfHk.PhysicalOperatorDomain
open scoped ENNReal
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true

local instance weylCoreFullRealNormedSpace : NormedSpace ℝ FullRadiationGraph :=
  NormedSpace.restrictScalars ℝ ℂ _

/-- Select the derivative's real normed-space instances before specializing
to nested operator graphs. This is literally ordinary `HasDerivAt`. -/
abbrev HasGraphDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (df : E) (t : ℝ) : Prop := HasDerivAt f df t

theorem smooth_curve_hasDerivAt {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : E → H) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {x : ℝ → E} {dx : E} {t : ℝ} (hx : HasDerivAt x dx t) :
    HasGraphDerivAt (fun s => f (x s)) (fderiv ℝ f (x t) dx) t :=
  (hf.differentiable (by simp) (x t)).hasFDerivAt.comp_hasDerivAt t hx

theorem mapped_derivative_unique {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : E →L[ℝ] H) {f : ℝ → E} {g : ℝ → H} {df : E} {dg : H} {t : ℝ}
    (hf : HasGraphDerivAt f df t) (hg : HasGraphDerivAt g dg t)
    (he : (fun s => T (f s)) = g) : T df = dg := by
  have h := T.hasFDerivAt.comp_hasDerivAt t hf
  change HasDerivAt (fun s => T (f s)) (T df) t at h
  rw [he] at h
  exact h.unique hg

def graphAction {E : Type*} (W : ConcreteWeylLaw photonMeasure)
    (f y : E → Lp ℂ 2 photonMeasure)
    (hy : ∀ x, ∀ᵐ p ∂photonMeasure, y x p = (Real.sqrt ‖p.1‖ : ℂ) * f x p)
    (u : E → FullRadiationGraph) (x : E) : RadiationGraphSpace :=
  weylWeightedGraph W (f x) (y x) (hy x) (fullRootProjection (u x))

/-- Standard smooth-vector Weyl calculus, expressed only as regularity of
the actual operators and graphs. This is a retained operator-theory input. -/
structure StandardWeylGraphC1 (W : ConcreteWeylLaw photonMeasure) : Prop where
  ambient_c1 : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → Lp ℂ 2 photonMeasure) (u : E → PhotonFock) (M : ℕ),
    ContDiff ℝ (1 : ℕ∞) f → ContDiff ℝ (1 : ℕ∞) u →
    (∀ x, FiniteNumberSupport photonMeasure M (u x)) →
    ContDiff ℝ (1 : ℕ∞) (fun x => W.weyl (f x) (u x))
  graph_c1 : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f y : E → Lp ℂ 2 photonMeasure)
    (hy : ∀ x, ∀ᵐ p ∂photonMeasure, y x p = (Real.sqrt ‖p.1‖ : ℂ) * f x p)
    (u : E → FullRadiationGraph) (M : ℕ),
    ContDiff ℝ (1 : ℕ∞) f → ContDiff ℝ (1 : ℕ∞) y → ContDiff ℝ (1 : ℕ∞) u →
    (∀ x, FiniteNumberSupport photonMeasure M (fullRadiationInclusion (u x))) →
    ContDiff ℝ (1 : ℕ∞) (graphAction W f y hy u)
  parameter_graph_c1 : ∀ (K : Type) [TopologicalSpace K] [CompactSpace K]
    (f df y dy : ℝ × K → Lp ℂ 2 photonMeasure)
    (hy : ∀ x, ∀ᵐ p ∂photonMeasure, y x p = (Real.sqrt ‖p.1‖ : ℂ) * f x p)
    (u du : ℝ × K → FullRadiationGraph) (M : ℕ),
    Continuous f → Continuous df → Continuous y → Continuous dy →
    Continuous u → Continuous du →
    (∀ k t, L2OperatorDerivative.HasL2DerivAt (fun s => f (s, k)) (df (t, k)) t) →
    (∀ k t, L2OperatorDerivative.HasL2DerivAt (fun s => y (s, k)) (dy (t, k)) t) →
    (∀ k t, HasGraphDerivAt (fun s => u (s, k)) (du (t, k)) t) →
    (∀ x, FiniteNumberSupport photonMeasure M (fullRadiationInclusion (u x))) →
    Continuous (graphAction W f y hy u) ∧
      ∃ d : ℝ × K → RadiationGraphSpace, Continuous d ∧
        ∀ k t, HasGraphDerivAt (fun s => graphAction W f y hy u (s, k)) (d (t, k)) t

end PfHk.WeylGraphC1Calculus
