import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Ordinary continuity of finite real quadratic-form pairings of bounded
complex-linear maps, before specializing the nested physical graph spaces. -/
noncomputable section
namespace PfHk.SlabFormAlgebra

open scoped InnerProductSpace

variable {X E H K Q J : Type*}

/-- Apply a bounded map with the source and target instances chosen at
abstract normed spaces, before specializing nested physical graph types. -/
def applyCLM [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (T : E →L[ℂ] H) (u : E) : H := T u

def realScale {V : Type*} [SMul ℝ V] (a : ℝ) (v : V) : V := a • v

theorem real_smul_congr {V : Type*} [SMul ℝ V] (a : ℝ) {x y : V} (h : x = y) :
    a • x = a • y := congrArg (fun z => a • z) h

theorem scaled_sub_congr {V : Type*} [AddCommGroup V] [Module ℝ V]
    (a b : ℝ) {x y z w : V} (hxy : x = y) (hzw : z = w) :
    a • (x-b • z) = a • (y-b • w) := by rw [hxy, hzw]

theorem zero_left_pair [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedSpace ℂ H]
    (T : E →L[ℂ] H) {x : E} (hx : x = 0) (y : H) : 2 * inner ℝ (T x) y = 0 := by
  rw [hx, map_zero, inner_zero_left, mul_zero]

theorem scaled_inner_congr [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a : ℝ) (z : H) {x y : H} (h : x = y) :
    inner ℝ (a • x) z = inner ℝ (a • y) z := by rw [h]

theorem continuous_affine_clm [TopologicalSpace X]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : Q →L[ℂ] H) (T : K →L[ℂ] Q →L[ℂ] H) {y : X → K} (hy : Continuous y) :
    Continuous (fun x => A + T (y x)) := continuous_const.add (T.continuous.comp hy)

theorem continuous_form_left [Fintype J]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [NormedSpace ℂ K]
    (R : E →L[ℂ] H) (A : J → E →L[ℂ] H) (D : E →L[ℂ] K) (S : K →L[ℂ] K) (u : E) :
    Continuous (fun v => inner ℝ (R v) (R u) + (∑ j, inner ℝ (A j v) (A j u)) +
      2 * inner ℝ (D v) (S (D u))) :=
  ((R.continuous.inner continuous_const).add
    (continuous_finsetSum _ fun j _ => (A j).continuous.inner continuous_const)).add
      (continuous_const.mul (D.continuous.inner continuous_const))

theorem angular_scaling [AddCommGroup H] [Module ℂ H] [Module ℝ H] [IsScalarTower ℝ ℂ H]
    [AddCommGroup Q] [Module ℂ Q] [Module ℝ Q] [IsScalarTower ℝ ℂ Q]
    (T : Q →ₗ[ℂ] H) (a : ℝ) (p : H) (q : Q) :
    a • p + Complex.I • T (a • q) = a • (p + Complex.I • T q) := by
  rw [T.map_smul_of_tower, smul_comm Complex.I a, smul_add]

theorem angular_of_reps [AddCommGroup H] [Module ℂ H] [Module ℝ H] [IsScalarTower ℝ ℂ H]
    [AddCommGroup Q] [Module ℂ Q] [Module ℝ Q] [IsScalarTower ℝ ℂ Q]
    (T : Q →ₗ[ℂ] H) (a : ℝ) {p p' : H} {q q' : Q}
    (hp : p = a • p') (hq : q = a • q') :
    p + Complex.I • T q = a • (p' + Complex.I • T q') := by
  rw [hp, hq]
  exact angular_scaling T a p' q'

theorem linear_of_smul_rep [AddCommGroup H] [Module ℂ H] [Module ℝ H] [IsScalarTower ℝ ℂ H]
    [AddCommGroup Q] [Module ℂ Q] [Module ℝ Q] [IsScalarTower ℝ ℂ Q]
    (T : Q →ₗ[ℂ] H) (a : ℝ) {q q' : Q} (hq : q = a • q') :
    T q = a • T q' := by rw [hq, T.map_smul_of_tower]

theorem clm_of_smul_rep [NormedAddCommGroup H] [NormedSpace ℂ H] [Module ℝ H] [IsScalarTower ℝ ℂ H]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q] [Module ℝ Q] [IsScalarTower ℝ ℂ Q]
    (T : Q →L[ℂ] H) (a : ℝ) {q q' : Q} (hq : q = a • q') :
    T q = a • T q' := linear_of_smul_rep T.toLinearMap a hq

theorem radial_test_scaling [AddCommGroup H] [Module ℂ H] [Module ℝ H] [IsScalarTower ℝ ℂ H]
    (d c a : ℝ) (v : H) :
    d • v + (c : ℂ) • (a • v) = (d + c*a) • v := by
  have hc : (c : ℂ) • (a • v) = c • (a • v) := IsScalarTower.algebraMap_smul ℂ c _
  rw [hc, smul_smul, add_smul]

theorem radial_test_of_rep [AddCommGroup H] [Module ℂ H] [Module ℝ H] [IsScalarTower ℝ ℂ H]
    (d c a : ℝ) {p v : H} (h : p = d • v) :
    p + (c : ℂ) • (a • v) = (d+c*a) • v := by
  rw [h]
  exact radial_test_scaling d c a v

theorem eq_of_sequence [TopologicalSpace E] {f g : E → ℝ} {x : E} {u : ℕ → E}
    (hf : Continuous f) (hg : Continuous g)
    (hu : Filter.Tendsto u Filter.atTop (nhds x)) (he : ∀ n, f (u n) = g (u n)) :
    f x = g x := by
  have hfirst := (hf.tendsto x).comp hu
  have hsecond := (hg.tendsto x).comp hu
  exact tendsto_nhds_unique hfirst (hsecond.congr (fun n => (he n).symm))

theorem continuous_pair_clm [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedSpace ℂ H]
    (T : E →L[ℂ] H) (z : H) : Continuous (fun x => inner ℝ (T x) z) :=
  T.continuous.inner continuous_const

end PfHk.SlabFormAlgebra
