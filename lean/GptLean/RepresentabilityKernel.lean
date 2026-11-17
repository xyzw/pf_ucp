import GptLean.Representability
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
The weighted field kernel in the photonic representability argument.

A bounded measurable family of one-photon coupling maps defines an actual
operator on the weighted L2 space. Its integral formula, symmetry and
positivity are proved from the Bochner integral and the Hilbert adjoint.
In the article the measure is rho times volume and the coupling map sends
a real three-vector to the corresponding sum of annular field kernels.
-/

noncomputable section

set_option Elab.async false

namespace GptLean.Representability

open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {X V H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsFiniteMeasure μ]

/-- Only measurability and a uniform bound on the one-photon coupling
maps are supplied. No integral operator or positivity is assumed. -/
structure BoundedCoupling (μ : Measure X) (V H : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  value : X → V →L[ℝ] H
  measurable : AEStronglyMeasurable value μ
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ᵐ x ∂μ, ‖value x‖ ≤ bound

namespace BoundedCoupling

variable (G : BoundedCoupling μ V H)

omit [IsFiniteMeasure μ] in
theorem adjoint_measurable (h : H) :
    AEStronglyMeasurable (fun x => (G.value x).adjoint h) μ :=
  (ContinuousLinearMap.adjoint.continuous.comp_aestronglyMeasurable G.measurable).apply_continuousLinearMap
    h

omit [IsFiniteMeasure μ] in
theorem adjoint_bound (h : H) :
    ∀ᵐ x ∂μ, ‖(G.value x).adjoint h‖ ≤ G.bound * ‖h‖ := by
  filter_upwards [G.norm_le] with x hx
  exact ((G.value x).adjoint.le_opNorm h).trans
    (mul_le_mul_of_nonneg_right (by simpa using hx) (norm_nonneg h))

theorem adjoint_memLp (h : H) : MemLp (fun x => (G.value x).adjoint h) 2 μ :=
  MemLp.of_bound (G.adjoint_measurable h) _ (G.adjoint_bound h)

/-- Evaluation of all coupling adjoints in the density-weighted L2 space. -/
def analysisLinear : H →ₗ[ℝ] Lp V 2 μ where
  toFun h := (G.adjoint_memLp h).toLp (fun x => (G.value x).adjoint h)
  map_add' h k := by
    apply Lp.ext
    filter_upwards [(G.adjoint_memLp (h + k)).coeFn_toLp,
      (G.adjoint_memLp h).coeFn_toLp, (G.adjoint_memLp k).coeFn_toLp,
      Lp.coeFn_add ((G.adjoint_memLp h).toLp _) ((G.adjoint_memLp k).toLp _)]
      with x hsum hh hk hadd
    rw [hsum, hadd, Pi.add_apply, hh, hk, map_add]
  map_smul' c h := by
    apply Lp.ext
    simp only [RingHom.id_apply]
    filter_upwards [(G.adjoint_memLp (c • h)).coeFn_toLp,
      (G.adjoint_memLp h).coeFn_toLp,
      Lp.coeFn_smul c ((G.adjoint_memLp h).toLp _)] with x hsmul hh heq
    rw [hsmul, heq, Pi.smul_apply, hh, map_smul]

theorem analysisLinear_bound (h : H) :
    ‖G.analysisLinear h‖ ≤
      ((measureUnivNNReal μ : ℝ) ^ (1 / 2 : ℝ) * G.bound) * ‖h‖ := by
  have hb : ∀ᵐ x ∂μ, ‖G.analysisLinear h x‖ ≤ G.bound * ‖h‖ := by
    filter_upwards [(G.adjoint_memLp h).coeFn_toLp, G.adjoint_bound h] with x hx hb
    exact hx ▸ hb
  have hn := Lp.norm_le_of_ae_bound (mul_nonneg G.bound_nonneg (norm_nonneg h)) hb
  convert hn using 1
  norm_num
  ring

def analysis : H →L[ℝ] Lp V 2 μ :=
  G.analysisLinear.mkContinuous
    ((measureUnivNNReal μ : ℝ) ^ (1 / 2 : ℝ) * G.bound) G.analysisLinear_bound

theorem analysis_ae (h : H) :
    (G.analysis h : X → V) =ᵐ[μ] (fun x => (G.value x).adjoint h) :=
  (G.adjoint_memLp h).coeFn_toLp

omit [CompleteSpace V] [CompleteSpace H] in
theorem synthesis_integrable (u : Lp V 2 μ) :
    Integrable (fun x => G.value x (u x)) μ := by
  apply ((Lp.memLp u).integrable (by norm_num)).norm.const_mul G.bound |>.mono'
    ((ContinuousLinearMap.id ℝ (V →L[ℝ] H)).aestronglyMeasurable_comp₂
      G.measurable (Lp.aestronglyMeasurable u))
  filter_upwards [G.norm_le] with x hx
  exact ((G.value x).le_opNorm (u x)).trans
    (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

/-- The abstract adjoint is exactly the Bochner synthesis integral. -/
theorem synthesis_eq_integral (u : Lp V 2 μ) :
    G.analysis.adjoint u = ∫ x, G.value x (u x) ∂μ := by
  apply ext_inner_left ℝ
  intro h
  rw [ContinuousLinearMap.adjoint_inner_right, ← integral_inner (G.synthesis_integrable u),
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [G.analysis_ae h] with x hx
  rw [hx, ContinuousLinearMap.adjoint_inner_left]

/-- The article's kernel, including its factor two. -/
def kernel : Lp V 2 μ →L[ℝ] Lp V 2 μ :=
  (2 : ℝ) • (G.analysis.comp G.analysis.adjoint)

theorem kernel_ae (u : Lp V 2 μ) :
    (G.kernel u : X → V) =ᵐ[μ]
      (fun x => (2 : ℝ) • ((G.value x).adjoint (∫ y, G.value y (u y) ∂μ))) := by
  filter_upwards [Lp.coeFn_smul (2 : ℝ) (G.analysis (G.analysis.adjoint u)),
    G.analysis_ae (G.analysis.adjoint u)] with x hsmul hx
  change ((2 : ℝ) • G.analysis (G.analysis.adjoint u)) x = _
  rw [hsmul, Pi.smul_apply, hx, G.synthesis_eq_integral]

/-- The integral kernel is the Gram kernel of the coupling family. -/
theorem kernel_integral_ae (u : Lp V 2 μ) :
    (G.kernel u : X → V) =ᵐ[μ]
      (fun x => ∫ y, (2 : ℝ) • ((G.value x).adjoint (G.value y (u y))) ∂μ) := by
  filter_upwards [G.kernel_ae u] with x hx
  rw [hx, ← (G.value x).adjoint.integral_comp_comm (G.synthesis_integrable u),
    integral_smul]

/-- Equation `photonic-kernel-positivity`, with the integral constructed. -/
theorem kernel_quadratic (u : Lp V 2 μ) :
    ⟪u, G.kernel u⟫_ℝ = 2 * ‖∫ x, G.value x (u x) ∂μ‖ ^ 2 := by
  change ⟪u, (2 : ℝ) • G.analysis (G.analysis.adjoint u)⟫_ℝ = _
  rw [real_inner_smul_right, ← ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq, G.synthesis_eq_integral]

theorem kernel_nonneg (u : Lp V 2 μ) : 0 ≤ ⟪u, G.kernel u⟫_ℝ := by
  rw [G.kernel_quadratic]
  positivity

theorem kernel_symmetric (u v : Lp V 2 μ) :
    ⟪G.kernel u, v⟫_ℝ = ⟪u, G.kernel v⟫_ℝ := by
  change ⟪(2 : ℝ) • G.analysis (G.analysis.adjoint u), v⟫_ℝ =
    ⟪u, (2 : ℝ) • G.analysis (G.analysis.adjoint v)⟫_ℝ
  rw [real_inner_smul_left, real_inner_smul_right,
    ← G.analysis.adjoint_inner_right, ← G.analysis.adjoint_inner_left]

end BoundedCoupling

end GptLean.Representability
