import GptLean.PhysicalCoulombH1
import Mathlib.Analysis.Normed.Operator.Banach

/-!
The everywhere-defined Coulomb square-root graph map is closed, hence
bounded by the closed graph theorem. Its operator norm gives an actual
uniform quadratic Coulomb estimate on the electronic H1 reference.
-/

noncomputable section

namespace GptLean.PhysicalCoulombH1

open MeasureTheory GptLean.ElectronicH1Complex
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

private theorem operator_sq_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) (u : E) : ‖L u‖ ^ 2 ≤ ‖L‖ ^ 2 * ‖u‖ ^ 2 := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm u) 2

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

abbrev CoulombGraph (c : ℝ) := PhysicalMultiplicationGraph.GraphSpace volume (H := H)
  (fun x : SymmetricLift.Configuration N => (Real.sqrt (c * potential N x) : ℂ))

def potentialGraphLinear (c : ℝ) (hc : 0 ≤ c) :
    ComplexH1 H (Fin N × Fin 3) →ₗ[ℂ] CoulombGraph (N := N) (H := H) c where
  toFun := complexPotentialGraph c hc
  map_add' u v := by
    apply PhysicalMultiplicationGraph.inclusion_injective volume _
    simp only [inclusion_complexPotentialGraph, map_add]
  map_smul' a u := by
    apply PhysicalMultiplicationGraph.inclusion_injective volume _
    simp only [inclusion_complexPotentialGraph, map_smul, RingHom.id_apply]

theorem potentialGraphLinear_closed (c : ℝ) (hc : 0 ≤ c) :
    IsClosed ((potentialGraphLinear (N := N) (H := H) c hc).graph :
      Set (ComplexH1 H (Fin N × Fin 3) × CoulombGraph (N := N) (H := H) c)) := by
  have heq : ((potentialGraphLinear (N := N) (H := H) c hc).graph :
      Set (ComplexH1 H (Fin N × Fin 3) × CoulombGraph (N := N) (H := H) c)) =
      {p | PhysicalMultiplicationGraph.inclusion volume _ p.2 = value p.1} := by
    ext p
    change p.2 = complexPotentialGraph c hc p.1 ↔
      PhysicalMultiplicationGraph.inclusion volume _ p.2 = value p.1
    rw [← inclusion_complexPotentialGraph c hc p.1]
    exact (PhysicalMultiplicationGraph.inclusion_injective volume _).eq_iff.symm
  rw [heq]
  exact isClosed_eq ((PhysicalMultiplicationGraph.inclusion volume _).continuous.comp continuous_snd)
    (value.continuous.comp continuous_fst)

/-- A bounded graph-valued Coulomb map, derived from its actual domain. -/
def potentialGraphOperator (c : ℝ) (hc : 0 ≤ c) :
    ComplexH1 H (Fin N × Fin 3) →L[ℂ] CoulombGraph (N := N) (H := H) c :=
  ContinuousLinearMap.ofIsClosedGraph (potentialGraphLinear_closed c hc)

def sqrtPotentialOperator (c : ℝ) (hc : 0 ≤ c) :
    ComplexH1 H (Fin N × Fin 3) →L[ℂ] ElectronicH1Space.L2 H (Fin N × Fin 3) :=
  (PhysicalMultiplicationGraph.output volume _).comp (potentialGraphOperator c hc)

theorem sqrtPotentialOperator_energy (c : ℝ) (hc : 0 ≤ c)
    (u : ComplexH1 H (Fin N × Fin 3)) :
    ‖sqrtPotentialOperator c hc u‖ ^ 2 =
      ∫ x, (c * potential N x) * ‖value u x‖ ^ 2 := by
  have hn := Repair.toL2_norm_sq (Lp.memLp (sqrtPotentialOperator c hc u))
  simp only [Lp.toLp_coeFn] at hn
  rw [hn]
  apply integral_congr_ae
  filter_upwards [(complexPotentialGraph c hc u).property] with x hx
  change ‖(complexPotentialGraph c hc u).val.2 x‖ ^ 2 = _
  change (complexPotentialGraph c hc u).val.2 x =
    (Real.sqrt (c * potential N x) : ℂ) • value u x at hx
  rw [hx]
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (mul_nonneg hc (potential_nonneg N x))]

set_option backward.isDefEq.respectTransparency.types true in
theorem quadratic_bound (c : ℝ) (hc : 0 ≤ c)
    (u : ComplexH1 H (Fin N × Fin 3)) :
    (∫ x, (c * potential N x) * ‖value u x‖ ^ 2) ≤
      ‖sqrtPotentialOperator (N := N) (H := H) c hc‖ ^ 2 * ‖u‖ ^ 2 := by
  exact (sqrtPotentialOperator_energy c hc u).symm.le.trans
    (operator_sq_bound
      (E := ComplexH1 H (Fin N × Fin 3))
      (F := ElectronicH1Space.L2 H (Fin N × Fin 3))
      (sqrtPotentialOperator (N := N) (H := H) c hc) u)

/-- A positive uniform constant for the physical reverse comparison. -/
theorem exists_positive_quadratic_bound (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ComplexH1 H (Fin N × Fin 3),
      (∫ x, (c * potential N x) * ‖value u x‖ ^ 2) ≤ C * ‖u‖ ^ 2 := by
  refine ⟨‖sqrtPotentialOperator (N := N) (H := H) c hc‖ ^ 2 + 1, by positivity, ?_⟩
  intro u
  exact (quadratic_bound c hc u).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg _))

end GptLean.PhysicalCoulombH1
