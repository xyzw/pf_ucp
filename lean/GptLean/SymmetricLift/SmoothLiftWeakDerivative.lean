import GptLean.SymmetricLift.FullSmoothTensorLift
import GptLean.SymmetricLift.SobolevRemovability

/-! Weak derivatives of the constructed tensor lift for differentiable tensor
fields. The classical product derivative on distinct configurations is derived
from the recursive construction and then extended across collision diagonals.
Integrability of the three test products remains explicit. -/

noncomputable section
namespace GptLean.SymmetricLift

open MeasureTheory TopologicalSpace

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [SeparableSpace V]

/-- The tensor field obtained from the actual recursive lift. -/
def recursiveLiftField (B : TensorBackground V) (N : ℕ)
    (T : Configuration N → B.H N) :
    Configuration N → (recursiveLiftCandidate B N).target :=
  fun x => (recursiveLiftCandidate B N).operator x (T x)

/-- The product derivative contains the variation of the constructed operator
and the lifted derivative of the input field. -/
def recursiveLiftFieldDerivative (B : TensorBackground V) (N : ℕ)
    (T : Configuration N → B.H N) (x d : Configuration N) :
    (recursiveLiftCandidate B N).target :=
  (fderiv ℝ (recursiveLiftCandidate B N).operator x d) (T x) +
    (recursiveLiftCandidate B N).operator x (fderiv ℝ T x d)

/-- Flatness makes the operator and input variations orthogonal, so their
squared derivative norms add without a cross term. -/
theorem recursiveLiftFieldDerivative_norm_sq
    (B : TensorBackground V) (N : ℕ) (T : Configuration N → B.H N)
    {x : Configuration N} (hx : x ∈ distinctConfigurations N) (d : Configuration N) :
    ‖recursiveLiftFieldDerivative B N T x d‖ ^ 2 = ‖fderiv ℝ T x d‖ ^ 2 +
      ‖(fderiv ℝ (recursiveLiftCandidate B N).operator x d) (T x)‖ ^ 2 := by
  have h := recursiveLiftCandidate_properties B N
  rw [recursiveLiftFieldDerivative, add_comm]
  simpa only [pow_two, h.norm x hx] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _
      (h.flat x hx d (fderiv ℝ T x d) (T x))

/-- Off the collision diagonals the recursive lift satisfies the ordinary
Leibniz rule, obtained from its proved smoothness. -/
theorem recursiveLiftField_hasLineDerivAt
    (B : TensorBackground V) (N : ℕ) {T : Configuration N → B.H N}
    {x : Configuration N} (hx : x ∈ distinctConfigurations N)
    (hT : DifferentiableAt ℝ T x) (d : Configuration N) :
    HasLineDerivAt ℝ (recursiveLiftField B N T)
      (recursiveLiftFieldDerivative B N T x d) x d := by
  have hL := (((recursiveLiftCandidate_properties B N).smooth.contDiffAt
    ((distinctConfigurations_isOpen N).mem_nhds hx)).differentiableAt
      (by simp)).hasFDerivAt
  have happly := ((isBoundedBilinearMap_apply
    (𝕜 := ℂ) (E := B.H N) (F := (recursiveLiftCandidate B N).target)).hasFDerivAt
      ((recursiveLiftCandidate B N).operator x, T x)).restrictScalars ℝ
  have hprod := (happly.comp x (hL.prodMk hT.hasFDerivAt)).hasLineDerivAt d
  change HasLineDerivAt ℝ (recursiveLiftField B N T)
    ((recursiveLiftCandidate B N).operator x (fderiv ℝ T x d) +
      (fderiv ℝ (recursiveLiftCandidate B N).operator x d) (T x)) x d at hprod
  simpa only [recursiveLiftFieldDerivative, add_comm] using hprod

/-- The explicitly constructed lift has the stated distributional coordinate
derivative whenever the input field is differentiable off collisions and the
test products are integrable. No full-space derivative identity is assumed. -/
theorem recursiveLiftField_weak_coordinate_derivative
    (B : TensorBackground V) (N : ℕ) (q : Fin N × Fin 3)
    {T : Configuration N → B.H N}
    (hT : ∀ x ∈ distinctConfigurations N, DifferentiableAt ℝ T x)
    {φ φ' : Configuration N → ℝ}
    (hφ : ∀ x, HasLineDerivAt ℝ φ (φ' x) x (EuclideanSpace.single q 1))
    (hφ'T : Integrable (fun x => φ' x • recursiveLiftField B N T x) volume)
    (hφdT : Integrable (fun x =>
      φ x • recursiveLiftFieldDerivative B N T x (EuclideanSpace.single q 1)) volume)
    (hφT : Integrable (fun x => φ x • recursiveLiftField B N T x) volume) :
    (∫ x, φ x • recursiveLiftFieldDerivative B N T x (EuclideanSpace.single q 1)) =
      -(∫ x, φ' x • recursiveLiftField B N T x) := by
  exact integral_smul_coordinate_derivative_across_collisions q
    (fun x hx => recursiveLiftField_hasLineDerivAt B N hx (hT x hx) _)
    hφ hφ'T hφdT hφT

end GptLean.SymmetricLift
