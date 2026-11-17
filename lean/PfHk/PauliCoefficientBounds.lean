import PfHk.PauliFormBounds
import PfHk.PhysicalCommonFormDomain
import PfHk.ScalarPotentialSmallForm
import PfHk.PhysicalDiamagneticPotential

/-! The ordinary Sobolev bounds needed by the Pauli form follow from
the actual global coefficient classes. Repulsive Coulomb interactions
contribute to the positive scalar amplitude and require no smallness. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.PauliCoefficientBounds

open MeasureTheory GptLean GptLean.PhysicalPairDuality
open GptLean.PhysicalSourceCoordinates PfHk.CoordinateSobolev
open PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

variable {N : ℕ}

attribute [local irreducible] GptLean.PhysicalPFReference.referenceSubspace
  GptLean.PhysicalPFReference.inclusion

private theorem vector_square_in_sum (A : VectorPotential) :
    ∃ p : ScalarPotential, (fun x => ‖A.val x‖ ^ 2) =ᵐ[volume] (p.val : Position → ℝ) := by
  refine ⟨PhysicalDiamagneticPotential.halfSquare A + PhysicalDiamagneticPotential.halfSquare A, ?_⟩
  filter_upwards [TransformationsPotentials.coeFn_sum_add
    (PhysicalDiamagneticPotential.halfSquare A) (PhysicalDiamagneticPotential.halfSquare A),
    PhysicalDiamagneticPotential.coeFn_halfSquare A] with x hsum hsq
  rw [hsum, hsq]
  ring

private theorem vector_sq_le (A : VectorPotential) (q : Fin N × Fin 3) (X : Configuration N) :
    vector A q X ^ 2 ≤ ∑ n : Fin N,
      |coordinateCoefficient n (fun x => ‖A.val x‖ ^ 2) X| := by
  have hcoord : vector A q X ^ 2 ≤ ‖A.val (split q.1 X).1‖ ^ 2 := by
    change A.val (split q.1 X).1 q.2 ^ 2 ≤ _
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ q.2)
  have hsum : ‖A.val (split q.1 X).1‖ ^ 2 ≤
      ∑ n : Fin N, |coordinateCoefficient n (fun x => ‖A.val x‖ ^ 2) X| := by
    have h := Finset.single_le_sum
      (s := Finset.univ) (f := fun n : Fin N =>
        |coordinateCoefficient n (fun x => ‖A.val x‖ ^ 2) X|)
      (fun n _ => abs_nonneg _) (Finset.mem_univ q.1)
    simpa only [coordinateCoefficient, abs_pow, abs_norm] using h
  exact hcoord.trans hsum

theorem vector_measurable (A : VectorPotential) (q : Fin N × Fin 3) :
    AEStronglyMeasurable (vector A q) volume :=
  coordinateCoefficient_measurable q.1
    ((EuclideanSpace.proj q.2 : PhysicalPairSpace.Vector →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
      A.val.aestronglyMeasurable)

/-- One constant controls every electronic coordinate at any positive
ordinary kinetic coefficient. -/
theorem vector_small_form (A : VectorPotential) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Fin N × Fin 3, ScalarMultiplierBound (vector A q) ε C := by
  classical
  have hex : ∀ q : Fin N × Fin 3, ∃ C : ℝ, 0 ≤ C ∧
      ScalarMultiplierBound (vector A q) ε C := by
    intro q
    exact ScalarPotentialSmallForm.negative_bound_of_scalarPotential
      (fun _ : Fin N => fun x => ‖A.val x‖ ^ 2)
      (fun _ => vector_square_in_sum A) (vector A q) (vector_measurable A q)
      (Filter.Eventually.of_forall (vector_sq_le A q)) hε
  choose C hC hb using hex
  refine ⟨∑ q, C q, Finset.sum_nonneg (fun q _ => hC q), ?_⟩
  intro q f g hfg hf hg
  apply (hb q f g hfg hf hg).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun q _ => hC q) (Finset.mem_univ q))
    (integral_nonneg (fun _ => sq_nonneg _)))

theorem negative_measurable (v : ScalarPotential) (c : ℝ) :
    AEStronglyMeasurable (negative (N := N) v c) volume :=
  (Real.continuous_sqrt.comp (continuous_id.max continuous_const)).comp_aestronglyMeasurable
    (scalar_measurable v c).neg

theorem negative_sq_le (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c) (X : Configuration N) :
    negative v c X ^ 2 ≤ ∑ n : Fin N, |coordinateCoefficient n (v.val : Position → ℝ) X| := by
  rw [negative, SignedScalarMultiplier.negativeAmplitude_sq]
  apply max_le
  · have h := neg_le_abs (∑ n : Fin N, coordinateCoefficient n (v.val : Position → ℝ) X)
    have hs := Finset.abs_sum_le_sum_abs (s := Finset.univ)
      (f := fun n : Fin N => coordinateCoefficient n (v.val : Position → ℝ) X)
    have hp := mul_nonneg hc (PhysicalCoulombH1.potential_nonneg N X)
    change -((∑ n : Fin N, coordinateCoefficient n (v.val : Position → ℝ) X) +
      c * PhysicalCoulombH1.potential N X) ≤ _
    linarith only [h, hs, hp]
  · exact Finset.sum_nonneg fun n _ => abs_nonneg _

/-- The negative form bound has arbitrarily small ordinary kinetic
coefficient for every nonnegative Coulomb coupling. -/
theorem negative_small_form (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ScalarMultiplierBound (negative (N := N) v c) ε C :=
  ScalarPotentialSmallForm.negative_bound_of_scalarPotential
    (fun _ : Fin N => (v.val : Position → ℝ)) (fun _ => ⟨v, Filter.EventuallyEq.rfl⟩)
    (negative v c) (negative_measurable v c)
    (Filter.Eventually.of_forall (negative_sq_le v c hc)) hε

theorem domain (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (u : PauliGroundState.Ref N) :
    PauliGroundState.Domain (vector A) (positive v c) (negative v c) u :=
  fun s => externalDomain A v c hc (u s)

end PfHk.PauliCoefficientBounds
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
