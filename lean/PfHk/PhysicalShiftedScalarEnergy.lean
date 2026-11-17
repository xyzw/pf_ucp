import PfHk.PhysicalShiftedFormEnergyBase

/-! The diamagnetic scalar shift is integrated against the actual
configuration density. Its integral algebra is carried out for real
functions before inserting the reference vector. -/

noncomputable section
namespace PfHk.PhysicalShiftedFormEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality PfHk.PhysicalCommonFormDomain

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

attribute [local irreducible] inclusion PhysicalPFReference.referenceSubspace

private theorem integral_add_sum {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : Measure α) (f : α → ℝ) (g : β → α → ℝ) (c : ℝ)
    (hf : Integrable f μ) (hg : ∀ b, Integrable (g b) μ) :
    (∫ x, f x + c * ∑ b, g b x ∂μ) =
      (∫ x, f x ∂μ) + c * ∑ b, ∫ x, g b x ∂μ := by
  rw [integral_add hf ((integrable_finsetSum _ (fun b _ => hg b)).const_mul c),
    integral_const_mul, integral_finsetSum _ (fun b _ => hg b)]

variable {N : ℕ}

private theorem scalar_shift_sum (A : VectorPotential) (v w : ScalarPotential)
    (hshift : (w.val : PhysicalSourceCoordinates.Position → ℝ) =ᵐ[volume]
      fun x => v.val x + (1 / 2 : ℝ) * ∑ b : Fin 3, A.val x b ^ 2)
    (ρ : PhysicalSourceCoordinates.Configuration N → ℝ)
    (hv : ∀ n : Fin N, Integrable
      (fun X : PhysicalSourceCoordinates.Configuration N =>
        CoordinateSobolev.coordinateCoefficient (N := N) n
          (v.val : PhysicalSourceCoordinates.Position → ℝ) X * ρ X) volume)
    (hA : ∀ q : Fin N × Fin 3, Integrable
      (fun X : PhysicalSourceCoordinates.Configuration N =>
        vector (N := N) A q X ^ 2 * ρ X) volume) :
    (∑ n : Fin N, ∫ X : PhysicalSourceCoordinates.Configuration N,
      CoordinateSobolev.coordinateCoefficient (N := N) n
        (w.val : PhysicalSourceCoordinates.Position → ℝ) X * ρ X) =
      (∑ n : Fin N, ∫ X : PhysicalSourceCoordinates.Configuration N,
        CoordinateSobolev.coordinateCoefficient (N := N) n
          (v.val : PhysicalSourceCoordinates.Position → ℝ) X * ρ X) +
      (1 / 2 : ℝ) * ∑ q : Fin N × Fin 3,
        ∫ X : PhysicalSourceCoordinates.Configuration N, vector (N := N) A q X ^ 2 * ρ X := by
  have hrow (n : Fin N) :
      (∫ X : PhysicalSourceCoordinates.Configuration N,
        CoordinateSobolev.coordinateCoefficient (N := N) n
          (w.val : PhysicalSourceCoordinates.Position → ℝ) X * ρ X) =
      (∫ X : PhysicalSourceCoordinates.Configuration N,
        CoordinateSobolev.coordinateCoefficient (N := N) n
          (v.val : PhysicalSourceCoordinates.Position → ℝ) X * ρ X) +
      (1 / 2 : ℝ) * ∑ b : Fin 3,
        ∫ X : PhysicalSourceCoordinates.Configuration N,
          vector (N := N) A (n, b) X ^ 2 * ρ X := by
    have he :
        (fun X : PhysicalSourceCoordinates.Configuration N =>
          CoordinateSobolev.coordinateCoefficient (N := N) n
            (w.val : PhysicalSourceCoordinates.Position → ℝ) X * ρ X) =ᵐ[volume]
        fun X : PhysicalSourceCoordinates.Configuration N =>
          CoordinateSobolev.coordinateCoefficient (N := N) n
            (v.val : PhysicalSourceCoordinates.Position → ℝ) X * ρ X +
          (1 / 2 : ℝ) * ∑ b : Fin 3, vector (N := N) A (n, b) X ^ 2 * ρ X := by
      filter_upwards [ScalarCoordinateFormBound.coordinate_ae (N := N) n hshift] with X hX
      change w.val (PhysicalSourceCoordinates.split n X).1 = _ at hX
      change w.val (PhysicalSourceCoordinates.split n X).1 * ρ X = _
      exact (congrArg (fun r : ℝ => r * ρ X) hX).trans (by
        simp only [add_mul, mul_assoc, Finset.sum_mul]
        rfl)
    exact (integral_congr_ae he).trans
      (integral_add_sum volume
        (fun X : PhysicalSourceCoordinates.Configuration N =>
          CoordinateSobolev.coordinateCoefficient (N := N) n
            (v.val : PhysicalSourceCoordinates.Position → ℝ) X * ρ X)
        (fun b : Fin 3 => fun X : PhysicalSourceCoordinates.Configuration N =>
          vector (N := N) A (n, b) X ^ 2 * ρ X)
        (1 / 2 : ℝ) (hv n) (fun b => hA (n, b)))
  refine (Finset.sum_congr rfl (fun n _ => hrow n)).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact congrArg (fun r : ℝ =>
    (∑ n : Fin N, ∫ X : PhysicalSourceCoordinates.Configuration N,
      CoordinateSobolev.coordinateCoefficient (N := N) n
        (v.val : PhysicalSourceCoordinates.Position → ℝ) X * ρ X) + (1 / 2 : ℝ) * r)
    (Fintype.sum_prod_type (fun q : Fin N × Fin 3 =>
      ∫ X : PhysicalSourceCoordinates.Configuration N, vector (N := N) A q X ^ 2 * ρ X)).symm

theorem scalarSum_shift (A : VectorPotential) (v w : ScalarPotential)
    (hshift : (w.val : PhysicalSourceCoordinates.Position → ℝ) =ᵐ[volume]
      fun x => v.val x + (1 / 2 : ℝ) * ∑ b : Fin 3, A.val x b ^ 2)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    scalarSum (N := N) w u =
      scalarSum (N := N) v u + (1 / 2 : ℝ) * squareSum (N := N) A u :=
  scalar_shift_sum (N := N) A v w hshift
    (fun X : PhysicalSourceCoordinates.Configuration N =>
      ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2)
    (fun n => scalar_integrable (N := N) v n u)
    (fun q => square_integrable (N := N) A q u)

end PfHk.PhysicalShiftedFormEnergy
