import GptLean.SymmetricLift.Configuration
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! Collision diagonals are negligible even after extending a configuration along
one Cartesian coordinate line. An unchanged spatial coordinate separates each
pair outside a finite collection of null hyperplanes. -/

noncomputable section
namespace GptLean.SymmetricLift

open MeasureTheory MeasureTheory.Measure

/-- Equality of one spatial coordinate of two different particles is a null
hyperplane in configuration space. -/
theorem volume_coordinate_collision {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (μ : Fin 3) :
    volume {x : Configuration N | x (i, μ) = x (j, μ)} = 0 := by
  let L : Configuration N →ₗ[ℝ] ℝ :=
    EuclideanSpace.projₗ (i, μ) - EuclideanSpace.projₗ (j, μ)
  have hker : L.ker ≠ ⊤ := by
    intro h
    have hmem : EuclideanSpace.single (i, μ) 1 ∈ L.ker := by
      rw [h]
      trivial
    have hzero : L (EuclideanSpace.single (i, μ) 1) = 0 := hmem
    simp [L, Ne.symm hij] at hzero
  have hnull := addHaar_submodule (volume : Measure (Configuration N)) L.ker hker
  have hset : (L.ker : Set (Configuration N)) =
      {x | x (i, μ) = x (j, μ)} := by
    ext x
    simp [LinearMap.mem_ker, L, sub_eq_zero]
  rwa [hset] at hnull

theorem ae_coordinate_separation {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (μ : Fin 3) :
    ∀ᵐ x : Configuration N ∂volume, x (i, μ) ≠ x (j, μ) := by
  simpa only [ae_iff, not_not] using volume_coordinate_collision hij μ

/-- A single full-measure set separates every distinct particle pair in every
spatial coordinate. This stronger condition is useful for coordinate lines. -/
theorem ae_all_coordinate_separations (N : ℕ) :
    ∀ᵐ x : Configuration N ∂volume,
      ∀ i j : Fin N, i ≠ j → ∀ μ : Fin 3, x (i, μ) ≠ x (j, μ) := by
  simp only [ae_all_iff]
  intro i j hij μ
  exact ae_coordinate_separation hij μ

/-- Almost every configuration has no coincident particles. -/
theorem ae_distinctConfigurations (N : ℕ) :
    ∀ᵐ x : Configuration N ∂volume, x ∈ distinctConfigurations N := by
  filter_upwards [ae_all_coordinate_separations N] with x hx
  intro i j hij
  exact ⟨0, hx i j hij 0⟩

/-- For almost every base point, every coordinate-axis line through that point
misses all collision diagonals. The exceptional set is independent of the line
parameter, so no uncountable intersection of almost-everywhere statements is
needed. -/
theorem ae_coordinate_lines_distinct (N : ℕ) :
    ∀ᵐ x : Configuration N ∂volume, ∀ q : Fin N × Fin 3, ∀ s : ℝ,
      x + s • EuclideanSpace.single q 1 ∈ distinctConfigurations N := by
  filter_upwards [ae_all_coordinate_separations N] with x hx
  intro q s i j hij
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin 3, μ ≠ q.2 := exists_ne q.2
  refine ⟨μ, ?_⟩
  have hi : (i, μ) ≠ q := by
    intro h
    exact hμ (congrArg Prod.snd h)
  have hj : (j, μ) ≠ q := by
    intro h
    exact hμ (congrArg Prod.snd h)
  simpa [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, hi, hj] using hx i j hij μ

theorem ae_coordinate_line_distinct {N : ℕ} (q : Fin N × Fin 3) :
    ∀ᵐ x : Configuration N ∂volume, ∀ s : ℝ,
      x + s • EuclideanSpace.single q 1 ∈ distinctConfigurations N := by
  filter_upwards [ae_coordinate_lines_distinct N] with x hx
  exact hx q

/-- The inverse-square singularity is locally integrable in the three relative
spatial coordinates of a particle pair. -/
theorem locallyIntegrable_inverse_square_norm_three :
    LocallyIntegrable (fun x : EuclideanSpace ℝ (Fin 3) => (‖x‖ ^ 2)⁻¹) volume := by
  refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 2)
    (by norm_num) (by norm_num) ?_ ?_
  · filter_upwards [] with x
    simp
  · exact (continuous_norm.pow 2).measurable.inv.aestronglyMeasurable

end GptLean.SymmetricLift
