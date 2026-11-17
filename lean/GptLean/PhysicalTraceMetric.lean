import GptLean.PhysicalNormalTrace
import GptLean.PhotonLocalizationChannelGentle

/-!
The rank-one trace distance estimate follows from the same isometric
normal functional representation used by the concrete physical states.
It is not an additional metric assumption on the physical channel.
-/

noncomputable section
namespace GptLean.PhysicalNormalTrace

open PhotonLocalizationChannel
open scoped InnerProductSpace

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData H T}

omit [CompleteSpace T] in
theorem rankOne_norm_sub_le (F : NormalFunctionalData R) (u v : H) :
    ‖R.rankOne u - R.rankOne v‖ ≤ (‖u‖ + ‖v‖) * ‖u - v‖ := by
  rw [← dist_eq_norm, ← F.isometry.dist_eq, dist_eq_norm]
  apply (F.repr (R.rankOne u) - F.repr (R.rankOne v)).opNorm_le_bound (by positivity)
  intro A
  change ‖F.repr (R.rankOne u) A - F.repr (R.rankOne v) A‖ ≤ _
  rw [F.rankOne, F.rankOne]
  have he : ⟪u, A u⟫_ℂ - ⟪v, A v⟫_ℂ =
      ⟪u - v, A u⟫_ℂ + ⟪v, A (u - v)⟫_ℂ := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  rw [he]
  calc
    ‖⟪u - v, A u⟫_ℂ + ⟪v, A (u - v)⟫_ℂ‖
        ≤ ‖⟪u - v, A u⟫_ℂ‖ + ‖⟪v, A (u - v)⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖u - v‖ * ‖A u‖ + ‖v‖ * ‖A (u - v)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖u - v‖ * (‖A‖ * ‖u‖) + ‖v‖ * (‖A‖ * ‖u - v‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (A.le_opNorm u) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (A.le_opNorm (u - v)) (norm_nonneg _))
    _ = (‖u‖ + ‖v‖) * ‖u - v‖ * ‖A‖ := by ring

omit [CompleteSpace T] in
theorem rankOneMetric (F : NormalFunctionalData R) : RankOneMetric R where
  norm_sub_le := rankOne_norm_sub_le F

end GptLean.PhysicalNormalTrace
