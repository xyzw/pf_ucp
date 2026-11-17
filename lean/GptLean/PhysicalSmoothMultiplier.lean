import GptLean.ElectronicH1Multiplier
import GptLean.PhysicalPairSmoothTests
import GptLean.PhysicalSourceCoordinates

/-! Smooth spatial pair tests give bounded differentiable configuration multipliers. -/

noncomputable section

namespace GptLean.PhysicalPairSpace.SmoothSpatialTest

open ElectronicH1Multiplier PhysicalSourceCoordinates
open scoped ContDiff

variable (t : SmoothSpatialTest)

theorem exists_derivative_bound : ∃ c : ℝ, 0 ≤ c ∧ ∀ x, ‖fderiv ℝ t.weight x‖ ≤ c := by
  obtain ⟨c, hc⟩ := (t.smooth.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (t.compact.fderiv ℝ)
  exact ⟨c, (norm_nonneg _).trans (hc 0), hc⟩

def derivativeBound : ℝ := Classical.choose t.exists_derivative_bound

theorem derivativeBound_nonneg : 0 ≤ t.derivativeBound :=
  (Classical.choose_spec t.exists_derivative_bound).1

theorem derivative_norm_le (x : Position) : ‖fderiv ℝ t.weight x‖ ≤ t.derivativeBound :=
  (Classical.choose_spec t.exists_derivative_bound).2 x

def pullback {I : Type*} [Fintype I] [DecidableEq I]
    (L : EuclideanSpace ℝ I →L[ℝ] Position) : SmoothMultiplier I where
  weight := fun x => t.weight (L x)
  smooth := t.smooth.comp L.contDiff
  bound := 1
  bounded x := by simpa only [Real.norm_eq_abs] using t.bounded (L x)
  derivativeBound := t.derivativeBound * ‖L‖
  derivative_bounded i x := by
    have hd := ((t.smooth.differentiable (by simp)) (L x)).hasFDerivAt.comp x L.hasFDerivAt
    change |fderiv ℝ (t.weight ∘ L) x (EuclideanSpace.single i 1)| ≤ _
    rw [hd.fderiv]
    change ‖fderiv ℝ t.weight (L x) (L (EuclideanSpace.single i 1))‖ ≤ _
    exact ((fderiv ℝ t.weight (L x)).le_of_opNorm_le (t.derivative_norm_le (L x)) _).trans
      ((mul_le_mul_of_nonneg_left (L.le_opNorm _) t.derivativeBound_nonneg).trans_eq
        (by simp only [PiLp.norm_single, norm_one, mul_one]))

def configuration {N : ℕ} (i : Fin N) : SmoothMultiplier (Fin N × Fin 3) :=
  t.pullback ((ContinuousLinearMap.fst ℝ Position (Spectator i)).comp
    (split i).toContinuousLinearMap)

theorem configuration_weight {N : ℕ} (i : Fin N) (x : Configuration N) :
    (t.configuration i).weight x = t.weight ((split i) x).1 := rfl

end GptLean.PhysicalPairSpace.SmoothSpatialTest
