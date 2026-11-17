import GptLean.PhysicalPFSpatialObservables
import GptLean.PhotonLocalizationCurrentPassage

/-! Bounded tests and scalar multiples preserve relative current approximation. -/

noncomputable section

namespace GptLean.PhysicalPFSource

open PhotonLocalizationCurrent RemovalState Filter Topology

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData H T} {Tr : PositiveTraceData T} {E : PositiveForm Tr}

def boundedRelativeApproximation (A : T →L[ℝ] ℝ) :
    RelativeApproximation (R := R) E (boundedObservable A) where
  rate _ := 0
  nonneg _ := le_rfl
  tends_zero := tendsto_const_nhds
  pure_bound _ _ _ _ _ := by simp only [boundedObservable, sub_self, abs_zero, zero_mul, le_refl]

def scaleRelativeApproximation {J : FormObservable E}
    (A : RelativeApproximation (R := R) E J) (r : ℝ) :
    RelativeApproximation (R := R) E (scaleObservable r J) where
  rate n := |r| * A.rate n
  nonneg n := mul_nonneg (abs_nonneg r) (A.nonneg n)
  tends_zero := by simpa only [mul_zero] using A.tends_zero.const_mul |r|
  pure_bound n m hnm v hv := by
    change |r * J.approximation m (R.rankOne v) - r * J.approximation n (R.rankOne v)| ≤ _
    rw [← mul_sub, abs_mul]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (A.pure_bound n m hnm v hv) (abs_nonneg r)

end GptLean.PhysicalPFSource
