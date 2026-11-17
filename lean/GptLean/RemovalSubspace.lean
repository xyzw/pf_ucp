import GptLean.RemovalVacuum

/-!
Closed physical subspaces pass through the actual trace-norm channel and
its Bochner aggregate. For fermions, the compression is conjugation by
the antisymmetric projection. Rank-one compression is ordinary operator
background and every vector's subspace membership is proved separately.
-/

namespace GptLean.RemovalConstruction

open MeasureTheory Filter RemovalState

variable {Q K H T U : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [IsProbabilityMeasure μ]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  {R : Gaussian.RankOneData K T} {Tr : PositiveTraceData T} {E : PositiveForm Tr}

theorem VectorData.output_fixed
    (D : VectorData R Tr E μ) (P : T →L[ℝ] T)
    (hvector : ∀ i, ∀ᵐ q ∂μ, ∀ j, P (R.rankOne (D.vector i j q)) = R.rankOne (D.vector i j q)) :
    P D.output = D.output := by
  have hconditional (i : ℕ) : ∀ᵐ q ∂μ, P (D.conditional i q) = D.conditional i q := by
    filter_upwards [D.mass_sum i, hvector i] with q hmass hq
    have hs := Repair.rankOneSeries_hasSum R hmass
    have hs' := P.hasSum hs
    have hf : (fun j => P (R.rankOne (D.vector i j q))) =
        (fun j => R.rankOne (D.vector i j q)) := funext hq
    rw [hf] at hs'
    exact hs'.unique hs
  have hsum := P.hasSum D.output_hasSum
  have hf : (fun i => P (∫ q, D.conditional i q ∂μ)) =
      (fun i => ∫ q, D.conditional i q ∂μ) := by
    funext i
    rw [← P.integral_comp_comm (D.conditional_integrable i)]
    exact integral_congr_ae (hconditional i)
  rw [hf] at hsum
  exact hsum.unique D.output_hasSum

/-- Membership of every channel vector in the physical Hilbert subspace
implies support of the constructed positive operator on that subspace. -/
theorem VectorData.output_supported
    (D : VectorData R Tr E μ) (S : Submodule ℂ K) (P : T →L[ℝ] T)
    (hcompression : ∀ v ∈ S, P (R.rankOne v) = R.rankOne v)
    (hvector : ∀ i, ∀ᵐ q ∂μ, ∀ j, D.vector i j q ∈ S) : P D.output = D.output :=
  D.output_fixed P (fun i => (hvector i).mono (fun q hq j => hcompression _ (hq j)))

end GptLean.RemovalConstruction
