import GptLean.RemovalPFLocalization
import GptLean.RemovalSourceLatticeRepresentatives

/-! The physical reference data of the actual lattice-localized WIS source
are derived from the original source's reference data and the universal
spatial scalar action of the ordinary WIS unitaries. -/

noncomputable section

set_option maxHeartbeats 800000

namespace GptLean.RemovalSource.LatticeSourceData

open MeasureTheory GptLean.Repair GptLean.SymmetricLift GptLean.RemovalEnergy

variable {Q H K Hr Kr Hs : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [IsProbabilityMeasure μ] {N : ℕ}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup Kr] [InnerProductSpace ℂ Kr]
  [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

/-- No localized graph or weak-derivative assumption remains. The input
`P₀` concerns the original, unlocalized WIS reference decomposition. -/
def localizedPFData (D : LatticeSourceData N μ H K Hr Kr Hs)
    (R : ℝ) (hR : 0 < R)
    (hU : SpatialScalarIntertwining D.U) (hUr : SpatialScalarIntertwining D.Ur)
    (rad : K →ₗ.[ℂ] K) (hard : (Fin N × Fin 3) → Configuration N → K →ₗ.[ℂ] K)
    (rest : Configuration N → K →ₗ.[ℂ] Kr) (e : ℝ)
    (soft : (Fin N × Fin 3) → Q × Configuration N → ℝ)
    (P₀ : D.original.PFData rad hard rest e (fun _ => soft)) :
    (D.conditioned R hR).PFData rad hard rest e (fun _ => soft) := by
  apply ConditionedSource.PFData.localize P₀
    (fun n => (Nat.unpair n).1) (fun n => latticeMultiplier R (Nat.unpair n).2)
    (fun n j x => fderiv ℝ (latticeMultiplier R (Nat.unpair n).2) x (EuclideanSpace.single j 1))
    (fun n => weakH1Local_of_differentiable_bounded
      (latticeMultiplier_differentiable R (Nat.unpair n).2)
      (Real.sqrt (LatticePartition.metricConstant / R ^ 2))
      (fun j x => by simpa only [Real.norm_eq_abs] using
        latticeMultiplier_derivative_bound R hR (Nat.unpair n).2 j x))
    (fun _ => 1) (fun _ => Real.sqrt (LatticePartition.metricConstant / R ^ 2))
  · intro n x
    exact partition_abs_le_one (latticeMultiplier R) (latticeMultiplier_partition R)
      (Nat.unpair n).2 x
  · intro n j x
    exact latticeMultiplier_derivative_bound R hR (Nat.unpair n).2 j x
  · intro n
    exact D.source_eq_mul R hR
      (hU.localized_commute (latticeMultiplier R) (latticeMultiplier_partition R)
        (latticeMultiplier_measurable R)) n
  · intro n j
    exact D.covariant_eq_mul R hR hU n j
  · intro n
    exact D.rest_eq_mul R hR
      (hUr.localized_commute (latticeMultiplier R) (latticeMultiplier_partition R)
        (latticeMultiplier_measurable R)) n

end GptLean.RemovalSource.LatticeSourceData
