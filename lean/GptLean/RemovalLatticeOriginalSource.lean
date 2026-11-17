import GptLean.RemovalOriginalSource
import GptLean.RemovalSourceLattice

/-! The original-source interface instantiated by the actual lattice
partition. Localization assumptions are all proved by the construction. -/

noncomputable section

namespace GptLean.RemovalSource.LatticeSourceData

open MeasureTheory SymmetricLift

variable {N : ℕ} {Q H K Hr Kr Hs : Type*} [MeasurableSpace Q] {μ : Measure Q} [SFinite μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup Kr] [InnerProductSpace ℂ Kr]
  [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  (D : LatticeSourceData N μ H K Hr Kr Hs)

def toOriginalSource (R : ℝ) (hR : 0 < R) :
    OriginalSource μ (volume : Measure (Configuration N)) (Fin N × Fin 3) H K Hr Kr Hs where
  wis := D.U
  wisRest := D.Ur
  cutoff := latticeMultiplier R
  locallyFinite := latticeMultiplier_locallyFinite R
  differentiable := latticeMultiplier_differentiable R
  nonneg := latticeMultiplier_nonneg R
  partition := latticeMultiplier_partition R
  measurable := latticeMultiplier_measurable R
  vector := D.ψ
  covariant := D.dψ
  rest := D.rest
  soft := D.soft
  direction j := EuclideanSpace.single j 1
  derivative_measurable := latticeMultiplier_derivative_measurable R
  metric _ := LatticePartition.metricConstant / R ^ 2
  metric_bound := latticeMultiplier_coordinate_metric R hR
  normalized := D.mass
  kinetic_summable := D.kinetic_summable
  rest_summable := D.rest_summable
  soft_summable := D.soft_summable

@[simp] theorem toOriginalSource_conditioned (R : ℝ) (hR : 0 < R) :
    (D.toOriginalSource R hR).conditionedSource = D.conditioned R hR := rfl

@[simp] theorem toOriginalSource_energy (R : ℝ) (hR : 0 < R) :
    (D.toOriginalSource R hR).energy = D.inputEnergy := rfl

theorem toOriginalSource_metric_sum (R : ℝ) (hR : 0 < R) :
    (1 / 2 : ℝ) * ∑ j, (D.toOriginalSource R hR).metric j = latticeIMSConstant N / R ^ 2 := by
  change (1 / 2 : ℝ) * ∑ _j : Fin N × Fin 3, LatticePartition.metricConstant / R ^ 2 = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, latticeIMSConstant]
  ring

end GptLean.RemovalSource.LatticeSourceData
