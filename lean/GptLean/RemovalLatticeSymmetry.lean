import GptLean.RemovalClusterSymmetry
import GptLean.RemovalSourceLatticeRepresentatives

/-! Original source antisymmetry passes to the actual localized WIS
vectors. Together with the concrete cluster channel theorem, this keeps
all output vectors in the electronic character subspace. -/

noncomputable section

set_option maxHeartbeats 800000

namespace GptLean.RemovalSource.LatticeSourceData

open MeasureTheory MeasureTheory.Measure Filter GptLean.Repair GptLean.SymmetricLift

variable {Q H K Hr Kr Hs : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [SFinite μ] {N : ℕ}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup Kr] [InnerProductSpace ℂ Kr]
  [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

theorem conditioned_source_character
    (D : LatticeSourceData N μ H K Hr Kr Hs) (R : ℝ) (hR : 0 < R)
    (hU : SpatialScalarIntertwining D.U) (χ : Equiv.Perm (Fin N) → ℂ)
    (hχ : ∀ n, ∀ᵐ q ∂μ, HasElectronicCharacter (fun π => permuteConfiguration π) χ
      (fun x => D.original.source n (q,x))) :
    ∀ n, ∀ᵐ q ∂μ, HasElectronicCharacter (fun π => permuteConfiguration π) χ
      (fun x => (D.conditioned R hR).source n (q,x)) := by
  intro n
  have hs := D.source_eq_mul R hR
    (hU.localized_commute (latticeMultiplier R) (latticeMultiplier_partition R)
      (latticeMultiplier_measurable R)) n
  filter_upwards [ae_ae_of_ae_prod hs, hχ (Nat.unpair n).1] with q hsq hχq
  intro π
  have hpre := (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae hsq
  filter_upwards [hsq, hpre, hχq π] with x hx hπx hχx
  rw [hx, hπx, latticeMultiplier_permute]
  change (latticeMultiplier R (Nat.unpair n).2 x : ℂ) •
      D.original.source (Nat.unpair n).1 (q,permuteConfiguration π x) = _
  rw [hχx, smul_comm]
  rfl

end GptLean.RemovalSource.LatticeSourceData
