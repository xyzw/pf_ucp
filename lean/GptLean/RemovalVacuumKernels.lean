import GptLean.RemovalVacuumForm
import GptLean.Gaussian.FieldMoments
import GptLean.SymmetricLift.PairEnergyIntegrability

/-! The vacuum variance used in the same-state preparation is computed
from the actual three soft Fourier kernels and summed over the particles. -/

noncomputable section

namespace GptLean.Gaussian.KernelFieldData

open MeasureTheory SymmetricLift

variable {Q H K G Ω : Type*} [MeasurableSpace Q] [MeasurableSpace Ω]
  {μ : Measure Q} {ν : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  {W : WienerSegalData Q H K G μ} {w : Ω → ℝ} (D : KernelFieldData ν W w)

theorem many_particle_vacuum_variance
    (N : ℕ) (momentum : Ω → FieldSpace) (k : ℝ) (base : Fin 3 → Ω → ℂ)
    (label : Fin 3 → FieldSpace → G)
    (hkernel : ∀ i x, D.kernel (label i x) = softDerivativeKernel momentum [] k x (base i))
    (hA : ∀ i, Integrable (fun y => w y * ‖softBase momentum k (base i) y‖ ^ 2) ν)
    (hB : ∀ i, Integrable (fun y => ‖softBase momentum k (base i) y‖ ^ 2) ν)
    (Ω₀ : H) (hΩ : ‖Ω₀‖ = 1) (hrad : D.radiationDomain Ω₀) (hzero : D.radiation Ω₀ = 0)
    (x : Configuration N) :
    (∑ j : Fin N × Fin 3, ‖W.field (label j.2 (particle x j.1)) Ω₀‖ ^ 2) =
      N * ∑ i : Fin 3, ∫ y, ‖softBase momentum k (base i) y‖ ^ 2 ∂ν := by
  simp_rw [D.vacuum_soft_field_variance momentum k _ _ (hkernel _) (hA _) (hB _) Ω₀ hΩ hrad hzero]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

theorem many_particle_vacuum_variance_le
    (N : ℕ) (momentum : Ω → FieldSpace) (k b : ℝ) (base : Fin 3 → Ω → ℂ)
    (hcut : ∀ i, (∫ y, ‖softBase momentum k (base i) y‖ ^ 2 ∂ν) ≤ b ^ 2) :
    (N : ℝ) * (∑ i : Fin 3, ∫ y, ‖softBase momentum k (base i) y‖ ^ 2 ∂ν) ≤
      2 * (3 * (N : ℝ) / 2) * b ^ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcut i)
  have hb := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  calc
    _ ≤ (N : ℝ) * (3 * b ^ 2) := by simpa only [Nat.cast_ofNat] using hb
    _ = _ := by ring

end GptLean.Gaussian.KernelFieldData
