import PfHk.PauliMagneticField
import PfHk.PauliSpin
import PfHk.FiniteWeightedSource

/-! The actual quantum Zeeman action on the finite electron spin space.
The estimate is derived from the physical magnetic kernels and the exact
Pauli matrix action. It is uniform in all electron positions. -/

noncomputable section
namespace PfHk.PauliMagneticSpin

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel Gaussian PfHk.PhysicalFieldRegularity
  PfHk.PauliSpin

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

attribute [local irreducible] RadialGauge.momentBound radiationGraphDerivative
  radiationGraphInclusion PauliMagneticField.field

variable {N : ℕ}

theorem sigma_sum_norm_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (n : Fin N) (μ : Fin 3) (u : SpinIndex N → H) :
    (∑ s, ‖sigmaFamily n μ u s‖ ^ 2) = ∑ s, ‖u s‖ ^ 2 := by
  have h := fieldFamily_sum_norm_sq n (fun ν => if ν = μ then 1 else 0) u
  simpa [fieldFamily_eq_sum, apply_ite] using h

variable (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
  (C : CanonicalSectorCCR photonMeasure)

def contraction (n : Fin N) (x : FieldSpace) (q : SpinIndex N → RadiationGraphSpace)
    (s : SpinIndex N) : PhotonFock :=
  ∑ μ : Fin 3, sigmaFamily n μ (fun t => PauliMagneticField.field F χ hUV C μ x (q t)) s

theorem contraction_sq_le (n : Fin N) (x : FieldSpace)
    (q : SpinIndex N → RadiationGraphSpace) :
    (∑ s, ‖contraction F χ hUV C n x q s‖ ^ 2) ≤
      180 * (RadialGauge.momentBound F χ hUV) ^ 2 *
        ((∑ s, ‖radiationGraphDerivative (q s)‖ ^ 2) +
          ∑ s, ‖radiationGraphInclusion (q s)‖ ^ 2) := by
  classical
  have hcomponent (s : SpinIndex N) := FiniteWeightedSource.norm_sum_sq
    (Finset.univ : Finset (Fin 3))
    (fun μ => sigmaFamily n μ (fun t => PauliMagneticField.field F χ hUV C μ x (q t)) s)
  have hsum : (∑ s, ‖contraction F χ hUV C n x q s‖ ^ 2) ≤
      3 * ∑ s, ∑ μ : Fin 3,
        ‖sigmaFamily n μ (fun t => PauliMagneticField.field F χ hUV C μ x (q t)) s‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun s _ => by simpa [contraction] using hcomponent s)
  have heq : (∑ s, ∑ μ : Fin 3,
        ‖sigmaFamily n μ (fun t => PauliMagneticField.field F χ hUV C μ x (q t)) s‖ ^ 2) =
      ∑ s, ∑ μ : Fin 3, ‖PauliMagneticField.field F χ hUV C μ x (q s)‖ ^ 2 := by
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun s μ => ‖PauliMagneticField.field F χ hUV C μ x (q s)‖ ^ 2)]
    exact Finset.sum_congr rfl (fun μ _ => sigma_sum_norm_sq n μ _)
  rw [heq] at hsum
  have hb := mul_le_mul_of_nonneg_left
    (PauliMagneticField.finite_sum_field_sq_le F χ hUV C x q) (by norm_num : (0 : ℝ) ≤ 3)
  exact hsum.trans (hb.trans_eq (by ring))

/-- The complete quantum Zeeman multiplication on spin configurations. -/
def quantum (e : ℝ) (x : Fin N → FieldSpace)
    (q : SpinIndex N → RadiationGraphSpace) (s : SpinIndex N) : PhotonFock :=
  ((-e / 2 : ℝ) : ℂ) • ∑ n, contraction F χ hUV C n (x n) q s

theorem quantum_sq_le (e : ℝ) (x : Fin N → FieldSpace)
    (q : SpinIndex N → RadiationGraphSpace) :
    (∑ s, ‖quantum F χ hUV C e x q s‖ ^ 2) ≤
      (45 * e ^ 2 * (N : ℝ) ^ 2 * (RadialGauge.momentBound F χ hUV) ^ 2) *
        ((∑ s, ‖radiationGraphDerivative (q s)‖ ^ 2) +
          ∑ s, ‖radiationGraphInclusion (q s)‖ ^ 2) := by
  classical
  let energy := (∑ s, ‖radiationGraphDerivative (q s)‖ ^ 2) +
    ∑ s, ‖radiationGraphInclusion (q s)‖ ^ 2
  have hn (s : SpinIndex N) := FiniteWeightedSource.norm_sum_sq
    (Finset.univ : Finset (Fin N)) (fun n => contraction F χ hUV C n (x n) q s)
  have hs : (∑ s, ‖∑ n, contraction F χ hUV C n (x n) q s‖ ^ 2) ≤
      (N : ℝ) ^ 2 * 180 * (RadialGauge.momentBound F χ hUV) ^ 2 * energy := by
    calc
      _ ≤ (N : ℝ) * ∑ s, ∑ n, ‖contraction F χ hUV C n (x n) q s‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun s _ => by simpa using hn s)
      _ = (N : ℝ) * ∑ n, ∑ s, ‖contraction F χ hUV C n (x n) q s‖ ^ 2 := by
        rw [Finset.sum_comm]
      _ ≤ (N : ℝ) * ∑ _n : Fin N,
          180 * (RadialGauge.momentBound F χ hUV) ^ 2 * energy := by
        gcongr with n
        exact contraction_sq_le F χ hUV C n (x n) q
      _ = _ := by simp [energy]; ring
  have hscale := mul_le_mul_of_nonneg_left hs (sq_nonneg (-e / 2))
  calc
    _ = (-e / 2) ^ 2 * ∑ s, ‖∑ n, contraction F χ hUV C n (x n) q s‖ ^ 2 := by
      simp only [quantum, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        mul_pow, sq_abs, Finset.mul_sum]
    _ ≤ _ := hscale.trans_eq (by dsimp [energy]; ring)

end PfHk.PauliMagneticSpin
