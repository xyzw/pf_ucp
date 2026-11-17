import GptLean.Repair.LocalCost
import GptLean.RemovalGeometry

/-!
The gauge phase and residual current repair act on the same source vector.
The identities below remove the constant measured cluster field exactly
before estimating the residual lift metric. In particular the kinetic
remainder has no term proportional to the size of the constant field.
-/

namespace GptLean.RemovalEnergy

open GptLean.Repair
open scoped ComplexConjugate

variable {J H V : Type*} [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

noncomputable def phaseFactor (φ : ℝ) : ℂ := Complex.exp ((φ : ℂ) * Complex.I)

theorem phaseFactor_norm (φ : ℝ) : ‖phaseFactor φ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I φ

def phasedValue (w : ℂ) (ψ : H) : H := w • ψ

def phasedDerivative (w : ℂ) (p : ℝ) (u ψ : H) : H :=
  w • (u + (p : ℂ) • ψ)

/-- The phase and residual velocity combine before the norm is estimated. -/
theorem phased_shifted_derivative (w : ℂ) (p s : ℝ) (u ψ : H) :
    phasedDerivative w p u ψ + (s : ℂ) • phasedValue w ψ =
      w • (u + ((p + s : ℝ) : ℂ) • ψ) := by
  simp only [phasedDerivative, phasedValue, smul_add, smul_smul,
    Complex.ofReal_add, add_smul]
  module

theorem phased_mass (w : ℂ) (hw : ‖w‖ = 1) (ψ : H) :
    ‖phasedValue w ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  simp [phasedValue, norm_smul, hw]

theorem phased_inner (w : ℂ) (hw : ‖w‖ = 1) (ψ u : H) :
    inner ℂ (w • ψ) (w • u) = inner ℂ ψ u := by
  have hw' : conj w * w = 1 := by rw [Complex.conj_mul', hw]; norm_num
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, hw', one_mul]

/-- The shifted source energy is exactly the conditioned soft-field kinetic
energy when the phase gradient and residual sum to the removed field. -/
theorem phased_source_kinetic (w : ℂ) (hw : ‖w‖ = 1)
    (p s field : J → ℝ) (e : ℝ) (u : J → H) (ψ : H)
    (hcancel : ∀ j, p j + s j = -e * field j) :
    localShiftedKinetic (fun j => phasedDerivative w (p j) (u j) ψ)
      (phasedValue w ψ) s =
      1 / 2 * ∑ j, ‖u j - ((e * field j : ℝ) : ℂ) • ψ‖ ^ 2 := by
  unfold localShiftedKinetic
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [phased_shifted_derivative, norm_smul, hw, one_mul, hcancel]
  simp only [neg_mul, Complex.ofReal_neg, neg_smul, sub_eq_add_neg]

/-- Local current cancellation on the actual coordinate channel. The
source can have arbitrary spin or hard-photon fibre dimension. -/
theorem phased_channel_current (basis : HilbertBasis ℕ ℂ V)
    {z dz : V} {s : ℝ} (hz : ‖z‖ = 1)
    (hconn : inner ℂ z dz = Complex.I * s)
    (w : ℂ) (hw : ‖w‖ = 1) (p field e : ℝ)
    (hcancel : p + s = -e * field) (u ψ : H) :
    HasSum (fun a => inner ℂ (coordinate basis z a • phasedValue w ψ)
      (coordinate basis z a • phasedDerivative w p u ψ -
        Complex.I • coordinate basis dz a • phasedValue w ψ))
      (inner ℂ ψ (u - ((e * field : ℝ) : ℂ) • ψ)) := by
  have hs := coordinate_channel_current basis hz hconn
    (phasedDerivative w p u ψ) (phasedValue w ψ)
  convert hs using 1
  have hnorm : ‖phasedValue w ψ‖ = ‖ψ‖ := by simp [phasedValue, norm_smul, hw]
  rw [hnorm]
  change inner ℂ ψ (u - ((e * field : ℝ) : ℂ) • ψ) =
    inner ℂ (w • ψ) (w • (u + (p : ℂ) • ψ)) + (s : ℂ) * (‖ψ‖ : ℂ) ^ 2
  rw [phased_inner w hw]
  simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
  have hc : (p : ℂ) + (s : ℂ) = -((e * field : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add, hcancel]
    simp
  linear_combination -hc * (‖ψ‖ : ℂ) ^ 2

/-- The exact conditioned kinetic energy controls the repaired channel
with only the residual tensor metric as additional cost. -/
theorem phased_channel_kinetic_le (basis : HilbertBasis ℕ ℂ V)
    {z : V} (dz : J → V) (s : J → ℝ)
    (hz : ‖z‖ = 1) (hconn : ∀ j, inner ℂ z (dz j) = Complex.I * s j)
    (w : ℂ) (hw : ‖w‖ = 1) (p field : J → ℝ) (e : ℝ)
    (hcancel : ∀ j, p j + s j = -e * field j)
    (u : J → H) (ψ : H) {M : ℝ} (hmetric : ∑ j, ‖dz j‖ ^ 2 ≤ M) :
    localChannelKinetic basis z dz
      (fun j => phasedDerivative w (p j) (u j) ψ) (phasedValue w ψ) ≤
      1 / 2 * ∑ j, ‖u j - ((e * field j : ℝ) : ℂ) • ψ‖ ^ 2 +
        1 / 2 * M * ‖ψ‖ ^ 2 := by
  have h := localChannelKinetic_le_shifted basis dz s hz hconn
    (fun j => phasedDerivative w (p j) (u j) ψ) (phasedValue w ψ) hmetric
  rwa [phased_source_kinetic w hw p s field e u ψ hcancel, phased_mass w hw] at h

end GptLean.RemovalEnergy
