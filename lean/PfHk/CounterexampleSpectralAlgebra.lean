import PfHk.CounterexampleSpectralRadial

/-! Scalar series algebra and the elementary norm identity for a scalar
orbital times a constant Hilbert-space vector. These generic lemmas keep
the physical Fock-space implementation out of scalar normalization. -/

noncomputable section
namespace PfHk.CounterexampleSpectral

open MeasureTheory
open scoped InnerProductSpace ENNReal

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

theorem sum_energy_reorder {ι : Type*} (K A C R N : ι → ℝ)
    (hK : Summable K) (hA : Summable A) (hC : Summable C)
    (hR : Summable R) (hN : Summable N) (Z t : ℝ) :
    ((∑' j, (K j + A j)) - Z * (∑' j, C j)) + t * (∑' j, R j) +
      (Z ^ 2 / 2) * (∑' j, N j) =
    ∑' j, (((K j - Z * C j) + (Z ^ 2 / 2) * N j) + (A j + t * R j)) := by
  have hterm (j : ι) :
      ((K j - Z * C j) + (Z ^ 2 / 2) * N j) + (A j + t * R j) =
      ((K j + A j) - Z * C j) + t * R j + (Z ^ 2 / 2) * N j := by ring
  simp_rw [hterm]
  rw [(((hK.add hA).sub (hC.mul_left Z)).add (hR.mul_left t)).tsum_add
    (hN.mul_left (Z ^ 2 / 2)),
    ((hK.add hA).sub (hC.mul_left Z)).tsum_add (hR.mul_left t),
    (hK.add hA).tsum_sub (hC.mul_left Z),
    tsum_mul_left, tsum_mul_left, tsum_mul_left]

theorem lp_norm_eq_norm_coefficient {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α}
    (u : Lp E 2 μ) (f : α → ℝ) (c : E)
    (hf : u =ᵐ[μ] fun x => f x • c) (hnormal : (∫ x, f x ^ 2 ∂μ) = 1) :
    ‖u‖ = ‖c‖ := by
  have hs : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
    calc
      ‖u‖ ^ 2 = inner ℝ u u := (real_inner_self_eq_norm_sq _).symm
      _ = ∫ x, inner ℝ (u x) (u x) ∂μ := L2.inner_def _ _
      _ = ∫ x, ‖u x‖ ^ 2 ∂μ := by simp only [real_inner_self_eq_norm_sq]
  have he : (∫ x, ‖u x‖ ^ 2 ∂μ) = ‖c‖ ^ 2 := by
    calc
      (∫ x, ‖u x‖ ^ 2 ∂μ) = ∫ x, (f x ^ 2) * ‖c‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hf] with x hx
        rw [hx, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      _ = (∫ x, f x ^ 2 ∂μ) * ‖c‖ ^ 2 := integral_mul_const _ _
      _ = ‖c‖ ^ 2 := by rw [hnormal, one_mul]
  nlinarith [norm_nonneg u, norm_nonneg c]

theorem nonnegative_series_term_zero {ι : Type*} (f : ι → ℝ)
    (hf : Summable f) (hn : ∀ i, 0 ≤ f i) (energy a b : ℝ)
    (hs : energy + a * b = ∑' i, f i) (he : energy = -a * b) (i : ι) : f i = 0 := by
  have hz : (∑' i, f i) = 0 := by linarith only [hs, he]
  have hi := hf.le_tsum i (fun j _ => hn j)
  exact le_antisymm (hi.trans_eq hz) (hn i)

end PfHk.CounterexampleSpectral
