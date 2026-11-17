import PfHk.UniqueContinuation

noncomputable section
namespace PfHk.UniqueContinuation

open Filter
open scoped Topology

set_option maxHeartbeats 20000
set_option Elab.async false

/-- The scalar domination used after the physical annular commutator
estimate. Both decay hypotheses concern the actual local mass functions
when this lemma is specialized. -/
theorem tendsto_zero_of_inner_bound {U K error : ℝ → ℝ} {α τ G L R : ℝ}
    (hU : ∀ r, 0 < r → 0 ≤ U r) (hK : ∀ r, 0 < r → 0 ≤ K r)
    (hUf : InfiniteOrder.FlatAtZero U) (hKf : InfiniteOrder.FlatAtZero K)
    (hα : 0 ≤ α) (hτ : 0 ≤ τ) (hR : 0 < R)
    (herror : ∀ r, 0 ≤ error r)
    (hbound : ∀ r, 0 < r → r ≤ R → error r ≤
      Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log r)) *
        (8 * G * K (2 * r) + 2 * L / r ^ 2 * U (2 * r))) :
    Tendsto error (𝓝[>] 0) (𝓝 0) := by
  let C := max (8 * G) (2 * L)
  have hlim := (inner_error_tendsto hU hK hUf hKf hα hτ).const_mul C
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall herror) _ hlim
  have hrpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  have hrsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r ≤ R :=
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds |>.mono fun _ h => h.le
  filter_upwards [hrpos, hrsmall] with r hr hrs
  apply (hbound r hr hrs).trans
  have hu0 := hU (2 * r) (by linarith)
  have hk0 := hK (2 * r) (by linarith)
  have hcg : 8 * G ≤ C := le_max_left _ _
  have hcl : 2 * L ≤ C := le_max_right _ _
  rw [Real.rpow_neg hr.le, Real.rpow_two]
  have hc : 8 * G * K (2 * r) + 2 * L / r ^ 2 * U (2 * r) ≤
      C * (r ^ 2)⁻¹ * U (2 * r) + C * K (2 * r) := by
    have hk' := mul_le_mul_of_nonneg_right hcg hk0
    have hu' := mul_le_mul_of_nonneg_right hcl
      (mul_nonneg (inv_nonneg.mpr (sq_nonneg r)) hu0)
    simpa only [div_eq_mul_inv, mul_assoc, add_comm] using add_le_add hu' hk'
  have he := mul_le_mul_of_nonneg_left hc
    (Real.exp_pos (2 * τ * CarlemanWeights.weight α (-Real.log r))).le
  convert he using 1 <;> ring

end PfHk.UniqueContinuation
