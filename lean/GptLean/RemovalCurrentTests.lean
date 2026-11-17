import GptLean.RemovalChannelConstraints

/-!
Bounded spatial current tests use the channel's own derivative arrays.
Their connection and kinetic integrability follow from the channel
energy theorem. They are not independent current hypotheses.
-/

namespace GptLean.RemovalEnergy

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open MeasureTheory MeasureTheory.Measure Filter Repair RemovalState

section Algebra

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem weighted_current_connection (z dz : V) (c s : ℝ)
    (h : inner ℂ z dz = Complex.I * s) :
    inner ℂ z ((c : ℂ) • dz) = Complex.I * ((c * s : ℝ) : ℂ) := by
  rw [inner_smul_right, h, Complex.ofReal_mul]
  ring

theorem weighted_current_kinetic (dz : V) (u ψ : H) (c s : ℝ) :
    ‖(c : ℂ) • u‖ ^ 2 + 2 * (c * s) * (inner ℂ ((c : ℂ) • u) ψ).re +
      ‖(c : ℂ) • dz‖ ^ 2 * ‖ψ‖ ^ 2 =
      c ^ 2 * (‖u‖ ^ 2 + 2 * s * (inner ℂ u ψ).re + ‖dz‖ ^ 2 * ‖ψ‖ ^ 2) := by
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_left, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

end Algebra

section Channel

variable {Q X J V H F T : Type*}
  [MeasurableSpace Q] [MeasurableSpace X] {μ : Measure Q} {ν : Measure X}
  [IsProbabilityMeasure μ] [SFinite ν] [IsSeparable ν] [Fintype J]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {basis : HilbertBasis ℕ ℂ V}
  {R : Gaussian.RankOneData (Lp H 2 ν) T} {Tr : PositiveTraceData T} {E : PositiveForm Tr}
  {C CZ e k L a b : ℝ}
  (D : ChannelData (J := J) (F := F) basis R Tr E μ C CZ e k L a b)

/-- Each directional Parseval kinetic density is integrable because it
is nonnegative and is at most twice the complete channel kinetic density. -/
theorem ChannelData.directional_current_kinetic_integrable (i : ℕ) (j : J) :
    ∀ᵐ q ∂μ, Integrable (fun x => ‖D.u i j (q, x)‖ ^ 2 +
      2 * D.s i j (q, x) * (inner ℂ (D.u i j (q, x)) (D.ψ i (q, x))).re +
        ‖D.dz i j (q, x)‖ ^ 2 * ‖D.ψ i (q, x)‖ ^ 2) ν := by
  classical
  filter_upwards [D.local_energy i, (D.u_measurable i j).prodMk_left,
    (D.dz_measurable i j).prodMk_left, (D.s_measurable i j).prodMk_left,
    ae_ae_of_ae_prod (D.unit i), ae_ae_of_ae_prod (D.connection i j)]
    with q hlocal hu hdz hs hunit hc
  have hψ : AEStronglyMeasurable (fun x => D.ψ i (q, x)) ν :=
    ((D.ψ_measurable i).comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun x => ‖D.u i j (q, x)‖ ^ 2 +
      2 * D.s i j (q, x) * (inner ℂ (D.u i j (q, x)) (D.ψ i (q, x))).re +
        ‖D.dz i j (q, x)‖ ^ 2 * ‖D.ψ i (q, x)‖ ^ 2) ν :=
    ((hu.norm.pow 2).add ((hs.const_mul 2).mul
      (Complex.continuous_re.comp_aestronglyMeasurable (hu.inner hψ)))).add
      ((hdz.norm.pow 2).mul (hψ.norm.pow 2))
  apply (hlocal.1.const_mul 2).mono' hm
  filter_upwards [hunit, hc] with x hx hcx
  have hp := coordinate_channel_energy basis hx hcx (D.u i j (q, x)) (D.ψ i (q, x))
  have hpos := hp.nonneg (fun _ => sq_nonneg _)
  rw [Real.norm_of_nonneg hpos, ← hp.tsum_eq]
  have hle := Finset.single_le_sum
    (f := fun l : J => ∑' n, ‖coordinate basis (D.z i (q, x)) n • D.u i l (q, x) -
      Complex.I • coordinate basis (D.dz i l (q, x)) n • D.ψ i (q, x)‖ ^ 2)
    (fun _ (_ : _ ∈ (Finset.univ : Finset J)) => tsum_nonneg (fun _ => sq_nonneg _))
    (Finset.mem_univ j)
  simpa only [localChannelKinetic, ← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    one_mul] using hle

theorem ChannelData.weighted_current_kinetic_integrable
    (weight : X → ℝ) (hw : AEStronglyMeasurable weight ν) {B : ℝ}
    (hbound : ∀ᵐ x ∂ν, ‖weight x‖ ≤ B) (i : ℕ) (j : J) :
    ∀ᵐ q ∂μ, Integrable (fun x => ‖(weight x : ℂ) • D.u i j (q, x)‖ ^ 2 +
      2 * (weight x * D.s i j (q, x)) *
        (inner ℂ ((weight x : ℂ) • D.u i j (q, x)) (D.ψ i (q, x))).re +
      ‖(weight x : ℂ) • D.dz i j (q, x)‖ ^ 2 * ‖D.ψ i (q, x)‖ ^ 2) ν := by
  filter_upwards [D.directional_current_kinetic_integrable i j] with q hq
  have hb : ∀ᵐ x ∂ν, ‖weight x ^ 2‖ ≤ B ^ 2 := hbound.mono fun x hx => by
    simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg (weight x)) hx 2
  simpa only [weighted_current_kinetic, Pi.pow_apply] using hq.bdd_mul (hw.pow 2) hb

end Channel
end GptLean.RemovalEnergy
