import GptLean.Repair.CoordinateChannel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
Integration of the countable current-repair channel. The functions below
are the actual Hilbert-basis multipliers and their product derivatives.
The current series is absolutely integrable as a consequence of mass and
kinetic integrability. No exchange of an unbounded current with an infinite
sum is assumed. Nonnegative multiplication observables are preserved even
when their expectations are infinite.

Identifying these vector integrals with trace-class form expectations and
proving the physical covariant weak product rule remain separate tasks.
-/

namespace GptLean.Repair

open MeasureTheory Filter
open scoped ENNReal

variable {X V H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Every term of a measurable nonnegative series with integrable sum is
integrable. -/
theorem integrable_term_of_nonnegative_hasSum {f : ℕ → X → ℝ} {g : X → ℝ}
    (hf : ∀ a, AEStronglyMeasurable (f a) μ)
    (hpos : ∀ a, ∀ᵐ x ∂μ, 0 ≤ f a x)
    (hs : ∀ᵐ x ∂μ, HasSum (fun a => f a x) (g x))
    (hg : Integrable g μ) (a : ℕ) : Integrable (f a) μ := by
  apply hg.mono' (hf a)
  filter_upwards [hs, ae_all_iff.mpr hpos] with x hx hp
  rw [Real.norm_of_nonneg (hp a)]
  simpa only [Finset.sum_singleton, hx.tsum_eq] using
    hx.summable.sum_le_tsum {a} (fun i _ => hp i)

/-- Nonnegative pointwise series can be integrated using their integrable
sum. This also proves the summability of the resulting integrals. -/
theorem hasSum_integral_nonnegative {f : ℕ → X → ℝ} {g : X → ℝ}
    (hf : ∀ a, AEStronglyMeasurable (f a) μ)
    (hpos : ∀ a, ∀ᵐ x ∂μ, 0 ≤ f a x)
    (hs : ∀ᵐ x ∂μ, HasSum (fun a => f a x) (g x))
    (hg : Integrable g μ) :
    HasSum (fun a => ∫ x, f a x ∂μ) (∫ x, g x ∂μ) := by
  apply hasSum_integral_of_dominated_convergence f hf
  · intro a
    filter_upwards [hpos a] with x hx
    rw [Real.norm_of_nonneg hx]
  · exact hs.mono (fun _ h => h.summable)
  · exact hg.congr (hs.mono (fun _ h => h.tsum_eq.symm))
  · exact hs

/-- Each current term is integrable before its integral is taken. This
excludes any reliance on Lean's zero value for a nonintegrable integral. -/
theorem inner_term_integrable {p q : ℕ → X → H} {mass kinetic : X → ℝ}
    (hp : ∀ a, AEStronglyMeasurable (p a) μ)
    (hq : ∀ a, AEStronglyMeasurable (q a) μ)
    (hm : ∀ᵐ x ∂μ, HasSum (fun a => ‖p a x‖ ^ 2) (mass x))
    (hk : ∀ᵐ x ∂μ, HasSum (fun a => ‖q a x‖ ^ 2) (kinetic x))
    (hmint : Integrable mass μ) (hkint : Integrable kinetic μ) (a : ℕ) :
    Integrable (fun x => inner ℂ (p a x) (q a x)) μ := by
  apply ((hmint.add hkint).div_const 2).mono' ((hp a).inner (hq a))
  filter_upwards [hm, hk] with x hmx hkx
  have hpbound : ‖p a x‖ ^ 2 ≤ mass x := by
    simpa only [Finset.sum_singleton, hmx.tsum_eq] using
      hmx.summable.sum_le_tsum {a} (fun i _ => sq_nonneg ‖p i x‖)
  have hqbound : ‖q a x‖ ^ 2 ≤ kinetic x := by
    simpa only [Finset.sum_singleton, hkx.tsum_eq] using
      hkx.summable.sum_le_tsum {a} (fun i _ => sq_nonneg ‖q i x‖)
  have hi := norm_inner_le_norm (𝕜 := ℂ) (p a x) (q a x)
  change ‖inner ℂ (p a x) (q a x)‖ ≤ (mass x + kinetic x) / 2
  nlinarith [sq_nonneg (‖p a x‖ - ‖q a x‖)]

/-- Absolute current integrability follows from the two quadratic sums.
The estimate uses Cauchy--Schwarz followed by the scalar Young inequality. -/
theorem integrated_inner_series {p q : ℕ → X → H} {mass kinetic : X → ℝ}
    {current : X → ℂ}
    (hp : ∀ a, AEStronglyMeasurable (p a) μ)
    (hq : ∀ a, AEStronglyMeasurable (q a) μ)
    (hm : ∀ᵐ x ∂μ, HasSum (fun a => ‖p a x‖ ^ 2) (mass x))
    (hk : ∀ᵐ x ∂μ, HasSum (fun a => ‖q a x‖ ^ 2) (kinetic x))
    (hc : ∀ᵐ x ∂μ, HasSum (fun a => inner ℂ (p a x) (q a x)) (current x))
    (hmint : Integrable mass μ) (hkint : Integrable kinetic μ) :
    HasSum (fun a => ∫ x, inner ℂ (p a x) (q a x) ∂μ)
      (∫ x, current x ∂μ) ∧
    Summable (fun a => ∫ x, ‖inner ℂ (p a x) (q a x)‖ ∂μ) := by
  let bound := fun a x => (‖p a x‖ ^ 2 + ‖q a x‖ ^ 2) / 2
  have hbound : ∀ a, ∀ᵐ x ∂μ, ‖inner ℂ (p a x) (q a x)‖ ≤ bound a x := by
    intro a
    filter_upwards with x
    dsimp [bound]
    have h := norm_inner_le_norm (𝕜 := ℂ) (p a x) (q a x)
    nlinarith [sq_nonneg (‖p a x‖ - ‖q a x‖)]
  have hb : ∀ᵐ x ∂μ, HasSum (fun a => bound a x) ((mass x + kinetic x) / 2) := by
    filter_upwards [hm, hk] with x hx hy
    exact (hx.add hy).div_const 2
  have hbint : Integrable (fun x => ∑' a, bound a x) μ :=
    ((hmint.add hkint).div_const 2).congr (hb.mono (fun _ h => h.tsum_eq.symm))
  have hmeas : ∀ a, AEStronglyMeasurable (fun x => inner ℂ (p a x) (q a x)) μ :=
    fun a => (hp a).inner (hq a)
  refine ⟨hasSum_integral_of_dominated_convergence bound hmeas hbound
    (hb.mono (fun _ h => h.summable)) hbint hc, ?_⟩
  have hnormsum : ∀ᵐ x ∂μ, Summable (fun a => ‖inner ℂ (p a x) (q a x)‖) := by
    have hba := ae_all_iff.mpr hbound
    filter_upwards [hb, hba] with x hx hbx
    exact Summable.of_nonneg_of_le (fun a => norm_nonneg _) hbx hx.summable
  apply (hasSum_integral_of_dominated_convergence bound (fun a => (hmeas a).norm)
    (fun a => by simpa only [norm_norm] using hbound a)
    (hb.mono (fun _ h => h.summable)) hbint
    (hnormsum.mono (fun _ h => h.hasSum))).summable

/-- The multiplier applied to a wavefunction, before forming rank-one states. -/
noncomputable def channelValue (b : HilbertBasis ℕ ℂ V)
    (z : X → V) (ψ : X → H) (a : ℕ) (x : X) : H :=
  coordinate b (z x) a • ψ x

/-- The covariant product derivative for the same multiplier. -/
noncomputable def channelDerivative (b : HilbertBasis ℕ ℂ V)
    (z dz : X → V) (u ψ : X → H) (a : ℕ) (x : X) : H :=
  coordinate b (z x) a • u x - Complex.I • coordinate b (dz x) a • ψ x

theorem channelValue_measurable (b : HilbertBasis ℕ ℂ V)
    {z : X → V} {ψ : X → H}
    (hz : AEStronglyMeasurable z μ) (hψ : AEStronglyMeasurable ψ μ) (a : ℕ) :
    AEStronglyMeasurable (channelValue b z ψ a) μ :=
  (coordinate_aestronglyMeasurable b hz a).smul hψ

theorem channelDerivative_measurable (b : HilbertBasis ℕ ℂ V)
    {z dz : X → V} {u ψ : X → H}
    (hz : AEStronglyMeasurable z μ) (hdz : AEStronglyMeasurable dz μ)
    (hu : AEStronglyMeasurable u μ) (hψ : AEStronglyMeasurable ψ μ) (a : ℕ) :
    AEStronglyMeasurable (channelDerivative b z dz u ψ a) μ :=
  ((coordinate_aestronglyMeasurable b hz a).smul hu).sub
    (((coordinate_aestronglyMeasurable b hdz a).smul hψ).const_smul Complex.I)

/-- Total mass is preserved after integrating over configuration space. -/
theorem integrated_channel_mass (b : HilbertBasis ℕ ℂ V)
    {z : X → V} {ψ : X → H}
    (hz : AEStronglyMeasurable z μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hint : Integrable (fun x => ‖ψ x‖ ^ 2) μ) :
    HasSum (fun a => ∫ x, ‖channelValue b z ψ a x‖ ^ 2 ∂μ)
      (∫ x, ‖ψ x‖ ^ 2 ∂μ) := by
  apply hasSum_integral_nonnegative
    (fun a => ((channelValue_measurable b hz hψ a).norm).pow 2)
    (fun a => Eventually.of_forall (fun x => sq_nonneg _)) _ hint
  filter_upwards [hunit] with x hx
  simpa only [channelValue, Pi.pow_apply, hx, one_pow, one_mul] using
    coordinate_smul_norm_sq_hasSum b (z x) (ψ x)

/-- The exact kinetic formula survives the countable sum and integral. -/
theorem integrated_channel_energy (b : HilbertBasis ℕ ℂ V)
    {z dz : X → V} {u ψ : X → H} {s : X → ℝ}
    (hz : AEStronglyMeasurable z μ) (hdz : AEStronglyMeasurable dz μ)
    (hu : AEStronglyMeasurable u μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hconn : ∀ᵐ x ∂μ, inner ℂ (z x) (dz x) = Complex.I * s x)
    (hint : Integrable (fun x => ‖u x‖ ^ 2 +
      2 * s x * (inner ℂ (u x) (ψ x)).re + ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2) μ) :
    HasSum (fun a => ∫ x, ‖channelDerivative b z dz u ψ a x‖ ^ 2 ∂μ)
      (∫ x, ‖u x‖ ^ 2 + 2 * s x * (inner ℂ (u x) (ψ x)).re +
        ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2 ∂μ) := by
  apply hasSum_integral_nonnegative
    (fun a => ((channelDerivative_measurable b hz hdz hu hψ a).norm).pow 2)
    (fun a => Eventually.of_forall (fun x => sq_nonneg _)) _ hint
  filter_upwards [hunit, hconn] with x hx hc
  exact coordinate_channel_energy b hx hc (u x) (ψ x)

/-- Finite source kinetic energy and the weighted lift metric imply
integrability of the exact output energy density, including its cross term. -/
theorem channel_energy_integrable (b : HilbertBasis ℕ ℂ V)
    {z dz : X → V} {u ψ : X → H} {s : X → ℝ}
    (hdz : AEStronglyMeasurable dz μ)
    (hu : AEStronglyMeasurable u μ) (hψ : AEStronglyMeasurable ψ μ)
    (hs : AEStronglyMeasurable s μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hconn : ∀ᵐ x ∂μ, inner ℂ (z x) (dz x) = Complex.I * s x)
    (hsource : Integrable (fun x => ‖u x‖ ^ 2) μ)
    (hmetric : Integrable (fun x => ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2) μ) :
    Integrable (fun x => ‖u x‖ ^ 2 +
      2 * s x * (inner ℂ (u x) (ψ x)).re + ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2) μ := by
  have hreal := Complex.continuous_re.comp_aestronglyMeasurable (hu.inner hψ)
  apply ((hsource.add hmetric).const_mul 2).mono'
    (((hu.norm.pow 2).add ((hs.const_mul 2).mul hreal)).add
      ((hdz.norm.pow 2).mul (hψ.norm.pow 2)))
  filter_upwards [hunit, hconn] with x hx hc
  have hnonneg : 0 ≤ ‖u x‖ ^ 2 + 2 * s x * (inner ℂ (u x) (ψ x)).re +
      ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2 := by
    rw [← (coordinate_channel_energy b hx hc (u x) (ψ x)).tsum_eq]
    exact tsum_nonneg (fun a => sq_nonneg _)
  change ‖‖u x‖ ^ 2 + 2 * s x * (inner ℂ (u x) (ψ x)).re +
    ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2‖ ≤ 2 * (‖u x‖ ^ 2 + ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2)
  rw [Real.norm_of_nonneg hnonneg]
  have hsbound : |s x| ≤ ‖dz x‖ := by
    have hh := norm_inner_le_norm (𝕜 := ℂ) (z x) (dz x)
    rw [hc, hx, one_mul, norm_mul] at hh
    simpa using hh
  have hinner : |(inner ℂ (u x) (ψ x)).re| ≤ ‖u x‖ * ‖ψ x‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have hcross : s x * (inner ℂ (u x) (ψ x)).re ≤
      ‖dz x‖ * (‖u x‖ * ‖ψ x‖) :=
    (le_abs_self _).trans ((abs_mul _ _).trans_le
      (mul_le_mul hsbound hinner (abs_nonneg _) (norm_nonneg _)))
  nlinarith [sq_nonneg (‖u x‖ - ‖dz x‖ * ‖ψ x‖)]

/-- Every actual channel derivative has finite quadratic integral. The
total energy integrability is derived from the source and lift metric. -/
theorem channel_derivative_integrable_sq (b : HilbertBasis ℕ ℂ V)
    {z dz : X → V} {u ψ : X → H} {s : X → ℝ}
    (hz : AEStronglyMeasurable z μ) (hdz : AEStronglyMeasurable dz μ)
    (hu : AEStronglyMeasurable u μ) (hψ : AEStronglyMeasurable ψ μ)
    (hs : AEStronglyMeasurable s μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hconn : ∀ᵐ x ∂μ, inner ℂ (z x) (dz x) = Complex.I * s x)
    (hsource : Integrable (fun x => ‖u x‖ ^ 2) μ)
    (hmetric : Integrable (fun x => ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2) μ) (a : ℕ) :
    Integrable (fun x => ‖channelDerivative b z dz u ψ a x‖ ^ 2) μ := by
  apply integrable_term_of_nonnegative_hasSum
    (fun a => ((channelDerivative_measurable b hz hdz hu hψ a).norm).pow 2)
    (fun a => Eventually.of_forall (fun x => sq_nonneg _)) _
    (channel_energy_integrable b hdz hu hψ hs hunit hconn hsource hmetric) a
  filter_upwards [hunit, hconn] with x hx hc
  exact coordinate_channel_energy b hx hc (u x) (ψ x)

/-- The physical current shift has an absolutely integrable channel series.
Only mass and total kinetic integrability are needed for this exchange. -/
theorem integrated_channel_current (b : HilbertBasis ℕ ℂ V)
    {z dz : X → V} {u ψ : X → H} {s : X → ℝ}
    (hz : AEStronglyMeasurable z μ) (hdz : AEStronglyMeasurable dz μ)
    (hu : AEStronglyMeasurable u μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hconn : ∀ᵐ x ∂μ, inner ℂ (z x) (dz x) = Complex.I * s x)
    (hmass : Integrable (fun x => ‖ψ x‖ ^ 2) μ)
    (hkinetic : Integrable (fun x => ‖u x‖ ^ 2 +
      2 * s x * (inner ℂ (u x) (ψ x)).re + ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2) μ) :
    (∀ a, Integrable (fun x => inner ℂ (channelValue b z ψ a x)
      (channelDerivative b z dz u ψ a x)) μ) ∧
    HasSum (fun a => ∫ x, inner ℂ (channelValue b z ψ a x)
      (channelDerivative b z dz u ψ a x) ∂μ)
      (∫ x, inner ℂ (ψ x) (u x) + (s x : ℂ) * ‖ψ x‖ ^ 2 ∂μ) ∧
    Summable (fun a => ∫ x, ‖inner ℂ (channelValue b z ψ a x)
      (channelDerivative b z dz u ψ a x)‖ ∂μ) := by
  have hm : ∀ᵐ x ∂μ, HasSum (fun a => ‖channelValue b z ψ a x‖ ^ 2) (‖ψ x‖ ^ 2) := by
    filter_upwards [hunit] with x hx
    simpa only [channelValue, hx, one_pow, one_mul] using
      coordinate_smul_norm_sq_hasSum b (z x) (ψ x)
  have hk : ∀ᵐ x ∂μ, HasSum (fun a => ‖channelDerivative b z dz u ψ a x‖ ^ 2)
      (‖u x‖ ^ 2 + 2 * s x * (inner ℂ (u x) (ψ x)).re +
        ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2) := by
    filter_upwards [hunit, hconn] with x hx hc
    exact coordinate_channel_energy b hx hc (u x) (ψ x)
  refine ⟨inner_term_integrable (fun a => channelValue_measurable b hz hψ a)
    (fun a => channelDerivative_measurable b hz hdz hu hψ a) hm hk hmass hkinetic, ?_⟩
  apply integrated_inner_series
    (fun a => channelValue_measurable b hz hψ a)
    (fun a => channelDerivative_measurable b hz hdz hu hψ a) hm hk _ hmass hkinetic
  filter_upwards [hunit, hconn] with x hx hc
  exact coordinate_channel_current b hx hc (u x) (ψ x)

/-- All nonnegative multiplication potentials are preserved by the channel.
This includes unbounded Coulomb potentials and allows infinite expectations. -/
theorem integrated_channel_potential (b : HilbertBasis ℕ ℂ V)
    {z : X → V} {ψ : X → H} (W : X → ℝ≥0∞)
    (hz : AEStronglyMeasurable z μ) (hψ : AEStronglyMeasurable ψ μ)
    (hW : AEMeasurable W μ) (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1) :
    (∑' a, ∫⁻ x, W x * ENNReal.ofReal (‖channelValue b z ψ a x‖ ^ 2) ∂μ) =
      ∫⁻ x, W x * ENNReal.ofReal (‖ψ x‖ ^ 2) ∂μ := by
  have hm : ∀ a, AEMeasurable
      (fun x => W x * ENNReal.ofReal (‖channelValue b z ψ a x‖ ^ 2)) μ := by
    intro a
    exact hW.mul
      ((((channelValue_measurable b hz hψ a).norm).pow 2).aemeasurable.ennreal_ofReal)
  rw [← lintegral_tsum hm]
  apply lintegral_congr_ae
  filter_upwards [hunit] with x hx
  rw [ENNReal.tsum_mul_left]
  congr 1
  have hs : HasSum (fun a => ‖channelValue b z ψ a x‖ ^ 2) (‖ψ x‖ ^ 2) := by
    simpa only [channelValue, hx, one_pow, one_mul] using
      coordinate_smul_norm_sq_hasSum b (z x) (ψ x)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun a => sq_nonneg _) hs.summable, hs.tsum_eq]

end GptLean.Repair
