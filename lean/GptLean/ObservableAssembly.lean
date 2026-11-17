import GptLean.PositiveForm
import Mathlib.Analysis.Normed.Group.Tannery

/-!
Unbounded current tests of the constructed removal operator. Bounded
spectral approximants are evaluated by trace duality. Two dominated
convergence arguments, first over the conditional parameter and then over
the localization index, prove the full unbounded observable identity.

The existence of the spectral trace limit on the positive finite-energy
domain is standard form-trace calculus. The conditional domination bound
must be established for the actual tested current, for example by the
coordinate-channel mass and kinetic estimates.
-/

namespace GptLean.RemovalState

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Q T : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : PositiveTraceData T}

/-- The standard bounded approximants to a form-bounded trace observable.
There is no conditional-state or aggregate identity among these fields. -/
structure FormObservable (E : PositiveForm R) where
  approximation : ℕ → T →L[ℝ] ℝ
  value : T → ℝ
  converges : ∀ x ∈ R.positive, E.expectation x < ⊤ →
    Tendsto (fun n => approximation n x) atTop (𝓝 (value x))

namespace FormObservable

variable {E : PositiveForm R} (J : FormObservable E)

omit [CompleteSpace T] in
/-- A uniform integrable majorant proves individual current integrability
and the limit of the corresponding bounded tested traces. -/
theorem conditional_integral_limit {G : Q → T} {bound : Q → ℝ}
    (hG : AEStronglyMeasurable G μ)
    (hpos : ∀ᵐ q ∂μ, G q ∈ R.positive)
    (hfinite : ∀ᵐ q ∂μ, E.expectation (G q) < ⊤)
    (hb : Integrable bound μ)
    (hbound : ∀ n, ∀ᵐ q ∂μ, ‖J.approximation n (G q)‖ ≤ bound q) :
    Integrable (fun q => J.value (G q)) μ ∧
    (∀ᵐ q ∂μ, ‖J.value (G q)‖ ≤ bound q) ∧
    Tendsto (fun n => ∫ q, J.approximation n (G q) ∂μ) atTop
      (𝓝 (∫ q, J.value (G q) ∂μ)) := by
  have hm (n : ℕ) := (J.approximation n).continuous.comp_aestronglyMeasurable hG
  have hl : ∀ᵐ q ∂μ, Tendsto (fun n => J.approximation n (G q)) atTop
      (𝓝 (J.value (G q))) := by
    filter_upwards [hpos, hfinite] with q hp hf
    exact J.converges _ hp hf
  have hJm := aestronglyMeasurable_of_tendsto_ae atTop hm hl
  have hJb : ∀ᵐ q ∂μ, ‖J.value (G q)‖ ≤ bound q := by
    filter_upwards [hl, ae_all_iff.mpr hbound] with q hq hbq
    exact le_of_tendsto' hq.norm hbq
  exact ⟨hb.mono' hJm hJb, hJb,
    tendsto_integral_of_dominated_convergence bound hm hb hbound hl⟩

/-- The full current trace of the actual aggregate equals the conditional
current series. Absolute integral summability is a conclusion. -/
theorem value_aggregate {G : ℕ → Q → T} {bound : ℕ → Q → ℝ}
    (hG : ∀ a, Integrable (G a) μ)
    (hpos : ∀ a, ∀ᵐ q ∂μ, G a q ∈ R.positive)
    (hfinite : ∀ a, ∀ᵐ q ∂μ, E.expectation (G a q) < ⊤)
    (hs : Summable (fun a => ∫ q, ‖G a q‖ ∂μ))
    (haggregate_pos : aggregate G μ ∈ R.positive)
    (haggregate_finite : E.expectation (aggregate G μ) < ⊤)
    (hb : ∀ a, Integrable (bound a) μ)
    (hbs : Summable (fun a => ∫ q, bound a q ∂μ))
    (hbound : ∀ n a, ∀ᵐ q ∂μ, ‖J.approximation n (G a q)‖ ≤ bound a q) :
    (∀ a, Integrable (fun q => J.value (G a q)) μ) ∧
    Summable (fun a => ∫ q, ‖J.value (G a q)‖ ∂μ) ∧
    J.value (aggregate G μ) = ∑' a, ∫ q, J.value (G a q) ∂μ := by
  have hlocal (a : ℕ) := J.conditional_integral_limit (hG a).1 (hpos a)
    (hfinite a) (hb a) (fun n => hbound n a)
  have hnormbound (a : ℕ) : (∫ q, ‖J.value (G a q)‖ ∂μ) ≤ ∫ q, bound a q ∂μ :=
    integral_mono_ae (hlocal a).1.norm (hb a) (hlocal a).2.1
  have hnormsum : Summable (fun a => ∫ q, ‖J.value (G a q)‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun a => integral_nonneg (fun q => norm_nonneg _))
      hnormbound hbs
  refine ⟨fun a => (hlocal a).1, hnormsum, ?_⟩
  have hsumlim : Tendsto (fun n => ∑' a, ∫ q, J.approximation n (G a q) ∂μ)
      atTop (𝓝 (∑' a, ∫ q, J.value (G a q) ∂μ)) := by
    apply tendsto_tsum_of_dominated_convergence hbs (fun a => (hlocal a).2.2)
    apply Eventually.of_forall
    intro n a
    apply (norm_integral_le_integral_norm _).trans
    exact integral_mono_ae ((J.approximation n).integrable_comp (hG a)).norm
      (hb a) (hbound n a)
  have hagg := PositiveForm.aggregate_hasSum_of_norm hs
  have heq (n : ℕ) : J.approximation n (aggregate G μ) =
      ∑' a, ∫ q, J.approximation n (G a q) ∂μ := by
    have hh := ((J.approximation n).hasSum hagg).tsum_eq.symm
    simpa only [← (J.approximation n).integral_comp_comm (hG _)] using hh
  exact tendsto_nhds_unique (J.converges _ haggregate_pos haggregate_finite)
    (by simpa only [heq] using hsumlim)

end FormObservable

end GptLean.RemovalState
