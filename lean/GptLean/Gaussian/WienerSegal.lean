import GptLean.Gaussian.Disintegration

/-!
The user-authorized Wiener–Itô–Segal input, followed by its consequences for
the Gaussian appendix. The input gives only the L² norm identity, measurable
representatives and field/multiplication intertwining on the field domain.
It does not assume existence or uniqueness of the disintegration.

The concrete Fock space, unbounded field domain and trace-class operator model
remain interfaces. Their realization is not supplied by these generic proofs.
-/

namespace GptLean.Gaussian

open MeasureTheory
open scoped ENNReal

variable {Q H K G T : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [NormedAddCommGroup H] [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

/-- The precise portion of the standard Wiener–Itô–Segal theorem used here.
`H` represents the original hard/soft tensor product and `K` the hard fibers.
`fieldDomain` prevents treating unbounded fields as everywhere defined. -/
structure WienerSegalData (Q H K G : Type*) [MeasurableSpace Q]
    (μ : Measure Q) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedSpace ℝ K] where
  toFiber : H → Q → K
  measurable_fiber : ∀ ψ, AEStronglyMeasurable (toFiber ψ) μ
  norm_sq : ∀ ψ, ∫⁻ u, ENNReal.ofReal (‖toFiber ψ u‖ ^ 2) ∂μ =
    ENNReal.ofReal (‖ψ‖ ^ 2)
  fieldDomain : G → H → Prop
  field : G → H → H
  coordinate : G → Q → ℝ
  intertwining : ∀ g ψ, fieldDomain g ψ →
    toFiber (field g ψ) =ᵐ[μ] fun u => coordinate g u • toFiber ψ u

namespace WienerSegalData

variable (W : WienerSegalData Q H K G μ)

/-- Tonelli and the WIS norm identity give precisely the finite-mass input
needed to construct the trace-norm series. -/
theorem finite_fiber_mass {ψ : ℕ → H}
    (hψ : ∑' n, ENNReal.ofReal (‖ψ n‖ ^ 2) ≠ ⊤) :
    ∑' n, ∫⁻ u, ENNReal.ofReal (‖W.toFiber (ψ n) u‖ ^ 2) ∂μ ≠ ⊤ := by
  simpa only [W.norm_sq] using hψ

theorem integrated_total_fiber_mass (ψ : ℕ → H) :
    ∫⁻ u, ∑' n, ENNReal.ofReal (‖W.toFiber (ψ n) u‖ ^ 2) ∂μ =
      ∑' n, ENNReal.ofReal (‖ψ n‖ ^ 2) := by
  rw [lintegral_tsum]
  · simp only [W.norm_sq]
  · intro n
    exact ((W.measurable_fiber (ψ n)).norm.aemeasurable.pow_const 2).ennreal_ofReal

/-- Squared field norms become conditional Gaussian second moments. -/
theorem field_second_moment (g : G) (ψ : H) (hdom : W.fieldDomain g ψ) :
    ENNReal.ofReal (‖W.field g ψ‖ ^ 2) =
      ∫⁻ u, ENNReal.ofReal ((W.coordinate g u) ^ 2 * ‖W.toFiber ψ u‖ ^ 2) ∂μ := by
  rw [← W.norm_sq (W.field g ψ)]
  apply lintegral_congr_ae
  filter_upwards [W.intertwining g ψ hdom] with u hu
  rw [hu, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Construction and positivity of the appendix's conditional density from
the standard rank-one and WIS inputs, with no disintegration premise. -/
theorem density_exists (R : RankOneData K T) {ψ : ℕ → H}
    (hψ : ∑' n, ENNReal.ofReal (‖ψ n‖ ^ 2) ≠ ⊤) :
    Integrable (R.density (fun n => W.toFiber (ψ n))) μ ∧
    (∀ᵐ u ∂μ, Summable (fun n => R.rankOne (W.toFiber (ψ n) u))) ∧
    (∀ᵐ u ∂μ, R.density (fun n => W.toFiber (ψ n)) u ∈ R.positive) ∧
    (∀ᵐ u ∂μ, R.trace (R.density (fun n => W.toFiber (ψ n)) u) =
      ∑' n, ‖W.toFiber (ψ n) u‖ ^ 2) := by
  have hv := fun n => W.measurable_fiber (ψ n)
  have hmass := W.finite_fiber_mass hψ
  exact ⟨R.density_integrable hv hmass, R.density_summable_ae hv hmass,
    R.density_positive_ae hv hmass, R.trace_density_ae hv hmass⟩

/-- Complex bounded observable/test duality for the constructed density.
Identifying the left side with the source operator trace uses the standard
trace expansion and the WIS bounded multiplication-operator identity. -/
theorem density_test_duality (R : RankOneData K T) {ψ : ℕ → H}
    (hψ : ∑' n, ENNReal.ofReal (‖ψ n‖ ^ 2) ≠ ⊤)
    (B : T →L[ℝ] ℂ) {f : Q → ℂ} (hf : AEStronglyMeasurable f μ)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ u ∂μ, ‖f u‖ ≤ M) :
    (∑' n, ∫ u, f u * B (R.rankOne (W.toFiber (ψ n) u)) ∂μ) =
      ∫ u, f u * B (R.density (fun n => W.toFiber (ψ n)) u) ∂μ := by
  apply bounded_test_series_duality
    (R.rankOne_aestronglyMeasurable (fun n => W.measurable_fiber (ψ n)))
    (R.rankOne_total_finite (W.finite_fiber_mass hψ)) B hf hM hbound

theorem density_total_trace (R : RankOneData K T) {ψ : ℕ → H}
    (hψ : ∑' n, ENNReal.ofReal (‖ψ n‖ ^ 2) ≠ ⊤) :
    ∫⁻ u, ENNReal.ofReal (R.trace (R.density (fun n => W.toFiber (ψ n)) u)) ∂μ =
      ∑' n, ENNReal.ofReal (‖ψ n‖ ^ 2) := by
  rw [R.total_trace_density (fun n => W.measurable_fiber (ψ n)) (W.finite_fiber_mass hψ)]
  simp only [W.norm_sq]

end WienerSegalData

end GptLean.Gaussian
