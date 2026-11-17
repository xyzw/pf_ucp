import GptLean.PhotonLocalizationFormBoundsLifting
import GptLean.PhotonLocalizationFockChannel

/-!
Number and radiation estimates for the constructed photon channel.
The only Fock form background is uniform in every one-photon splitting
and every nonnegative observable. The cutoff inequalities are then lifted
through the proved sector, Kraus, and source spectral sums.
-/

namespace GptLean.PhotonLocalizationFormBounds

open MeasureTheory Filter Topology
open scoped ENNReal
open PhotonLocalizationChannel PhotonLocalizationFockChannel PhotonLocalizationKernelCutoffs

variable {h H T Q : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

/-- Universal additive second quantization on finite sectors, followed by
monotone sums. `pullback` is the vector tensor-factorization identity for
every splitting isometry. It contains no cutoff, localized estimate,
compactness assertion or restriction on the original photon number. -/
structure FockFormCalculus (R : Gaussian.RankOneData H T)
    (Tr : RemovalState.PositiveTraceData T) (F : FockFactorization h H) (Q : Type*) where
  value : Q → h → ℝ≥0∞
  observable : Q → RemovalState.PositiveForm Tr
  slice : H → (m : ℕ) → Fin m → ℕ → h
  rankOne : ∀ q v, (observable q).expectation (R.rankOne v) = fockForm (value q) (slice v)
  pullback : ∀ (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) q v,
    (∑' a, (observable q).expectation (R.rankOne (F.factor j v a))) =
      fockForm (fun u => value q (retainedMap j u)) (slice v)

namespace FockFormCalculus

variable {R : Gaussian.RankOneData H T} {Tr : RemovalState.PositiveTraceData T}
  {F : FockFactorization h H} (D : FockFormCalculus R Tr F Q)
  (N : NormalTraceData R)

/-- Any proved one-photon form order gives the actual mixed-state
localization estimate, including infinite nonnegative traces. -/
theorem channel_bound (hpositive : R.positive ⊆ Tr.positive)
    (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (q p : Q) {C : ℝ≥0∞}
    (hone : ∀ u, D.value q (retainedMap j u) ≤ C * D.value p u)
    {x : T} (hx : x ∈ R.positive) :
    (D.observable q).expectation (N.extend (F.factor j) x) ≤
      C * (D.observable p).expectation x := by
  apply channel_form_le N (D.observable q) (D.observable p) hpositive (F.factor j) _ hx
  intro v
  rw [D.pullback, D.rankOne]
  exact fockForm_le hone (D.slice v)

end FockFormCalculus

section Cutoffs

variable {P E : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [MeasurableSpace P] [BorelSpace P] {μ : Measure P}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E]
  {R : Gaussian.RankOneData H T} {Tr : RemovalState.PositiveTraceData T}
  {F : FockFactorization (Lp E 2 μ) H}
  (D : FockFormCalculus R Tr F Q) (N : NormalTraceData R)

omit [IsScalarTower ℝ ℂ E] in
/-- The square partition alone proves that localization decreases the
mean photon number, with no finite-number assumption. -/
theorem localized_number_decrease (hpositive : R.positive ⊆ Tr.positive)
    (number : Q) (hnumber : ∀ u, D.value number u = ENNReal.ofReal (‖u‖ ^ 2))
    (r : ℝ) {x : T} (hx : x ∈ R.positive) :
    (D.observable number).expectation (N.extend (F.factor (complexOnePhotonIsometry r)) x) ≤
      (D.observable number).expectation x := by
  simpa only [one_mul] using D.channel_bound N hpositive (complexOnePhotonIsometry r)
    number number (C := 1) (fun u => by
      rw [hnumber, hnumber, one_mul]
      apply ENNReal.ofReal_le_ofReal
      change ‖retainedOperator r u‖ ^ 2 ≤ ‖u‖ ^ 2
      nlinarith [square_partition_l2 r u, sq_nonneg ‖discardedOperator r u‖]) hx

omit [IsScalarTower ℝ ℂ E] in
/-- The fractional Hardy estimate supplies the missing number bound for
every finite-radiation source, even if its original number is infinite. -/
theorem localized_number_le_radiation (hpositive : R.positive ⊆ Tr.positive)
    (number radiation : Q)
    (hnumber : ∀ u, D.value number u = ENNReal.ofReal (‖u‖ ^ 2))
    {r CH : ℝ} (hr : 0 < r) (hCH : 0 < CH)
    (hradius : ∀ᵐ y ∂μ, 0 < ‖y‖)
    (hweighted : ∀ u, D.value radiation u ≠ ⊤ → Integrable (fun y => ‖u y‖ ^ 2 / ‖y‖) μ)
    (hHardy : ∀ u, D.value radiation u ≠ ⊤ →
      (∫ y, ‖u y‖ ^ 2 / ‖y‖ ∂μ) ≤ CH * (D.value radiation u).toReal)
    {x : T} (hx : x ∈ R.positive) :
    (D.observable number).expectation (N.extend (F.factor (complexOnePhotonIsometry r)) x) ≤
      ENNReal.ofReal (2 * CH * r) * (D.observable radiation).expectation x := by
  apply D.channel_bound N hpositive (complexOnePhotonIsometry r) number radiation _ hx
  intro u
  rw [hnumber]
  by_cases hu : D.value radiation u = ⊤
  · simp [hu, (ENNReal.ofReal_pos.mpr (by positivity : 0 < 2 * CH * r)).ne']
  · have hb := retainedOperator_mass_le_hardy u hr hradius (hweighted u hu) (hHardy u hu)
    have he := ENNReal.ofReal_le_ofReal hb
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * CH * r), ENNReal.ofReal_toReal hu] at he
    exact he

omit [IsScalarTower ℝ ℂ E] in
/-- The radiation estimate extends a bound proved on the original form
core by closedness, then lifts it through the actual Fock channel. -/
theorem localized_radiation_le_of_core (hpositive : R.positive ⊆ Tr.positive)
    (radiation : Q) (core : Set (Lp E 2 μ))
    (hlsc : LowerSemicontinuous (D.value radiation))
    (happrox : ∀ u, D.value radiation u < ⊤ → ∃ v : ℕ → Lp E 2 μ,
      (∀ n, v n ∈ core) ∧ Tendsto v atTop (𝓝 u) ∧
        Tendsto (fun n => D.value radiation (v n)) atTop (𝓝 (D.value radiation u)))
    (r : ℝ) {C : ℝ} (hC : 0 < C)
    (hcore : ∀ u ∈ core,
      D.value radiation (retainedOperator r u) ≤ ENNReal.ofReal C * D.value radiation u)
    {x : T} (hx : x ∈ R.positive) :
    (D.observable radiation).expectation (N.extend (F.factor (complexOnePhotonIsometry r)) x) ≤
      ENNReal.ofReal C * (D.observable radiation).expectation x := by
  apply D.channel_bound N hpositive (complexOnePhotonIsometry r) radiation radiation _ hx
  exact form_bound_of_core (D.value radiation) core hlsc happrox (retainedOperator r) hC hcore

end Cutoffs

end GptLean.PhotonLocalizationFormBounds
