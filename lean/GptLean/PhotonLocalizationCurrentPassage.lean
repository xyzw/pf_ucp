import GptLean.ObservableAssembly
import GptLean.PhotonLocalizationChannel
import GptLean.PhotonLossClosure

/-!
Bounded-energy passage for tested unbounded normal observables.

The proof first lifts pure-vector form inequalities through the normal
spectral decomposition. Bounded approximants then converge uniformly on
energy sublevels, which proves trace-norm passage. A final constructor
obtains the relative approximation from the spectral cutoff of the tested
observable itself and its square-form estimate. No cutoff of the ambient
Hamiltonian, compact resolvent, or mixed-state passage premise is used.
-/

namespace GptLean.PhotonLocalizationCurrent

open Filter Topology MeasureTheory
open scoped ENNReal
open PhotonLocalizationChannel RemovalState

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  {R : Gaussian.RankOneData H T} {Tr : PositiveTraceData T}

/-- Positive spectral expectations are lower semicontinuous on the full
ambient trace space, including at states of infinite energy. -/
theorem expectation_lowerSemicontinuous (E : PositiveForm Tr) :
    LowerSemicontinuous E.expectation := by
  apply lowerSemicontinuous_iSup
  intro n
  exact (ENNReal.continuous_ofReal.comp (E.truncation n).continuous).lowerSemicontinuous

/-- A pure-vector relative form bound extends to all finite-energy
positive normal operators by the actual trace-norm spectral series. -/
theorem normal_form_bound (N : NormalTraceData R) (E : PositiveForm Tr)
    (hpositive : R.positive ⊆ Tr.positive) (A : T →L[ℝ] ℝ) {c : ℝ}
    (hpure : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      |A (R.rankOne v)| ≤ c * (E.expectation (R.rankOne v)).toReal)
    {x : T} (hx : x ∈ R.positive) (hfinite : E.expectation x < ⊤) :
    |A x| ≤ c * (E.expectation x).toReal := by
  obtain ⟨v, hv⟩ := N.positive_decomposition x hx
  have he : (∑' n, E.expectation (R.rankOne (v n))) = E.expectation x := by
    rw [← E.expectation_tsum hv.summable
      (fun n => hpositive (R.rankOne_positive (v n))), hv.tsum_eq]
  have hterm (n : ℕ) : E.expectation (R.rankOne (v n)) < ⊤ :=
    (ENNReal.le_tsum n).trans_lt (he ▸ hfinite)
  have hs : HasSum (fun n => (E.expectation (R.rankOne (v n))).toReal)
      (E.expectation x).toReal := by
    have ht := ENNReal.summable_toReal (he ▸ hfinite.ne)
    have hh := ht.hasSum
    rw [← ENNReal.tsum_toReal_eq (fun n => (hterm n).ne), he] at hh
    exact hh
  simpa only [Real.norm_eq_abs] using
    (A.hasSum hv).norm_le_of_bounded (hs.mul_left c)
      (fun n => by simpa only [Real.norm_eq_abs] using hpure (v n) (hterm n))

/-- This premise concerns only bounded quadratic forms on individual
vectors. In `SpectralCurrentData` it follows from a second-moment estimate
and the scalar spectral-tail inequality. -/
structure RelativeApproximation (E : PositiveForm Tr) (J : FormObservable E) where
  rate : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ rate n
  tends_zero : Tendsto rate atTop (𝓝 0)
  pure_bound : ∀ n m, n ≤ m → ∀ v, E.expectation (R.rankOne v) < ⊤ →
    |J.approximation m (R.rankOne v) - J.approximation n (R.rankOne v)| ≤
      rate n * (E.expectation (R.rankOne v)).toReal

namespace RelativeApproximation

variable {E : PositiveForm Tr} {J : FormObservable E}
  (A : RelativeApproximation (R := R) E J)

/-- The approximation error for the full unbounded observable follows
by first extending the bounded differences and then taking their limit. -/
theorem error_bound (N : NormalTraceData R) (hpositive : R.positive ⊆ Tr.positive)
    (n : ℕ) {x : T} (hx : x ∈ R.positive) (hfinite : E.expectation x < ⊤) :
    |J.value x - J.approximation n x| ≤ A.rate n * (E.expectation x).toReal := by
  apply le_of_tendsto ((J.converges x (hpositive hx) hfinite).sub_const
    (J.approximation n x)).abs
  filter_upwards [eventually_ge_atTop n] with m hm
  exact normal_form_bound N E hpositive (J.approximation m - J.approximation n)
    (fun v hv => A.pure_bound n m hm v hv) hx hfinite

include A

/-- The exact bounded-energy passage used by `PhotonLoss.TraceData`.
The normal limit's positivity and finite energy are consequences. -/
theorem test_passage (N : NormalTraceData R) (hpositive : R.positive ⊆ Tr.positive)
    (D : PhotonLoss.LocalizationData T) (hstates : D.states ⊆ R.positive)
    (u : ℕ → T) (x : T) (B : ℝ) (hu : ∀ n, u n ∈ D.states)
    (hB : ∀ n, E.expectation (u n) ≤ ENNReal.ofReal B)
    (hlim : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun n => J.value (u n)) atTop (𝓝 (J.value x)) := by
  have hx : x ∈ R.positive :=
    hstates (D.states_closed.mem_of_tendsto hlim (Eventually.of_forall hu))
  have hxB : E.expectation x ≤ ENNReal.ofReal B :=
    PhotonLoss.LocalizationData.observable_le_of_tendsto
      (expectation_lowerSemicontinuous E) hlim hB
  have hbound {z : T} (hz : z ∈ R.positive)
      (hzB : E.expectation z ≤ ENNReal.ofReal B) (k : ℕ) :
      |J.value z - J.approximation k z| ≤ A.rate k * max B 0 := by
    apply (A.error_bound N hpositive k hz
      (hzB.trans_lt ENNReal.ofReal_lt_top)).trans
    apply mul_le_mul_of_nonneg_left _ (A.nonneg k)
    simpa only [ENNReal.toReal_ofReal'] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hzB
  have hr : Tendsto (fun k => A.rate k * max B 0) atTop (𝓝 0) := by
    simpa using A.tends_zero.mul_const (max B 0)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := (hr.eventually (gt_mem_nhds (by positivity : 0 < ε / 3))).exists
  have hkconv := ((J.approximation k).continuous.tendsto x).comp hlim
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp hkconv (ε / 3) (by positivity)
  refine ⟨n, fun m hm => ?_⟩
  have h1 := hbound (hstates (hu m)) (hB m) k
  have h3 := hbound hx hxB k
  have h2 := hn m hm
  simp only [Function.comp_def, Real.dist_eq] at h2 ⊢
  have htri := abs_add_three (J.value (u m) - J.approximation k (u m))
    (J.approximation k (u m) - J.approximation k x)
    (J.approximation k x - J.value x)
  rw [abs_sub_comm (J.approximation k x)] at htri
  have heq : (J.value (u m) - J.approximation k (u m)) +
      (J.approximation k (u m) - J.approximation k x) +
      (J.approximation k x - J.value x) = J.value (u m) - J.value x := by ring
  rw [heq] at htri
  linarith

end RelativeApproximation

/-- Bounded spectral cutoff of a real observable at level `n + 1`. -/
noncomputable def spectralCutoff (n : ℕ) (s : ℝ) : ℝ :=
  if |s| ≤ (n : ℝ) + 1 then s else 0

theorem spectralCutoff_abs_le (n : ℕ) (s : ℝ) :
    |spectralCutoff n s| ≤ (n : ℝ) + 1 := by
  unfold spectralCutoff
  split_ifs with h
  · exact h
  · simp only [abs_zero]
    positivity

/-- The tail of a first moment is bounded by its second moment. This is
why the spectral cutoff is taken in the tested observable itself. -/
theorem spectralCutoff_difference (n m : ℕ) (hnm : n ≤ m) (s : ℝ) :
    |spectralCutoff m s - spectralCutoff n s| ≤ s ^ 2 / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
  unfold spectralCutoff
  by_cases hsmall : |s| ≤ (n : ℝ) + 1
  · rw [ite_eq_left hsmall, ite_eq_left (hsmall.trans hnm')]
    simp only [sub_self, abs_zero]
    positivity
  · rw [ite_eq_right hsmall]
    split_ifs with hm
    · simp only [sub_zero]
      apply (le_div_iff₀ hn).mpr
      have habs : 0 ≤ |s| := abs_nonneg s
      nlinarith [sq_abs s, not_le.mp hsmall]
    · simp only [sub_zero, abs_zero]
      positivity

/-- A finite first-order observable has a square-form bound from its
bounded test multipliers, kinetic form bound, and bounded correction.
For the symmetric current the correction is the divergence term. -/
theorem first_order_square_bound {ι : Type*} [Fintype ι]
    (test : ι → H →L[ℂ] H) (correction : H →L[ℂ] H) (d : ι → H)
    (v j : H) {K M e : ℝ}
    (hidentity : j = (∑ i, test i (d i)) + correction v)
    (hkinetic : ∑ i, ‖d i‖ ^ 2 ≤ K * e) (hmass : ‖v‖ ^ 2 ≤ M * e) :
    ‖j‖ ^ 2 ≤ 2 * ((∑ i, ‖test i‖ ^ 2) * K + ‖correction‖ ^ 2 * M) * e := by
  have hnorm : ‖∑ i, test i (d i)‖ ≤ ∑ i, ‖test i‖ * ‖d i‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (test i).le_opNorm (d i))
  have hnorm0 : 0 ≤ ∑ i, ‖test i‖ * ‖d i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq := sq_le_sq₀ (norm_nonneg _) hnorm0 |>.mpr hnorm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖test i‖) (fun i => ‖d i‖)
  have hcoeff : 0 ≤ ∑ i, ‖test i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hprincipal : ‖∑ i, test i (d i)‖ ^ 2 ≤ (∑ i, ‖test i‖ ^ 2) * (K * e) :=
    hsq.trans (hcs.trans (mul_le_mul_of_nonneg_left hkinetic hcoeff))
  have hc := correction.le_opNorm v
  have hcsq := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hc
  have hcfinal : ‖correction v‖ ^ 2 ≤ ‖correction‖ ^ 2 * (M * e) := by
    calc
      ‖correction v‖ ^ 2 ≤ (‖correction‖ * ‖v‖) ^ 2 := hcsq
      _ = ‖correction‖ ^ 2 * ‖v‖ ^ 2 := mul_pow _ _ _
      _ ≤ ‖correction‖ ^ 2 * (M * e) :=
        mul_le_mul_of_nonneg_left hmass (sq_nonneg _)
  rw [hidentity]
  have htri := norm_add_le (∑ i, test i (d i)) (correction v)
  have htrisq := sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr htri
  nlinarith [sq_nonneg (‖∑ i, test i (d i)‖ - ‖correction v‖)]

/-- The universal pure-vector spectral measure identities for a tested
self-adjoint observable, together with its square-form comparison to the
energy. There is no state sequence or trace-limit conclusion among the
fields. The square-form comparison remains the physical operator input. -/
structure SpectralCurrentData (E : PositiveForm Tr) (J : FormObservable E) where
  measure : H → Measure ℝ
  finite : ∀ v, IsFiniteMeasure (measure v)
  pairing : ∀ n v, J.approximation n (R.rankOne v) =
    ∫ s, spectralCutoff n s ∂measure v
  square_integrable : ∀ v, E.expectation (R.rankOne v) < ⊤ →
    Integrable (fun s : ℝ => s ^ 2) (measure v)
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  square_bound : ∀ v, E.expectation (R.rankOne v) < ⊤ →
    (∫ s, s ^ 2 ∂measure v) ≤ constant * (E.expectation (R.rankOne v)).toReal

namespace SpectralCurrentData

variable {E : PositiveForm Tr} {J : FormObservable E}
  (S : SpectralCurrentData (R := R) E J)

omit [InnerProductSpace ℂ H] in
theorem cutoff_integrable (n : ℕ) (v : H) :
    Integrable (spectralCutoff n) (S.measure v) := by
  let := S.finite v
  apply (integrable_const ((n : ℝ) + 1)).mono'
  · apply Measurable.aestronglyMeasurable
    exact Measurable.ite (isClosed_le continuous_abs continuous_const).measurableSet
      measurable_id measurable_const
  · exact Eventually.of_forall fun s => by
      simpa only [Real.norm_eq_abs] using spectralCutoff_abs_le n s

/-- The scalar spectral inequality and the square-form comparison
construct the vanishing pure-vector error required by the passage proof. -/
noncomputable def relativeApproximation : RelativeApproximation (R := R) E J where
  rate n := S.constant / ((n : ℝ) + 1)
  nonneg n := div_nonneg S.constant_nonneg (by positivity)
  tends_zero := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul S.constant
  pure_bound n m hnm v hv := by
    rw [S.pairing, S.pairing, ← integral_sub (S.cutoff_integrable m v)
      (S.cutoff_integrable n v)]
    have h := norm_integral_le_of_norm_le
      (f := fun s => spectralCutoff m s - spectralCutoff n s)
      ((S.square_integrable v hv).div_const ((n : ℝ) + 1))
      (Eventually.of_forall fun s => by
        simpa only [Real.norm_eq_abs] using spectralCutoff_difference n m hnm s)
    rw [integral_div] at h
    rw [Real.norm_eq_abs] at h
    apply h.trans
    have hh := div_le_div_of_nonneg_right (S.square_bound v hv)
      (by positivity : 0 ≤ (n : ℝ) + 1)
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh

/-- A concrete first-order current supplies the square-form field of
the spectral constructor from vector identities and energy coercivity.
The spectral measure data are universal self-adjoint spectral calculus. -/
noncomputable def ofFirstOrder {ι : Type*} [Fintype ι]
    (measure : H → Measure ℝ) (hfinite : ∀ v, IsFiniteMeasure (measure v))
    (hpairing : ∀ n v, J.approximation n (R.rankOne v) =
      ∫ s, spectralCutoff n s ∂measure v)
    (hsquare : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      Integrable (fun s : ℝ => s ^ 2) (measure v))
    (current : H → H) (derivative : ι → H → H)
    (test : ι → H →L[ℂ] H) (correction : H →L[ℂ] H)
    (hcurrent : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      current v = (∑ i, test i (derivative i v)) + correction v)
    (hmoment : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      (∫ s, s ^ 2 ∂measure v) = ‖current v‖ ^ 2)
    {K M : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hkinetic : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      (∑ i, ‖derivative i v‖ ^ 2) ≤ K * (E.expectation (R.rankOne v)).toReal)
    (hmass : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      ‖v‖ ^ 2 ≤ M * (E.expectation (R.rankOne v)).toReal) :
    SpectralCurrentData (R := R) E J where
  measure := measure
  finite := hfinite
  pairing := hpairing
  square_integrable := hsquare
  constant := 2 * ((∑ i, ‖test i‖ ^ 2) * K + ‖correction‖ ^ 2 * M)
  constant_nonneg := by positivity
  square_bound v hv := by
    rw [hmoment v hv]
    exact first_order_square_bound test correction (fun i => derivative i v)
      v (current v) (hcurrent v hv) (hkinetic v hv) (hmass v hv)

include S

/-- Bounded-energy current passage from normal trace calculus, the
current spectral theorem, and the current-square form estimate. -/
theorem test_passage (N : NormalTraceData R) (hpositive : R.positive ⊆ Tr.positive)
    (D : PhotonLoss.LocalizationData T) (hstates : D.states ⊆ R.positive)
    (u : ℕ → T) (x : T) (B : ℝ) (hu : ∀ n, u n ∈ D.states)
    (hB : ∀ n, E.expectation (u n) ≤ ENNReal.ofReal B)
    (hlim : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun n => J.value (u n)) atTop (𝓝 (J.value x)) :=
  S.relativeApproximation.test_passage N hpositive D hstates u x B hu hB hlim

/-- Energy coercivity transfers passage from a controlling positive form
to the physical energy used by the attainment theorem. In particular,
the controlling form may include a positive constant shift. -/
theorem test_passage_of_control (N : NormalTraceData R)
    (hpositive : R.positive ⊆ Tr.positive) (D : PhotonLoss.LocalizationData T)
    (hstates : D.states ⊆ R.positive) (energy : T → ℝ≥0∞)
    (control : ℝ → ℝ)
    (hcontrol : ∀ B, ∀ z ∈ D.states, energy z ≤ ENNReal.ofReal B →
      E.expectation z ≤ ENNReal.ofReal (control B))
    (u : ℕ → T) (x : T) (B : ℝ) (hu : ∀ n, u n ∈ D.states)
    (hB : ∀ n, energy (u n) ≤ ENNReal.ofReal B)
    (hlim : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun n => J.value (u n)) atTop (𝓝 (J.value x)) :=
  S.test_passage N hpositive D hstates u x (control B) hu
    (fun n => hcontrol B (u n) (hu n) (hB n)) hlim

end SpectralCurrentData

end GptLean.PhotonLocalizationCurrent
