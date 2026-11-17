import GptLean.PhotonLocalizationCurrentPassage
import GptLean.PhotonLocalizationNormalTrace
import GptLean.PhotonLocalizationCurrentChannel

/-!
Current passage from energy spectral cutoffs and symmetry on the form
domain. The tested current need not have a self-adjoint spectral
realization. The proof uses its graph action only on finite-energy
vectors, together with bounded compressed trace pairings.
-/

namespace GptLean.PhotonLocalizationCurrent

open Filter Topology
open scoped ENNReal InnerProductSpace
open PhotonLocalizationChannel RemovalState

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  {R : Gaussian.RankOneData H T} {Tr : PositiveTraceData T}
  {E : PositiveForm Tr} {J : FormObservable E}

/-- The energy-cutoff square-root tail. -/
noncomputable def energyTail (n : ℕ) : ℝ := Real.sqrt (1 / ((n : ℝ) + 1))

theorem energyTail_nonneg (n : ℕ) : 0 ≤ energyTail n := Real.sqrt_nonneg _

theorem energyTail_antitone : Antitone energyTail := by
  intro n m hnm
  apply Real.sqrt_le_sqrt
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n : ℝ) + 1)
  exact_mod_cast Nat.add_le_add_right hnm 1

theorem energyTail_zero : Tendsto energyTail atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => Real.sqrt (1 / ((n : ℝ) + 1))) atTop (𝓝 0)
  simpa only [energyTail, Function.comp_def, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

omit [InnerProductSpace ℂ H] in
/-- The usual squared spectral-tail estimate supplies the norm tail
used by the current argument. -/
theorem energy_tail_norm (n : ℕ) (v p : H) {e : ℝ} (he : 0 ≤ e)
    (htail : ‖v - p‖ ^ 2 ≤ e / ((n : ℝ) + 1)) :
    ‖v - p‖ ≤ Real.sqrt e * energyTail n := by
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (energyTail_nonneg n))
  rw [mul_pow, Real.sq_sqrt he]
  have hlevel : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  simpa only [energyTail, Real.sq_sqrt hlevel, mul_one_div] using htail

/-- Symmetry moves the derivative in the second cross term onto the
cutoff vector. Both resulting factors are bounded by the energy norm. -/
theorem current_projection_error (v p jv jp : H) {C e δ : ℝ}
    (he : 0 ≤ e) (hδ : 0 ≤ δ)
    (hsym : ⟪p, jv⟫_ℂ = ⟪jp, v⟫_ℂ)
    (htail : ‖v - p‖ ≤ Real.sqrt e * δ)
    (hjv : ‖jv‖ ≤ C * Real.sqrt e) (hjp : ‖jp‖ ≤ C * Real.sqrt e) :
    |(⟪v, jv⟫_ℂ).re - (⟪p, jp⟫_ℂ).re| ≤ 2 * C * δ * e := by
  have hre (a b : H) : (⟪a, b⟫_ℂ).re = (⟪b, a⟫_ℂ).re :=
    inner_re_symm (𝕜 := ℂ) a b
  have hidentity : (⟪v, jv⟫_ℂ).re - (⟪p, jp⟫_ℂ).re =
      (⟪v - p, jv⟫_ℂ).re + (⟪jp, v - p⟫_ℂ).re := by
    rw [inner_sub_left, inner_sub_right, Complex.sub_re, Complex.sub_re, ← hsym,
      hre jp p]
    ring
  have h1 : |(⟪v - p, jv⟫_ℂ).re| ≤ C * δ * e := by
    apply ((Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul htail hjv (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hδ)))).trans_eq
    calc
      (Real.sqrt e * δ) * (C * Real.sqrt e) = C * δ * (Real.sqrt e) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt he]
  have h2 : |(⟪jp, v - p⟫_ℂ).re| ≤ C * δ * e := by
    rw [hre jp (v - p)]
    apply ((Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul htail hjp (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hδ)))).trans_eq
    calc
      (Real.sqrt e * δ) * (C * Real.sqrt e) = C * δ * (Real.sqrt e) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt he]
  rw [hidentity]
  exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

/-- The first-order square estimate supplies the current graph norm
bound required by the energy spectral-cutoff argument. -/
theorem first_order_current_norm_bound {ι : Type*} [Fintype ι]
    (test : ι → H →L[ℂ] H) (correction : H →L[ℂ] H) (d : ι → H)
    (v j : H) {K M e : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (he : 0 ≤ e)
    (hidentity : j = (∑ i, test i (d i)) + correction v)
    (hkinetic : ∑ i, ‖d i‖ ^ 2 ≤ K * e) (hmass : ‖v‖ ^ 2 ≤ M * e) :
    ‖j‖ ≤ Real.sqrt (2 * ((∑ i, ‖test i‖ ^ 2) * K + ‖correction‖ ^ 2 * M)) *
      Real.sqrt e := by
  have hc : 0 ≤ 2 * ((∑ i, ‖test i‖ ^ 2) * K + ‖correction‖ ^ 2 * M) := by positivity
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  simpa only [mul_pow, Real.sq_sqrt hc, Real.sq_sqrt he] using
    first_order_square_bound test correction d v j hidentity hkinetic hmass

/-- The bounded compressed current is evaluated through the actual
normal trace pairing. The second map represents the current applied to
the energy-cutoff vector. -/
noncomputable def compressedCurrentApproximation [CompleteSpace H]
    (F : NormalFunctionalData R) (P L : H →L[ℂ] H) : T →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (((ContinuousLinearMap.apply ℂ ℂ (P.adjoint.comp L)).restrictScalars ℝ).comp F.repr)

/-- Rank-one evaluation of the normal pairing supplies the compressed
quadratic form, so that this pairing need not be an extra trace identity. -/
theorem compressedCurrentApproximation_rankOne [CompleteSpace H]
    (F : NormalFunctionalData R) (P L : H →L[ℂ] H) (v : H) :
    compressedCurrentApproximation F P L (R.rankOne v) = (⟪P v, L v⟫_ℂ).re := by
  change (F.repr (R.rankOne v) (P.adjoint.comp L)).re = _
  rw [F.rankOne]
  change (⟪v, P.adjoint (L v)⟫_ℂ).re = _
  rw [ContinuousLinearMap.adjoint_inner_right]

/-- Standard energy spectral-cutoff facts and the actual symmetric
current graph action. Only the positive energy operator is spectrally
resolved. The current action is controlled on the energy form domain.
Bounded compressed trace pairings are identified on pure vectors. -/
structure EnergyCutoffCurrentData (E : PositiveForm Tr) (J : FormObservable E) where
  current : H → H
  cutoff : ℕ → H →L[ℂ] H
  pairing : ∀ n v, J.approximation n (R.rankOne v) =
    (⟪cutoff n v, current (cutoff n v)⟫_ℂ).re
  symmetry : ∀ v w, E.expectation (R.rankOne v) < ⊤ →
    E.expectation (R.rankOne w) < ⊤ →
    ⟪v, current w⟫_ℂ = ⟪current v, w⟫_ℂ
  contractive : ∀ n v, E.expectation (R.rankOne v) < ⊤ →
    E.expectation (R.rankOne (cutoff n v)) ≤ E.expectation (R.rankOne v)
  tail : ∀ n v, E.expectation (R.rankOne v) < ⊤ →
    ‖v - cutoff n v‖ ≤ Real.sqrt (E.expectation (R.rankOne v)).toReal * energyTail n
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  current_bound : ∀ v, E.expectation (R.rankOne v) < ⊤ →
    ‖current v‖ ≤ constant * Real.sqrt (E.expectation (R.rankOne v)).toReal

namespace EnergyCutoffCurrentData

variable (S : EnergyCutoffCurrentData (R := R) E J)

/-- The compressed current has a quantitative pure-vector error with
rate twice the energy spectral tail. -/
theorem pure_error (n : ℕ) (v : H) (hv : E.expectation (R.rankOne v) < ⊤) :
    |(⟪v, S.current v⟫_ℂ).re - J.approximation n (R.rankOne v)| ≤
      2 * S.constant * energyTail n * (E.expectation (R.rankOne v)).toReal := by
  have hcut := S.contractive n v hv
  have hfinite := hcut.trans_lt hv
  rw [S.pairing]
  apply current_projection_error v (S.cutoff n v) (S.current v) (S.current (S.cutoff n v))
    ENNReal.toReal_nonneg (energyTail_nonneg n) (S.symmetry _ _ hfinite hv)
    (S.tail n v hv) (S.current_bound v hv)
  exact (S.current_bound _ hfinite).trans
    (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (ENNReal.toReal_mono hv.ne hcut)) S.constant_nonneg)

/-- Differences of bounded energy-compressed currents satisfy the
relative approximation interface. No spectral theorem for the current
is invoked. -/
noncomputable def relativeApproximation : RelativeApproximation (R := R) E J where
  rate n := 4 * S.constant * energyTail n
  nonneg n := mul_nonneg (mul_nonneg (by norm_num) S.constant_nonneg) (energyTail_nonneg n)
  tends_zero := by simpa using energyTail_zero.const_mul (4 * S.constant)
  pure_bound n m hnm v hv := by
    have hm := S.pure_error m v hv
    have hn := S.pure_error n v hv
    have hr : 2 * S.constant * energyTail m * (E.expectation (R.rankOne v)).toReal ≤
        2 * S.constant * energyTail n * (E.expectation (R.rankOne v)).toReal :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (energyTail_antitone hnm)
          (mul_nonneg (by norm_num) S.constant_nonneg)) ENNReal.toReal_nonneg
    calc
      |J.approximation m (R.rankOne v) - J.approximation n (R.rankOne v)| =
          |(J.approximation m (R.rankOne v) - (⟪v, S.current v⟫_ℂ).re) +
            ((⟪v, S.current v⟫_ℂ).re - J.approximation n (R.rankOne v))| := by congr 1; ring
      _ ≤ |J.approximation m (R.rankOne v) - (⟪v, S.current v⟫_ℂ).re| +
          |(⟪v, S.current v⟫_ℂ).re - J.approximation n (R.rankOne v)| := abs_add_le _ _
      _ ≤ (2 * S.constant * energyTail n * (E.expectation (R.rankOne v)).toReal) +
          (2 * S.constant * energyTail n * (E.expectation (R.rankOne v)).toReal) := by
        rw [abs_sub_comm (J.approximation m (R.rankOne v))]
        exact add_le_add (hm.trans hr) hn
      _ = _ := by ring

/-- The value of the unbounded normal observable on a finite-energy pure
state is its symmetric current graph pairing. This follows from the
bounded compression identity and the proved vanishing error. -/
theorem pure_value (hpositive : R.positive ⊆ Tr.positive)
    (v : H) (hv : E.expectation (R.rankOne v) < ⊤) :
    J.value (R.rankOne v) = (⟪v, S.current v⟫_ℂ).re := by
  have hzero : Tendsto (fun n =>
      2 * S.constant * energyTail n * (E.expectation (R.rankOne v)).toReal) atTop (𝓝 0) := by
    simpa using (energyTail_zero.const_mul (2 * S.constant)).mul_const
      (E.expectation (R.rankOne v)).toReal
  have hlim := ((J.converges (R.rankOne v) (hpositive (R.rankOne_positive v)) hv).const_sub
    (⟪v, S.current v⟫_ℂ).re).abs
  have hle := le_of_tendsto_of_tendsto' hlim hzero (fun n => S.pure_error n v hv)
  exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))).symm

/-- The energy-cutoff realization supplies the pure current evaluation
fields in the channel theorem. Only the actual first-order graph actions
before and after the dilation remain to be identified. -/
theorem pure_channel_difference [CompleteSpace H] [CompleteSpace T]
    {ι : Type*} [Fintype ι]
    (N : NormalTraceData R) (hpositive : R.positive ⊆ Tr.positive)
    (U : KrausIsometry H) (v : H) (test : ι → H →L[ℂ] H)
    (hintertwine : ∀ i w a, U (test i w) a = test i (U w a))
    (hadjoint : ∀ i w a, U ((test i).adjoint w) a = (test i).adjoint (U w a))
    (d field : ι → H) (noise localized : ι → lp (fun _ : ℕ => H) 2)
    (charge : ℝ)
    (hgraph : ∀ i, localized i = U (d i + (charge : ℂ) • field i) + noise i)
    (hnoise : ∀ i w, ⟪U w, noise i⟫_ℂ = 0)
    (hin : E.expectation (R.rankOne v) < ⊤)
    (hout : E.expectation (pure R U v) < ⊤)
    (horiginal : S.current v = ∑ i, test i (d i))
    (hlocalized : ∀ a, S.current (U v a) = ∑ i, test i (localized i a)) :
    J.value (pure R U v) - J.value (R.rankOne v) =
      (⟪v, (charge : ℂ) • ∑ i, test i (field i)⟫_ℂ).re := by
  have hterm (a : ℕ) : E.expectation (R.rankOne (U v a)) < ⊤ := by
    apply (ENNReal.le_tsum a).trans_lt
    rwa [← NormalTraceData.pure_expectation E hpositive U v]
  apply pure_current_difference S.relativeApproximation N hpositive U v test
    hintertwine hadjoint d field noise localized charge hgraph hnoise hout
  · rw [S.pure_value hpositive v hin, horiginal]
  · intro a
    rw [S.pure_value hpositive (U v a) (hterm a), hlocalized a]

include S in
/-- The exact bounded-energy current passage follows using only energy
spectral calculus, graph symmetry, and normal trace calculus. -/
theorem test_passage (N : NormalTraceData R) (hpositive : R.positive ⊆ Tr.positive)
    (D : PhotonLoss.LocalizationData T) (hstates : D.states ⊆ R.positive)
    (u : ℕ → T) (x : T) (B : ℝ) (hu : ∀ n, u n ∈ D.states)
    (hB : ∀ n, E.expectation (u n) ≤ ENNReal.ofReal B)
    (hlim : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun n => J.value (u n)) atTop (𝓝 (J.value x)) :=
  S.relativeApproximation.test_passage N hpositive D hstates u x B hu hB hlim

include S in
/-- A shifted controlling energy can be used while the final trace data
retain the physical energy functional. -/
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

end EnergyCutoffCurrentData

end GptLean.PhotonLocalizationCurrent
