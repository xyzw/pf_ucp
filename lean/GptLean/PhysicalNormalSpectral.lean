import GptLean.PhysicalNormalStates
import GptLean.PhotonLocalizationCurrentChannel
import GptLean.Theorem48

/-!
Normalized pure ensembles are constructed from the actual positive
normal source series. Zero source vectors use a pure state obtained from
a nonzero term of that same series. Positive-form monotone convergence
and the proved form-observable series theorem give the full energy sum.
The final spectral ensemble is a conclusion, not background data.
-/

noncomputable section

namespace GptLean.PhysicalNormalSpectral

open Filter Topology RemovalState PhotonLocalizationChannel PhysicalNormalTrace PhysicalNormalStates
open scoped ENNReal

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData H T}
  {normal : NormalTraceData R} {F : NormalFunctionalData R}
  (E : PositiveForm (positiveTrace normal F))
  (C : NormalConjugationData R) (P : H →L[ℂ] H)

omit [InnerProductSpace ℂ H] [CompleteSpace H] [CompleteSpace T] in
theorem rankOne_zero : R.rankOne (0 : H) = 0 := by
  apply norm_eq_zero.mp
  simp only [R.norm_rankOne, norm_zero, zero_pow (by decide : 2 ≠ 0)]

def normalize (v : H) (hP : P v = v) (hE : E.expectation (R.rankOne v) < ⊤)
    (hv : v ≠ 0) : Pure E P := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, ?_, ?_⟩
  · simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ hn
  · rw [map_smul, hP]
  · rw [rankOne_real_smul F, expectation_smul E (sq_nonneg _)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE

theorem normalize_rankOne (v : H) (hP : P v = v) (hE : E.expectation (R.rankOne v) < ⊤)
    (hv : v ≠ 0) :
    ‖v‖ ^ 2 • R.rankOne (normalize E P v hP hE hv).val = R.rankOne v := by
  change ‖v‖ ^ 2 • R.rankOne (((‖v‖⁻¹ : ℝ) : ℂ) • v) = R.rankOne v
  rw [rankOne_real_smul F, smul_smul]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hmul : ‖v‖ ^ 2 * (‖v‖⁻¹) ^ 2 = 1 := by field_simp
  rw [hmul, one_smul]

def sourcePure (p₀ : Pure E P) (v : H) (hP : P v = v)
    (hE : E.expectation (R.rankOne v) < ⊤) : Pure E P := by
  classical
  exact if hv : v = 0 then p₀ else normalize E P v hP hE hv

theorem sourcePure_rankOne (p₀ : Pure E P) (v : H) (hP : P v = v)
    (hE : E.expectation (R.rankOne v) < ⊤) :
    ‖v‖ ^ 2 • R.rankOne (sourcePure E P p₀ v hP hE).val = R.rankOne v := by
  by_cases hv : v = 0
  · simp only [hv, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_smul, rankOne_zero]
  · simp only [sourcePure, dite_eq_right hv]
    exact normalize_rankOne E P v hP hE hv

theorem observable_smul (J : FormObservable E) {x : T} (hx : x ∈ R.positive)
    (hE : E.expectation x < ⊤) {r : ℝ} (hr : 0 ≤ r) :
    J.value (r • x) = r * J.value x := by
  have hscaled : E.expectation (r • x) < ⊤ := by
    rw [expectation_smul E hr]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE
  apply tendsto_nhds_unique (J.converges _ (positive_smul normal F hx hr) hscaled)
  simpa only [map_smul, smul_eq_mul] using (J.converges x hx hE).const_mul r

theorem sourcePure_energy (p₀ : Pure E P) (v : H) (hP : P v = v)
    (hE : E.expectation (R.rankOne v) < ⊤) :
    ‖v‖ ^ 2 * (E.expectation (R.rankOne (sourcePure E P p₀ v hP hE).val)).toReal =
      (E.expectation (R.rankOne v)).toReal := by
  rw [← sourcePure_rankOne E P p₀ v hP hE, expectation_smul E (sq_nonneg _),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]

theorem sourcePure_observable (J : FormObservable E) (p₀ : Pure E P)
    (v : H) (hP : P v = v) (hE : E.expectation (R.rankOne v) < ⊤) :
    ‖v‖ ^ 2 * J.value (R.rankOne (sourcePure E P p₀ v hP hE).val) =
      J.value (R.rankOne v) := by
  rw [← sourcePure_rankOne E P p₀ v hP hE]
  exact (observable_smul E J (R.rankOne_positive _)
    (sourcePure E P p₀ v hP hE).property.2.2 (sq_nonneg _)).symm

theorem source_form_hasSum {v : ℕ → H} {x : T}
    (hv : HasSum (fun n => R.rankOne (v n)) x) (hx : E.expectation x < ⊤) :
    HasSum (fun n => (E.expectation (R.rankOne (v n))).toReal) (E.expectation x).toReal := by
  have he : (∑' n, E.expectation (R.rankOne (v n))) = E.expectation x := by
    rw [← E.expectation_tsum hv.summable (fun n => R.rankOne_positive (v n)), hv.tsum_eq]
  have hf (n : ℕ) : E.expectation (R.rankOne (v n)) < ⊤ :=
    (ENNReal.le_tsum n).trans_lt (he ▸ hx)
  have hs := (ENNReal.summable_toReal (he ▸ hx.ne)).hasSum
  rw [← ENNReal.tsum_toReal_eq (fun n => (hf n).ne), he] at hs
  exact hs

theorem source_form_finite {v : ℕ → H} {x : T}
    (hv : HasSum (fun n => R.rankOne (v n)) x) (hx : E.expectation x < ⊤) (n : ℕ) :
    E.expectation (R.rankOne (v n)) < ⊤ := by
  have he : (∑' n, E.expectation (R.rankOne (v n))) = E.expectation x := by
    rw [← E.expectation_tsum hv.summable (fun n => R.rankOne_positive (v n)), hv.tsum_eq]
  exact (ENNReal.le_tsum n).trans_lt (he ▸ hx)

variable {Pair Potential : Type*}

/-- The ordinary pure/mixed spectral-energy relation is obtained from
the supported source series and the standard bounded approximation of
each physical potential form. -/
theorem spectralEnsemble (hP : IsIdempotentElem P) (pair : Mixed E C P → Pair)
    (duality : Potential → Pair → ℝ)
    (observable : Potential → FormObservable E)
    (approximation : ∀ a, PhotonLocalizationCurrent.RelativeApproximation
      (R := R) E (observable a))
    (hmatch : ∀ a m, (observable a).value m.val.val = duality a (pair m))
    (m : Mixed E C P) (a : Potential) :
    Nonempty (Theorem48.SpectralEnsemble (pureModel E C P pair)
      (mixedModel E C P pair) duality m a) := by
  obtain ⟨v, hv, hs⟩ := C.supported_decomposition normal P hP m.val.property.1 m.property
  have hmass : HasSum (fun n => ‖v n‖ ^ 2) 1 := by
    have ht : R.trace m.val.val = 1 := m.val.property.2.1
    simpa only [R.trace_rankOne, ht] using R.trace.hasSum hv
  have hfinite (n : ℕ) := source_form_finite E hv m.val.property.2.2 n
  have hnz : ∃ n, v n ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : HasSum (fun _ : ℕ => (0 : ℝ)) 1 := by simpa only [h, norm_zero, zero_pow (by decide : 2 ≠ 0)] using hmass
    have := hzero.unique hasSum_zero
    norm_num at this
  obtain ⟨n₀, hn₀⟩ := hnz
  let p₀ := normalize E P (v n₀) (hs n₀) (hfinite n₀) hn₀
  let p (n : ℕ) := sourcePure E P p₀ (v n) (hs n) (hfinite n)
  have henergy := source_form_hasSum E hv m.val.property.2.2
  have hobs := PhotonLocalizationCurrent.source_value_hasSum (approximation a) normal
    (show R.positive ⊆ (positiveTrace normal F).positive from fun _ h => h)
    hv (fun n => R.rankOne_positive (v n)) m.val.property.1 m.val.property.2.2
  have hterm (n : ℕ) : ‖v n‖ ^ 2 *
      ((pureModel E C P pair).energy (p n) + duality a ((pureModel E C P pair).density (p n))) =
      (E.expectation (R.rankOne (v n))).toReal + (observable a).value (R.rankOne (v n)) := by
    change ‖v n‖ ^ 2 * ((E.expectation (R.rankOne (p n).val)).toReal +
      duality a (pair (pureToMixed E C P (p n)))) = _
    rw [← hmatch a (pureToMixed E C P (p n)), mul_add]
    change ‖v n‖ ^ 2 * (E.expectation (R.rankOne (p n).val)).toReal +
      ‖v n‖ ^ 2 * (observable a).value (R.rankOne (p n).val) = _
    rw [sourcePure_energy E P p₀ (v n) (hs n) (hfinite n),
      sourcePure_observable E P (observable a) p₀ (v n) (hs n) (hfinite n)]
  have hsum := henergy.add hobs
  rw [hmatch a m] at hsum
  refine ⟨{
    pure := p
    weight := fun n => ‖v n‖ ^ 2
    weight_nonneg := fun n => sq_nonneg _
    weight_summable := hmass.summable
    weight_sum := hmass.tsum_eq
    energy_summable := ?_
    energy_sum := ?_ }⟩
  · simpa only [hterm] using hsum.summable
  · change (∑' n, ‖v n‖ ^ 2 *
      ((pureModel E C P pair).energy (p n) + duality a ((pureModel E C P pair).density (p n)))) =
      (E.expectation m.val.val).toReal + duality a (pair m)
    simpa only [hterm] using hsum.tsum_eq

end GptLean.PhysicalNormalSpectral
