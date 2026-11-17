import GptLean.PhotonLocalizationCurrentPassage
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
The tested-current identity for the actual normal localization channel.

Current evaluation on positive source series is derived from bounded
spectral approximants. Kraus inner-product Parseval then turns a vector
graph identity into the pure-channel current formula. The discarded
vacuum term cancels from the current when it is orthogonal to the range
of the dilation. No pure or mixed current localization identity is an
input.
-/

namespace GptLean.PhotonLocalizationCurrent

open Filter Topology
open scoped ENNReal InnerProductSpace
open PhotonLocalizationChannel RemovalState

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  {R : Gaussian.RankOneData H T} {Tr : PositiveTraceData T}
  {E : PositiveForm Tr} {J : FormObservable E}

/-- Finite energy and positivity justify the full unbounded current
series for any actual trace-norm positive source expansion. -/
theorem source_value_hasSum (A : RelativeApproximation (R := R) E J)
    (N : NormalTraceData R) (hpositive : R.positive ⊆ Tr.positive)
    {z : ℕ → T} {x : T} (hz : HasSum z x)
    (hpos : ∀ n, z n ∈ R.positive) (hx : x ∈ R.positive)
    (hfinite : E.expectation x < ⊤) :
    HasSum (fun n => J.value (z n)) (J.value x) := by
  have he : (∑' n, E.expectation (z n)) = E.expectation x := by
    rw [← E.expectation_tsum hz.summable (fun n => hpositive (hpos n)), hz.tsum_eq]
  have hf (n : ℕ) : E.expectation (z n) < ⊤ :=
    (ENNReal.le_tsum n).trans_lt (he ▸ hfinite)
  have hsE : Summable (fun n => (E.expectation (z n)).toReal) :=
    ENNReal.summable_toReal (he ▸ hfinite.ne)
  have hsnorm : Summable (fun n => ‖z n‖) := by
    simpa only [Tr.norm_eq_trace (hpositive (hpos _))] using (Tr.trace.hasSum hz).summable
  let b : ℕ → ℝ := fun n =>
    ‖J.approximation 0‖ * ‖z n‖ + A.rate 0 * (E.expectation (z n)).toReal
  have hsb : Summable b := (hsnorm.mul_left _).add (hsE.mul_left _)
  have hb (m n : ℕ) : ‖J.approximation m (z n)‖ ≤ b n := by
    have hd := normal_form_bound N E hpositive (J.approximation m - J.approximation 0)
      (fun v hv => A.pure_bound 0 m (Nat.zero_le m) v hv) (hpos n) (hf n)
    have h0 := (J.approximation 0).le_opNorm (z n)
    have ht := abs_add_le (J.approximation m (z n) - J.approximation 0 (z n))
      (J.approximation 0 (z n))
    simp only [sub_apply, sub_add_cancel, Real.norm_eq_abs] at hd h0 ht ⊢
    dsimp [b]
    linarith
  have hpoint (n : ℕ) := J.converges (z n) (hpositive (hpos n)) (hf n)
  have hvaluebound (n : ℕ) : ‖J.value (z n)‖ ≤ b n :=
    le_of_tendsto' (hpoint n).norm (fun m => hb m n)
  have hsvalue : Summable (fun n => J.value (z n)) := hsb.of_norm_bounded hvaluebound
  have hlimit := tendsto_tsum_of_dominated_convergence hsb hpoint
    (Eventually.of_forall fun m n => hb m n)
  have hbounded (m : ℕ) : (∑' n, J.approximation m (z n)) = J.approximation m x :=
    ((J.approximation m).hasSum hz).tsum_eq
  have heq : (∑' n, J.value (z n)) = J.value x := by
    apply tendsto_nhds_unique hlimit
    simpa only [hbounded] using J.converges x (hpositive hx) hfinite
  exact heq ▸ hsvalue.hasSum

section Vectors

/-- A bounded electronic operator acts coordinatewise on the discarded
Fock basis. Membership in the Hilbert sum follows from its operator norm. -/
noncomputable def coordinateMap (W : H →L[ℂ] H) (v : lp (fun _ : ℕ => H) 2) :
    lp (fun _ : ℕ => H) 2 :=
  ⟨fun a => W (v a), ((lp.memℓp v).norm.const_mul ‖W‖).mono
    (fun a => W.le_opNorm (v a))⟩

@[simp] theorem coordinateMap_apply (W : H →L[ℂ] H)
    (v : lp (fun _ : ℕ => H) 2) (a : ℕ) : coordinateMap W v a = W (v a) := rfl

/-- Adjointness is transported to the Hilbert sum by coordinate Parseval. -/
theorem coordinateMap_inner [CompleteSpace H] (W : H →L[ℂ] H)
    (v w : lp (fun _ : ℕ => H) 2) :
    ⟪v, coordinateMap W w⟫_ℂ = ⟪coordinateMap W.adjoint v, w⟫_ℂ := by
  have h := lp.hasSum_inner (𝕜 := ℂ) v (coordinateMap W w)
  have h' := lp.hasSum_inner (𝕜 := ℂ) (coordinateMap W.adjoint v) w
  simp only [coordinateMap_apply, ContinuousLinearMap.adjoint_inner_left] at h'
  exact h.unique h'

/-- Electronic intertwining passes from vectors to the coordinate map. -/
theorem coordinateMap_dilation (U : KrausIsometry H) (W : H →L[ℂ] H)
    (hW : ∀ v a, U (W v) a = W (U v a)) (v : H) :
    coordinateMap W (U v) = U (W v) := by
  ext a
  exact (hW v a).symm

/-- The tested vacuum noise vanishes using orthogonality to the entire
range and the electronic adjoint intertwining. -/
theorem noise_current_zero [CompleteSpace H]
    (U : KrausIsometry H) (W : H →L[ℂ] H)
    (hW : ∀ v a, U (W.adjoint v) a = W.adjoint (U v a))
    (noise : lp (fun _ : ℕ => H) 2)
    (hnoise : ∀ w, ⟪U w, noise⟫_ℂ = 0) (v : H) :
    ⟪U v, coordinateMap W noise⟫_ℂ = 0 := by
  rw [coordinateMap_inner, coordinateMap_dilation U W.adjoint hW]
  exact hnoise _

/-- The first-order graph identity gives its tested dilation identity.
The original current keeps coefficient one, and the vacuum contribution
is retained until its orthogonality is used in the next theorem. -/
theorem tested_derivative_identity {ι : Type*} [Fintype ι]
    (U : KrausIsometry H) (test : ι → H →L[ℂ] H)
    (hintertwine : ∀ i v a, U (test i v) a = test i (U v a))
    (d field : ι → H) (noise localized : ι → lp (fun _ : ℕ => H) 2)
    (charge : ℝ)
    (hgraph : ∀ i, localized i = U (d i + (charge : ℂ) • field i) + noise i) :
    (∑ i, coordinateMap (test i) (localized i)) =
      U ((∑ i, test i (d i)) + (charge : ℂ) • ∑ i, test i (field i)) +
      ∑ i, coordinateMap (test i) (noise i) := by
  ext a
  simp only [lp.coeFn_sum, Finset.sum_apply, coordinateMap_apply, hgraph,
    lp.coeFn_add, Pi.add_apply, map_add, map_smul, hintertwine,
    Finset.sum_add_distrib, ← Finset.smul_sum, map_sum, lp.coeFn_smul, Pi.smul_apply]

/-- Only the tested field needs a small norm. This version permits a
compactly supported electronic test, even when the untested field error
has no uniform spatial bound on the entire source state. -/
theorem tested_current_correction_bound {ι : Type*} [Fintype ι]
    (v : H) (test : ι → H →L[ℂ] H) (field : ι → H) (Z : ι → ℝ)
    {charge ε B c : ℝ} (hc : 0 ≤ c)
    (hv : ‖v‖ ≤ Real.sqrt c)
    (hfield : ∀ i, ‖test i (field i)‖ ≤ Z i * ε * B * Real.sqrt c) :
    |(⟪v, (charge : ℂ) • ∑ i, test i (field i)⟫_ℂ).re| ≤
      (|charge| * (∑ i, Z i) * ε * B) * c := by
  have hsum : ‖∑ i, test i (field i)‖ ≤
      (∑ i, Z i) * ε * B * Real.sqrt c := by
    apply (norm_sum_le _ _).trans
    simpa only [Finset.sum_mul] using Finset.sum_le_sum (fun i _ => hfield i)
  have hnorm : ‖(charge : ℂ) • ∑ i, test i (field i)‖ ≤
      |charge| * (∑ i, Z i) * ε * B * Real.sqrt c := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hsum (abs_nonneg _)).trans_eq (by ring)
  have hi := (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
    (mul_le_mul hv hnorm (norm_nonneg _) (Real.sqrt_nonneg _)))
  apply hi.trans_eq
  calc
    Real.sqrt c * (|charge| * (∑ i, Z i) * ε * B * Real.sqrt c) =
        (|charge| * (∑ i, Z i) * ε * B) * (Real.sqrt c) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt hc]

/-- The tested field correction has a homogeneous energy bound. The
field estimate can be supplied by the integrated annihilation and CCR
bound used for the kinetic estimate. -/
theorem current_correction_bound {ι : Type*} [Fintype ι]
    (v : H) (test : ι → H →L[ℂ] H) (field : ι → H)
    {charge ε B c : ℝ} (hc : 0 ≤ c)
    (hv : ‖v‖ ≤ Real.sqrt c)
    (hfield : ∀ i, ‖field i‖ ≤ ε * B * Real.sqrt c) :
    |(⟪v, (charge : ℂ) • ∑ i, test i (field i)⟫_ℂ).re| ≤
      (|charge| * (∑ i, ‖test i‖) * ε * B) * c := by
  have hsum : ‖∑ i, test i (field i)‖ ≤
      (∑ i, ‖test i‖) * (ε * B * Real.sqrt c) := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => ((test i).le_opNorm (field i)).trans
      (mul_le_mul_of_nonneg_left (hfield i) (norm_nonneg _))
  have hnorm : ‖(charge : ℂ) • ∑ i, test i (field i)‖ ≤
      |charge| * (∑ i, ‖test i‖) * ε * B * Real.sqrt c := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hsum (abs_nonneg _)).trans_eq (by ring)
  have hi := (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
    (mul_le_mul hv hnorm (norm_nonneg _) (Real.sqrt_nonneg _)))
  apply hi.trans_eq
  calc
    Real.sqrt c * (|charge| * (∑ i, ‖test i‖) * ε * B * Real.sqrt c) =
        (|charge| * (∑ i, ‖test i‖) * ε * B) * (Real.sqrt c) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt hc]

end Vectors

section Channel

variable [CompleteSpace H] [CompleteSpace T] {ι : Type*} [Fintype ι]

omit [CompleteSpace H] in
/-- Current evaluation of the pure output is the Hilbert-sum pairing,
proved from the explicit Kraus series and inner-product Parseval. -/
theorem pure_current (A : RelativeApproximation (R := R) E J)
    (N : NormalTraceData R) (hpositive : R.positive ⊆ Tr.positive)
    (U : KrausIsometry H) (v : H) (tested : lp (fun _ : ℕ => H) 2)
    (hfinite : E.expectation (pure R U v) < ⊤)
    (hevaluation : ∀ a, J.value (R.rankOne (U v a)) = (⟪U v a, tested a⟫_ℂ).re) :
    J.value (pure R U v) = (⟪U v, tested⟫_ℂ).re := by
  have h := source_value_hasSum A N hpositive (pure_hasSum R U v)
    (fun a => R.rankOne_positive _) (pure_positive R U v) hfinite
  have hinner := Complex.reCLM.hasSum (lp.hasSum_inner (𝕜 := ℂ) (U v) tested)
  simp only [hevaluation] at h
  exact h.unique hinner

/-- The pure-channel current difference is derived from its graph
identity, electronic intertwining, and discarded-vacuum orthogonality. -/
theorem pure_current_difference (A : RelativeApproximation (R := R) E J)
    (N : NormalTraceData R) (hpositive : R.positive ⊆ Tr.positive)
    (U : KrausIsometry H) (v : H) (test : ι → H →L[ℂ] H)
    (hintertwine : ∀ i w a, U (test i w) a = test i (U w a))
    (hadjoint : ∀ i w a, U ((test i).adjoint w) a = (test i).adjoint (U w a))
    (d field : ι → H) (noise localized : ι → lp (fun _ : ℕ => H) 2)
    (charge : ℝ)
    (hgraph : ∀ i, localized i = U (d i + (charge : ℂ) • field i) + noise i)
    (hnoise : ∀ i w, ⟪U w, noise i⟫_ℂ = 0)
    (hfinite : E.expectation (pure R U v) < ⊤)
    (horiginal : J.value (R.rankOne v) = (⟪v, ∑ i, test i (d i)⟫_ℂ).re)
    (hevaluation : ∀ a, J.value (R.rankOne (U v a)) =
      (⟪U v a, ∑ i, test i (localized i a)⟫_ℂ).re) :
    J.value (pure R U v) - J.value (R.rankOne v) =
      (⟪v, (charge : ℂ) • ∑ i, test i (field i)⟫_ℂ).re := by
  have hp := pure_current A N hpositive U v
    (∑ i, coordinateMap (test i) (localized i)) hfinite
    (fun a => by simpa only [lp.coeFn_sum, Finset.sum_apply, coordinateMap_apply]
      using hevaluation a)
  rw [tested_derivative_identity U test hintertwine d field noise localized charge hgraph,
    inner_add_right, U.inner_map_map, inner_add_right] at hp
  have hz : ⟪U v, ∑ i, coordinateMap (test i) (noise i)⟫_ℂ = 0 := by
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro i _
    exact noise_current_zero U (test i) (hadjoint i) (noise i) (hnoise i) v
  rw [hz, add_zero, Complex.add_re] at hp
  rw [hp, horiginal]
  ring

omit [CompleteSpace H] in
/-- A proved pure current identity lifts to the actual mixed output.
The correction series is summable before it is evaluated. -/
theorem channel_current_difference (A : RelativeApproximation (R := R) E J)
    (N : NormalTraceData R) (hpositive : R.positive ⊆ Tr.positive)
    (U : KrausIsometry H) {v : ℕ → H} {x : T}
    (hsource : HasSum (fun n => R.rankOne (v n)) x) (hx : x ∈ R.positive)
    (hin : E.expectation x < ⊤) (hout : E.expectation (N.extend U x) < ⊤)
    (correction : ℕ → ℝ)
    (hidentity : ∀ n, J.value (pure R U (v n)) - J.value (R.rankOne (v n)) = correction n) :
    HasSum correction (J.value (N.extend U x) - J.value x) := by
  have h1 := source_value_hasSum A N hpositive hsource
    (fun n => R.rankOne_positive _) hx hin
  have h2 := source_value_hasSum A N hpositive (N.extend_hasSum U hsource)
    (fun n => pure_positive R U _) (N.positive U hx) hout
  simpa only [hidentity] using h2.sub h1

omit [CompleteSpace H] in
/-- Pure homogeneous current estimates lift to the normal source series
without a photon-number bound. The only output-finiteness input is the
coarse form bound proved separately for the channel. -/
theorem channel_current_bound (A : RelativeApproximation (R := R) E J)
    (N : NormalTraceData R) (hpositive : R.positive ⊆ Tr.positive)
    (U : KrausIsometry H) {x : T} (hx : x ∈ R.positive)
    (hin : E.expectation x < ⊤) (hout : E.expectation (N.extend U x) < ⊤)
    {C : ℝ}
    (hvector : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      |J.value (pure R U v) - J.value (R.rankOne v)| ≤
        C * (E.expectation (R.rankOne v)).toReal) :
    |J.value (N.extend U x) - J.value x| ≤ C * (E.expectation x).toReal := by
  obtain ⟨v, hv⟩ := N.positive_decomposition x hx
  have he : (∑' n, E.expectation (R.rankOne (v n))) = E.expectation x := by
    rw [← E.expectation_tsum hv.summable
      (fun n => hpositive (R.rankOne_positive (v n))), hv.tsum_eq]
  have hf (n : ℕ) : E.expectation (R.rankOne (v n)) < ⊤ :=
    (ENNReal.le_tsum n).trans_lt (he ▸ hin)
  have hs := (ENNReal.summable_toReal (he ▸ hin.ne)).hasSum
  rw [← ENNReal.tsum_toReal_eq (fun n => (hf n).ne), he] at hs
  have hdiff := channel_current_difference A N hpositive U hv hx hin hout
    (fun n => J.value (pure R U (v n)) - J.value (R.rankOne (v n))) (fun n => rfl)
  simpa only [Real.norm_eq_abs] using hdiff.norm_le_of_bounded (hs.mul_left C)
    (fun n => by simpa only [Real.norm_eq_abs] using hvector (v n) (hf n))

end Channel

end GptLean.PhotonLocalizationCurrent
