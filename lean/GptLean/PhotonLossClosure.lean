import GptLean.PhotonCompactness
import GptLean.Attainment
import GptLean.Closure

/-!
The bridge from retained trace-norm limits to the two closure inputs used
in Theorem 4.8. Extended nonnegative energies are retained on the ambient
trace space, so the normal limit is not assumed to have finite energy.

`TraceData` records standard positive-form trace lower semicontinuity,
monotone convergence, bounded-energy trace pairings, and spectral Markov
estimates. `LocalizationEstimates` separately records the PF-specific
local compactness, rough energy bound, combined truncated energy estimate,
and tested-current localization error. Neither structure assumes the
conclusion of the photon-loss lemma. The successive limits and the
coefficient-one energy comparison are proved below.

Concrete Fock space localization, form-factor estimates, and the concrete
state realization are not constructed in this file. The later
`PhotonLocalizationKernelModel` module constructs this estimate interface
from kernel, Fock-form and finite-compression witnesses. The physical
realization of those witnesses remains explicit.
-/

namespace GptLean.PhotonLoss

open Filter Topology
open scoped ENNReal

variable {X Test : Type*} [NormedAddCommGroup X]

/-- A standard lower-semicontinuous observable also permits varying bounds. -/
theorem observable_le_of_tendsto_bounds {f : X → ℝ≥0∞}
    (hf : LowerSemicontinuous f) {u : ℕ → X} {x : X}
    (hu : Tendsto u atTop (𝓝 x)) {b : ℕ → ℝ≥0∞} {B : ℝ≥0∞}
    (hb : Tendsto b atTop (𝓝 B)) (hbound : ∀ n, f (u n) ≤ b n) :
    f x ≤ B := by
  refine le_of_forall_lt_imp_le_of_dense fun y hy => ?_
  have hev : ∀ᶠ n in atTop, y < f (u n) := hu.eventually (hf x y hy)
  exact ge_of_tendsto hb (hev.mono fun n hn => hn.le.trans (hbound n))

/-- Standard trace and spectral facts, stated separately from the PF
localization estimates. `test_passage` applies to the actual bounded-energy
trace pairings after their relative operator bound has been established. -/
structure TraceData (D : LocalizationData X) (Test : Type*) where
  energy : X → ℝ≥0∞
  number : X → ℝ≥0∞
  energy_lsc : LowerSemicontinuous energy
  number_lsc : LowerSemicontinuous number
  number_decrease : ∀ m, ∀ x ∈ D.states, number (D.localize m x) ≤ number x
  tail_markov : ∀ M, ∀ x ∈ D.states, number x < ⊤ →
    D.tail M x ≤ (number x).toReal / ((M : ℝ) + 1)
  cutoff : ℕ → X → X
  cutoff_cont : ∀ l, Continuous (cutoff l)
  cutoff_tendsto : ∀ x ∈ D.states, Tendsto (fun l => cutoff l x) atTop (𝓝 x)
  truncatedEnergy : ℕ → X → ℝ≥0∞
  truncated_lsc : ∀ k, LowerSemicontinuous (truncatedEnergy k)
  energy_eq_iSup : ∀ x, energy x = ⨆ k, truncatedEnergy k x
  test : Test → X → ℝ
  test_passage : ∀ (u : ℕ → X) (x : X) (E : ℝ),
    (∀ n, u n ∈ D.states) →
    (∀ n, energy (u n) ≤ ENNReal.ofReal E) →
    Tendsto u atTop (𝓝 x) →
    ∀ t, Tendsto (fun n => test t (u n)) atTop (𝓝 (test t x))

/-- The estimate interface used by the closure proof. The later kernel/form
constructor derives it from lower-level data. The sharp bound concerns each
localized truncated form, never the retained limit. Its localization error
may depend on both truncation indices. -/
structure LocalizationEstimates (D : LocalizationData X) (T : TraceData D Test) where
  electronicTight : (ℕ → X) → Prop
  precompact : ∀ (u : ℕ → X) (E : ℝ),
    (∀ n, u n ∈ D.states) →
    (∀ n, T.energy (u n) ≤ ENNReal.ofReal E) → electronicTight u →
    ∀ m, TotallyBounded (Set.range fun n => D.localize m (u n))
  rough : ℝ → ℝ
  rough_bound : ∀ E m, ∀ x ∈ D.states,
    T.energy x ≤ ENNReal.ofReal E →
    T.energy (D.localize m x) ≤ ENNReal.ofReal (rough E)
  imsError : ℕ → ℝ
  imsError_zero : Tendsto imsError atTop (𝓝 0)
  localError : ℝ → ℕ → ℕ → ℕ → ℝ
  localError_zero : ∀ E l k, Tendsto (localError E l k) atTop (𝓝 0)
  combined_bound : ∀ E e l k m, ∀ x ∈ D.states,
    0 ≤ e → T.energy x ≤ ENNReal.ofReal E → T.energy x ≤ ENNReal.ofReal e →
    T.truncatedEnergy k (T.cutoff l (D.localize m x)) ≤
      ENNReal.ofReal (e + imsError l + localError E l k m)
  testError : ℝ → Test → ℕ → ℝ
  testError_zero : ∀ E t, Tendsto (testError E t) atTop (𝓝 0)
  test_bound : ∀ E t m, ∀ x ∈ D.states,
    T.energy x ≤ ENNReal.ofReal E →
    |T.test t (D.localize m x) - T.test t x| ≤ testError E t m

namespace TraceData

variable {D : LocalizationData X} (T : TraceData D Test)

/-- Uniform mean number implies exactly the sector-tail quantifiers used by
the retained-state construction. The cap is not needed in that construction
itself. -/
theorem sector_tight_of_number_bound {u : ℕ → X} {M : ℝ}
    (hu : ∀ n, u n ∈ D.states)
    (hM : ∀ n, T.number (u n) ≤ ENNReal.ofReal M) :
    ∀ ε > 0, ∃ K, ∀ m, ∀ᶠ n in atTop,
      D.tail K (D.localize m (u n)) ≤ ε := by
  intro ε hε
  have ht : Tendsto (fun K : ℕ => max M 0 / ((K : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (max M 0)
  obtain ⟨K, hK⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨K, fun m => Eventually.of_forall fun n => ?_⟩
  have hcap := (T.number_decrease m _ (hu n)).trans (hM n)
  have hfinite := hcap.trans_lt ENNReal.ofReal_lt_top
  apply (T.tail_markov K _ (D.localize_state m _ (hu n)) hfinite).trans
  apply le_trans _ hK.le
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa only [ENNReal.toReal_ofReal'] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hcap

end TraceData

namespace LocalizationEstimates

variable {D : LocalizationData X} {T : TraceData D Test}
  (P : LocalizationEstimates D T)

include P

/-- The sharp energy comparison uses the order prescribed in the manuscript.
First take the input-state limit, then the photon-radius limit for fixed
`l,k`, then recover all photon energy, and finally remove the electronic
cutoff. No uniformity of the error in `k` is assumed. -/
theorem retained_energy_le {u G : ℕ → X} {Γ : X} {e : ℕ → ℝ} {E L : ℝ}
    (hu : ∀ n, u n ∈ D.states)
    (hE : ∀ n, T.energy (u n) ≤ ENNReal.ofReal E)
    (he : ∀ n, T.energy (u n) ≤ ENNReal.ofReal (e n))
    (he0 : ∀ n, 0 ≤ e n)
    (helim : Tendsto e atTop (𝓝 L))
    (hG : ∀ m, Tendsto (fun n => D.localize m (u n)) atTop (𝓝 (G m)))
    (hΓmem : Γ ∈ D.states) (hΓ : Tendsto G atTop (𝓝 Γ)) :
    T.energy Γ ≤ ENNReal.ofReal L := by
  have hfirst : ∀ l k m, T.truncatedEnergy k (T.cutoff l (G m)) ≤
      ENNReal.ofReal (L + P.imsError l + P.localError E l k m) := by
    intro l k m
    apply observable_le_of_tendsto_bounds (T.truncated_lsc k)
      (((T.cutoff_cont l).tendsto _).comp (hG m))
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((helim.add_const _).add_const _))
    exact fun n => P.combined_bound E (e n) l k m _ (hu n) (he0 n) (hE n) (he n)
  have hsecond : ∀ l k, T.truncatedEnergy k (T.cutoff l Γ) ≤
      ENNReal.ofReal (L + P.imsError l) := by
    intro l k
    apply observable_le_of_tendsto_bounds (T.truncated_lsc k)
      (((T.cutoff_cont l).tendsto _).comp hΓ)
    · apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      simpa using (P.localError_zero E l k).const_add (L + P.imsError l)
    · exact hfirst l k
  have hcut : ∀ l, T.energy (T.cutoff l Γ) ≤ ENNReal.ofReal (L + P.imsError l) := by
    intro l
    rw [T.energy_eq_iSup]
    exact iSup_le (hsecond l)
  apply observable_le_of_tendsto_bounds T.energy_lsc
    (T.cutoff_tendsto Γ hΓmem) _ hcut
  apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
  simpa using P.imsError_zero.const_add L

/-- The two trace-norm limits and the vanishing localization error preserve
every tested density/current constraint. Only bounded-energy trace passage
is used, so global trace-norm continuity of the current is unnecessary. -/
theorem retained_test_eq {u G : ℕ → X} {Γ : X} {E : ℝ} {target : Test → ℝ}
    (hu : ∀ n, u n ∈ D.states)
    (hE : ∀ n, T.energy (u n) ≤ ENNReal.ofReal E)
    (htest : ∀ t, Tendsto (fun n => T.test t (u n)) atTop (𝓝 (target t)))
    (hG : ∀ m, Tendsto (fun n => D.localize m (u n)) atTop (𝓝 (G m)))
    (hGmem : ∀ m, G m ∈ D.states) (hΓ : Tendsto G atTop (𝓝 Γ)) :
    ∀ t, T.test t Γ = target t := by
  have hlocE : ∀ m n, T.energy (D.localize m (u n)) ≤ ENNReal.ofReal (P.rough E) :=
    fun m n => P.rough_bound E m _ (hu n) (hE n)
  have hGE : ∀ m, T.energy (G m) ≤ ENNReal.ofReal (P.rough E) :=
    fun m => LocalizationData.observable_le_of_tendsto T.energy_lsc (hG m) (hlocE m)
  intro t
  have hfirst : ∀ m, |T.test t (G m) - target t| ≤ P.testError E t m := by
    intro m
    apply le_of_tendsto' (((T.test_passage _ _ (P.rough E)
      (fun n => D.localize_state m _ (hu n)) (hlocE m) (hG m) t).sub (htest t)).abs)
    exact fun n => P.test_bound E t m _ (hu n) (hE n)
  have hzero : |T.test t Γ - target t| ≤ 0 :=
    le_of_tendsto_of_tendsto' (((T.test_passage G Γ (P.rough E)
      hGmem hGE hΓ t).sub_const (target t)).abs) (P.testError_zero E t) hfirst
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))

/-- The normal retained limit has the sharp energy bound, inherited number
cap, and all tested constraints. Finite energy is a conclusion whenever
`L` is real. -/
theorem exists_retained_closed [CompleteSpace X] (u : ℕ → X)
    (e : ℕ → ℝ) (target : Test → ℝ) (E L M : ℝ)
    (hu : ∀ n, u n ∈ D.states)
    (hE : ∀ n, T.energy (u n) ≤ ENNReal.ofReal E)
    (he : ∀ n, T.energy (u n) ≤ ENNReal.ofReal (e n))
    (he0 : ∀ n, 0 ≤ e n)
    (helim : Tendsto e atTop (𝓝 L))
    (hM : ∀ n, T.number (u n) ≤ ENNReal.ofReal M)
    (htight : P.electronicTight u)
    (htest : ∀ t, Tendsto (fun n => T.test t (u n)) atTop (𝓝 (target t))) :
    ∃ Γ ∈ D.states, T.energy Γ ≤ ENNReal.ofReal L ∧
      T.number Γ ≤ ENNReal.ofReal M ∧ ∀ t, T.test t Γ = target t := by
  obtain ⟨φ, hφ, G, hG, hGmem, -, Γ, hΓmem, hΓ⟩ :=
    D.exists_retained_limit u hu (P.precompact u E hu hE htight)
      (T.sector_tight_of_number_bound hu hM)
  have henergy := P.retained_energy_le (fun n => hu (φ n)) (fun n => hE (φ n))
    (fun n => he (φ n)) (fun n => he0 (φ n)) (helim.comp hφ.tendsto_atTop) hG hΓmem hΓ
  have hnumber := (D.retained_number_le T.number T.number_lsc T.number_decrease
    (fun n => hu (φ n)) hG hΓ (fun n => hM (φ n))).2
  have htests := P.retained_test_eq (fun n => hu (φ n)) (fun n => hE (φ n))
    (fun t => (htest t).comp hφ.tendsto_atTop) hG hGmem hΓ
  exact ⟨Γ, hΓmem, henergy, hnumber, htests⟩

end LocalizationEstimates

/-- Norm convergence gives uniform spatial tails. For electronic densities
in `L¹`, take `tail R ρ = ∫ {|x| > R}, |ρ x|`. The two tail hypotheses are
ordinary single-function tail convergence and the `L¹` triangle inequality.
The proof includes the finitely many early sequence terms. -/
theorem uniform_tail_bounds_of_tendsto {V : Type*} [PseudoMetricSpace V]
    (tail : ℕ → V → ℝ)
    (htail : ∀ v, Tendsto (fun R => tail R v) atTop (𝓝 0))
    (hdifference : ∀ R v w, tail R v ≤ tail R w + dist v w)
    {u : ℕ → V} {v : V} (hu : Tendsto u atTop (𝓝 v)) :
    ∀ ε > 0, ∀ᶠ R in atTop, ∀ n, tail R (u n) ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hu (ε / 2) (half_pos hε)
  have hlimit : ∀ᶠ R in atTop, tail R v < ε / 2 :=
    (htail v).eventually (gt_mem_nhds (half_pos hε))
  have hprefix : ∀ᶠ R in atTop, ∀ n : Fin N, tail R (u n) ≤ ε := by
    apply Filter.eventually_all.2
    intro n
    exact ((htail (u n)).eventually (gt_mem_nhds hε)).mono fun _ h => h.le
  filter_upwards [hlimit, hprefix] with R hR hprefixR
  intro n
  by_cases hn : n < N
  · exact hprefixR ⟨n, hn⟩
  · have hdist := hN n (Nat.le_of_not_gt hn)
    exact (hdifference R (u n) v).trans (by linarith)

/-- Realization of finite-energy ambient normal states by the state type
used in the constrained search. Tested constraints separate pairs. Norm
convergence of pairs must imply electronic tightness. In the PF application
this last fact follows from the density component converging in `L¹`. -/
structure ConstraintRealization {State Pair : Type*} [TopologicalSpace Pair]
    {D : LocalizationData X} {T : TraceData D Test}
    (P : LocalizationEstimates D T) (A : DFT.StateModel State Pair)
    (number : State → ℝ≥0∞) where
  repr : State → X
  repr_mem : ∀ s, repr s ∈ D.states
  energy_nonneg : ∀ s, 0 ≤ A.energy s
  energy_repr : ∀ s, T.energy (repr s) = ENNReal.ofReal (A.energy s)
  number_repr : ∀ s, T.number (repr s) = number s
  realize : ∀ x ∈ D.states, T.energy x < ⊤ → ∃ s, repr s = x
  pairTest : Test → Pair → ℝ
  pairTest_cont : ∀ t, Continuous (pairTest t)
  pairTest_separates : ∀ d d', (∀ t, pairTest t d = pairTest t d') → d = d'
  test_repr : ∀ t s, T.test t (repr s) = pairTest t (A.density s)
  tight_of_converges : ∀ (s : ℕ → State) (d : Pair),
    Tendsto (fun n => A.density (s n)) atTop (𝓝 d) →
    P.electronicTight (fun n => repr (s n))

namespace ConstraintRealization

variable {State Pair : Type*} [TopologicalSpace Pair] [CompleteSpace X]
  {D : LocalizationData X} {T : TraceData D Test}
  {P : LocalizationEstimates D T} {A : DFT.StateModel State Pair}
  {number : State → ℝ≥0∞} (R : ConstraintRealization P A number)

include R

/-- Varying-pair closure is derived from the retained-limit construction and
the explicit local estimates. A number bound is used only to obtain sector
tightness. -/
theorem boundedConstraintClosure : Closure.BoundedConstraintClosure A number := by
  intro s d E M hden hE hM
  have hE0 : 0 ≤ E := (R.energy_nonneg (s 0)).trans (hE 0)
  have he : ∀ n, T.energy (R.repr (s n)) ≤ ENNReal.ofReal E := by
    intro n
    rw [R.energy_repr]
    exact ENNReal.ofReal_le_ofReal (hE n)
  have hn : ∀ n, T.number (R.repr (s n)) ≤ ENNReal.ofReal M := by
    simpa only [R.number_repr] using hM
  have ht : ∀ t, Tendsto (fun n => T.test t (R.repr (s n))) atTop
      (𝓝 (R.pairTest t d)) := by
    intro t
    simpa only [R.test_repr, Function.comp_def] using ((R.pairTest_cont t).tendsto d).comp hden
  obtain ⟨Γ, hΓmem, hΓE, -, hΓtest⟩ :=
    P.exists_retained_closed (fun n => R.repr (s n)) (fun _ => E)
      (fun t => R.pairTest t d) E E M (fun n => R.repr_mem (s n)) he he (fun _ => hE0)
      tendsto_const_nhds hn (R.tight_of_converges s d hden) ht
  obtain ⟨state, hstate⟩ := R.realize Γ hΓmem (hΓE.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨state, ?_, ?_⟩
  · apply R.pairTest_separates
    intro t
    rw [← R.test_repr, hstate]
    exact hΓtest t
  · rw [← hstate, R.energy_repr] at hΓE
    exact (ENNReal.ofReal_le_ofReal_iff hE0).mp hΓE

/-- Fixed-fiber photon-loss compactness, including preservation of the mean
number cap, now follows from the same construction as varying-pair closure. -/
theorem photonLossInput (d : Pair) : Attainment.PhotonLossInput State
    (fun s => A.density s = d) A.energy number := by
  intro s L M hfeasible hbounded hM hlim
  obtain ⟨E, hE⟩ := hbounded
  have hL0 : 0 ≤ L := ge_of_tendsto hlim (Eventually.of_forall fun n =>
    R.energy_nonneg (s n))
  have hden : Tendsto (fun n => A.density (s n)) atTop (𝓝 d) := by
    simpa only [hfeasible] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => d) atTop (𝓝 d))
  have hglobal : ∀ n, T.energy (R.repr (s n)) ≤ ENNReal.ofReal E := by
    intro n
    rw [R.energy_repr]
    exact ENNReal.ofReal_le_ofReal (hE n)
  have he : ∀ n, T.energy (R.repr (s n)) ≤ ENNReal.ofReal (A.energy (s n)) := by
    intro n
    rw [R.energy_repr]
  have hn : ∀ n, T.number (R.repr (s n)) ≤ ENNReal.ofReal M := by
    simpa only [R.number_repr] using hM
  have ht : ∀ t, Tendsto (fun n => T.test t (R.repr (s n))) atTop
      (𝓝 (R.pairTest t d)) := by
    intro t
    simpa only [R.test_repr, Function.comp_def] using ((R.pairTest_cont t).tendsto d).comp hden
  obtain ⟨Γ, hΓmem, hΓE, hΓM, hΓtest⟩ :=
    P.exists_retained_closed (fun n => R.repr (s n)) (fun n => A.energy (s n))
      (fun t => R.pairTest t d) E L M (fun n => R.repr_mem (s n)) hglobal he (fun n => R.energy_nonneg (s n))
      hlim hn (R.tight_of_converges s d hden) ht
  obtain ⟨state, hstate⟩ := R.realize Γ hΓmem (hΓE.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨state, ?_, ?_, ?_⟩
  · apply R.pairTest_separates
    intro t
    rw [← R.test_repr, hstate]
    exact hΓtest t
  · rw [← hstate, R.energy_repr] at hΓE
    exact (ENNReal.ofReal_le_ofReal_iff hL0).mp hΓE
  · rwa [← hstate, R.number_repr] at hΓM

end ConstraintRealization

end GptLean.PhotonLoss
