import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
The quantitative contradiction in the current `prop-pure-nonattainment`.

The current manuscript uses thin elliptic loops. It does not use the older
Gaussian-vorticity construction in `claude_lean`. This file checks radiation
energy forcing, the two-scale photon-number limit, the winding contradiction,
and existence of a representable pair without a pure minimizer.

The actual thin-loop states, PF energy estimates, infrared optimizer bound,
and extraction of a nonvanishing vacuum-component loop are paper-specific
bridge hypotheses. They are not standard facts silently imported as axioms.
Integer winding for a nonvanishing scalar loop is explicitly separated as
the permitted standard topological input.
-/

namespace GptLean.Nonattainment

open Filter Topology

/-- The energy comparison in step 5 forces a quantitative radiation bound. -/
theorem radiation_bound {E δ gap : ℝ} (hE : 0 ≤ E)
    (h : E - δ * (1 + Real.sqrt E) ≤ gap) :
    E ≤ 2 * gap + 2 * δ + δ ^ 2 := by
  have hy : δ * Real.sqrt E ≤ E / 2 + δ ^ 2 / 2 := by
    nlinarith [sq_nonneg (Real.sqrt E - δ), Real.sq_sqrt hE]
  nlinarith

/-- No prior bound on the radiation energies is needed. -/
theorem radiation_tendsto_zero {E δ gap : ℕ → ℝ}
    (hE : ∀ n, 0 ≤ E n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hgap : Tendsto gap atTop (𝓝 0))
    (h : ∀ n, E n - δ n * (1 + Real.sqrt (E n)) ≤ gap n) :
    Tendsto E atTop (𝓝 0) := by
  apply squeeze_zero hE (fun n => radiation_bound (hE n) (h n))
  simpa using ((hgap.const_mul 2).add (hδ.const_mul 2)).add (hδ.pow 2)

/-- First fix a frequency cutoff, send the sequence index to infinity,
then send the cutoff to zero. Here `soft m` is the optimizer infrared
number bound and `κ m` is any positive sequence of permitted cutoffs. -/
theorem depletion_tendsto_zero {p E soft κ fieldError : ℕ → ℝ}
    (hp : ∀ n, 0 ≤ p n) (hκ : ∀ m, 0 < κ m)
    (hE : Tendsto E atTop (𝓝 0)) (hs : Tendsto soft atTop (𝓝 0))
    (hfield : Tendsto fieldError atTop (𝓝 0))
    (hbound : ∀ m n, p n ≤ soft m + E n / κ m + fieldError n) :
    Tendsto p atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨m, hm⟩ := (hs.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by
    linarith))).exists
  have hfixed : Tendsto (fun n => E n / κ m + fieldError n) atTop (𝓝 0) := by
    simpa using (hE.div tendsto_const_nhds (hκ m).ne').add hfield
  have hevent : ∀ᶠ n in atTop, E n / κ m + fieldError n < ε / 2 := by
    exact hfixed.eventually
      (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hp n)]
  linarith [hbound m n, hN n hn]

/-- Half a circulation quantum stays at least `π` from every integer
multiple of the full circulation quantum. -/
theorem half_quantum_gap (m : ℤ) :
    Real.pi ≤ |Real.pi - 2 * Real.pi * (m : ℝ)| := by
  rcases le_or_gt m 0 with hm | hm
  · have hm' : (m : ℝ) ≤ 0 := by exact_mod_cast hm
    have hmul : 2 * Real.pi * (m : ℝ) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hm'
    rw [abs_of_nonneg (by linarith [Real.pi_pos])]
    linarith
  · have hm' : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (show (1 : ℤ) ≤ m from hm)
    have hmul : 2 * Real.pi ≤ 2 * Real.pi * (m : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hm' (show 0 ≤ 2 * Real.pi by positivity)
    rw [abs_of_nonpos (by linarith [Real.pi_pos])]
    linarith

/-- The perturbed half-quantum estimate used for every Fourier mode in
Step 3. Taking the infimum over integer modes gives the magnetic-circle
spectral lower bound once the circle form has been diagonalized. -/
theorem perturbed_half_quantum_sq (x : ℝ) (m : ℤ) :
    Real.pi ^ 2 - 2 * Real.pi * |x| ≤
      |Real.pi + x - 2 * Real.pi * (m : ℝ)| ^ 2 := by
  have htri : Real.pi ≤ |Real.pi + x - 2 * Real.pi * (m : ℝ)| + |x| := by
    calc
      Real.pi ≤ |Real.pi - 2 * Real.pi * (m : ℝ)| := half_quantum_gap m
      _ = |(Real.pi + x - 2 * Real.pi * (m : ℝ)) - x| := by
        congr 1
        ring
      _ ≤ |Real.pi + x - 2 * Real.pi * (m : ℝ)| + |x| := abs_sub _ _
  by_cases hx : |x| ≤ Real.pi
  · have hsq : (Real.pi - |x|) ^ 2 ≤
        |Real.pi + x - 2 * Real.pi * (m : ℝ)| ^ 2 := by
      exact pow_le_pow_left₀ (sub_nonneg.mpr hx) (by linarith) 2
    nlinarith [sq_nonneg |x|]
  · have hprod : Real.pi ^ 2 ≤ Real.pi * |x| := by
      nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr (le_of_not_ge hx))]
    nlinarith [sq_nonneg |Real.pi + x - 2 * Real.pi * (m : ℝ)|,
      sq_nonneg Real.pi]

/-- A circulation cannot be simultaneously close to `π` and an integer
multiple of `2π` when the sum of errors is below `π`. -/
theorem circulation_impossible {c phase a b : ℝ}
    (hhalf : |c - Real.pi| ≤ a) (hphase : |c - phase| ≤ b)
    (hquantized : ∃ m : ℤ, phase = 2 * Real.pi * (m : ℝ))
    (hsmall : a + b < Real.pi) : False := by
  obtain ⟨m, rfl⟩ := hquantized
  have htri := abs_sub_le Real.pi c (2 * Real.pi * (m : ℝ))
  rw [abs_sub_comm Real.pi c] at htri
  have hgap := half_quantum_gap m
  linarith

/-- The one-dimensional Sobolev estimate for the vacuum defect in step 6. -/
noncomputable def vacuumDefect (C p : ℝ) : ℝ :=
  3 * p + 6 * Real.sqrt (C * p)

/-- The error comparing the full Berry circulation with the scalar
vacuum-component phase. This uses `k ≤ 3C` and perpendicular mass `≤ 3p`. -/
noncomputable def windingError (C p : ℝ) : ℝ :=
  Real.sqrt 2 * vacuumDefect C p * Real.sqrt (3 * C) +
    Real.sqrt (3 * p) * Real.sqrt (3 * C)

theorem vacuumDefect_tendsto {p : ℕ → ℝ} (C : ℝ)
    (hp : Tendsto p atTop (𝓝 0)) :
    Tendsto (fun n => vacuumDefect C (p n)) atTop (𝓝 0) := by
  have hc : Continuous (vacuumDefect C) := by
    unfold vacuumDefect
    fun_prop
  simpa [Function.comp_def, vacuumDefect] using (hc.tendsto 0).comp hp

theorem windingError_tendsto {p : ℕ → ℝ} (C : ℝ)
    (hp : Tendsto p atTop (𝓝 0)) :
    Tendsto (fun n => windingError C (p n)) atTop (𝓝 0) := by
  have hc : Continuous (windingError C) := by
    unfold windingError vacuumDefect
    fun_prop
  simpa [Function.comp_def, windingError, vacuumDefect] using (hc.tendsto 0).comp hp

/-- There is no sequence of loops satisfying all the final estimates of
step 6. `phaseQuantized` is the standard winding theorem. `loopExtraction`
contains the paper-specific current identity and analytic loop estimates.
The type `Loop` can later be instantiated by nonvanishing Sobolev loops. -/
theorem no_loop_sequence {Loop : Type*} (Nonvanishing : Loop → Prop)
    (phaseIntegral : Loop → ℝ)
    (phaseQuantized : ∀ u, Nonvanishing u →
      ∃ m : ℤ, phaseIntegral u = 2 * Real.pi * (m : ℝ))
    {p : ℕ → ℝ} (C : ℝ) (hp : Tendsto p atTop (𝓝 0))
    (loopExtraction : ∀ n, vacuumDefect C (p n) ≤ 1 / 2 →
      ∃ u : Loop, Nonvanishing u ∧ ∃ c : ℝ,
        |c - Real.pi| ≤ 3 * p n ∧
        |c - phaseIntegral u| ≤ windingError C (p n)) : False := by
  have hd : ∀ᶠ n in atTop, vacuumDefect C (p n) < 1 / 2 :=
    (vacuumDefect_tendsto C hp).eventually (gt_mem_nhds (by norm_num))
  have he : Tendsto (fun n => 3 * p n + windingError C (p n)) atTop (𝓝 0) := by
    simpa using (hp.const_mul 3).add (windingError_tendsto C hp)
  obtain ⟨n, hn, hsmall⟩ := (hd.and (he.eventually (gt_mem_nhds Real.pi_pos))).exists
  obtain ⟨u, hu, c, hhalf, hphase⟩ := loopExtraction n hn.le
  exact circulation_impossible hhalf hphase (phaseQuantized u hu) hsmall

/-- Conditional existence theorem for the *current* thin-loop construction.
Every index is representable. If every index had a pure minimizer, choose
one at each index. The energy estimate forces its radiation to zero, the
infrared estimate forces its vacuum depletion to zero, and the extracted
loop contradicts integer winding. Thus at least one representable pair
has no pure minimizer.

`energyComparison`, `photonBound`, and `loopExtraction` are explicit
paper-specific obligations, not established PF background. In particular
the existence of the actual thin-loop states is supplied by `hrepresentable`.
-/
theorem exists_pair_without_pure_minimizer
    {State Pair Loop : Type*} (pair : ℕ → Pair)
    (Representable : Pair → Prop) (PureMinimizer : Pair → State → Prop)
    (hrepresentable : ∀ n, Representable (pair n))
    (radiation : State → ℝ) (depletion : ℕ → State → ℝ)
    (δ gap soft κ fieldError : ℕ → ℝ) (C : ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hgap : Tendsto gap atTop (𝓝 0))
    (hsoft : Tendsto soft atTop (𝓝 0)) (hκ : ∀ m, 0 < κ m)
    (hfield : Tendsto fieldError atTop (𝓝 0))
    (radiationNonneg : ∀ n s, PureMinimizer (pair n) s → 0 ≤ radiation s)
    (depletionNonneg : ∀ n s, PureMinimizer (pair n) s → 0 ≤ depletion n s)
    (energyComparison : ∀ n s, PureMinimizer (pair n) s →
      radiation s - δ n * (1 + Real.sqrt (radiation s)) ≤ gap n)
    (photonBound : ∀ m n s, PureMinimizer (pair n) s →
      depletion n s ≤ soft m + radiation s / κ m + fieldError n)
    (Nonvanishing : Loop → Prop) (phaseIntegral : Loop → ℝ)
    (phaseQuantized : ∀ u, Nonvanishing u →
      ∃ m : ℤ, phaseIntegral u = 2 * Real.pi * (m : ℝ))
    (loopExtraction : ∀ n s, PureMinimizer (pair n) s →
      vacuumDefect C (depletion n s) ≤ 1 / 2 →
      ∃ u : Loop, Nonvanishing u ∧ ∃ c : ℝ,
        |c - Real.pi| ≤ 3 * depletion n s ∧
        |c - phaseIntegral u| ≤ windingError C (depletion n s)) :
    ∃ n, Representable (pair n) ∧ ¬ ∃ s, PureMinimizer (pair n) s := by
  classical
  by_contra hnone
  have hex : ∀ n, ∃ s, PureMinimizer (pair n) s := by
    intro n
    by_contra h
    exact hnone ⟨n, hrepresentable n, h⟩
  choose state hstate using hex
  have hE : Tendsto (fun n => radiation (state n)) atTop (𝓝 0) :=
    radiation_tendsto_zero (fun n => radiationNonneg n _ (hstate n)) hδ hgap
      (fun n => energyComparison n _ (hstate n))
  have hp : Tendsto (fun n => depletion n (state n)) atTop (𝓝 0) :=
    depletion_tendsto_zero (fun n => depletionNonneg n _ (hstate n)) hκ hE hsoft hfield
      (fun m n => photonBound m n _ (hstate n))
  exact no_loop_sequence Nonvanishing phaseIntegral phaseQuantized C hp
    (fun n => loopExtraction n _ (hstate n))

/-- Under the same explicit analytic hypotheses, every sufficiently late pair
has no pure minimizer. This is the stronger conclusion at the end of Step 6.
If minimizers existed at arbitrarily large indices, a strictly increasing
subsequence would retain all the limits and contradict the existence theorem.
-/
theorem eventually_pair_without_pure_minimizer
    {State Pair Loop : Type*} (pair : ℕ → Pair)
    (Representable : Pair → Prop) (PureMinimizer : Pair → State → Prop)
    (hrepresentable : ∀ n, Representable (pair n))
    (radiation : State → ℝ) (depletion : ℕ → State → ℝ)
    (δ gap soft κ fieldError : ℕ → ℝ) (C : ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hgap : Tendsto gap atTop (𝓝 0))
    (hsoft : Tendsto soft atTop (𝓝 0)) (hκ : ∀ m, 0 < κ m)
    (hfield : Tendsto fieldError atTop (𝓝 0))
    (radiationNonneg : ∀ n s, PureMinimizer (pair n) s → 0 ≤ radiation s)
    (depletionNonneg : ∀ n s, PureMinimizer (pair n) s → 0 ≤ depletion n s)
    (energyComparison : ∀ n s, PureMinimizer (pair n) s →
      radiation s - δ n * (1 + Real.sqrt (radiation s)) ≤ gap n)
    (photonBound : ∀ m n s, PureMinimizer (pair n) s →
      depletion n s ≤ soft m + radiation s / κ m + fieldError n)
    (Nonvanishing : Loop → Prop) (phaseIntegral : Loop → ℝ)
    (phaseQuantized : ∀ u, Nonvanishing u →
      ∃ m : ℤ, phaseIntegral u = 2 * Real.pi * (m : ℝ))
    (loopExtraction : ∀ n s, PureMinimizer (pair n) s →
      vacuumDefect C (depletion n s) ≤ 1 / 2 →
      ∃ u : Loop, Nonvanishing u ∧ ∃ c : ℝ,
        |c - Real.pi| ≤ 3 * depletion n s ∧
        |c - phaseIntegral u| ≤ windingError C (depletion n s)) :
    ∀ᶠ n in atTop, Representable (pair n) ∧ ¬ ∃ s, PureMinimizer (pair n) s := by
  classical
  suffices h : ∀ᶠ n in atTop, ¬ ∃ s, PureMinimizer (pair n) s from
    h.mono (fun n hn => ⟨hrepresentable n, hn⟩)
  by_contra h
  have hfreq : ∃ᶠ n in atTop, ∃ s, PureMinimizer (pair n) s := by
    simpa only [not_not] using (not_eventually.mp h)
  obtain ⟨f, hf, hmin⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨n, _, hn⟩ := exists_pair_without_pure_minimizer
    (fun n => pair (f n)) Representable PureMinimizer
    (fun n => hrepresentable (f n)) radiation (fun n => depletion (f n))
    (δ ∘ f) (gap ∘ f) soft κ (fieldError ∘ f) C
    (hδ.comp hf.tendsto_atTop) (hgap.comp hf.tendsto_atTop)
    hsoft hκ (hfield.comp hf.tendsto_atTop)
    (fun n => radiationNonneg (f n)) (fun n => depletionNonneg (f n))
    (fun n => energyComparison (f n)) (fun m n => photonBound m (f n))
    Nonvanishing phaseIntegral phaseQuantized (fun n => loopExtraction (f n))
  exact hn (hmin n)

/-- Zero-coupling equality of energies forces vanishing radiation and
electronic optimality, by positivity alone. -/
theorem zero_radiation_of_minimal_energy {F electronic photon total : ℝ}
    (hph : 0 ≤ photon) (hfloor : F ≤ electronic)
    (hsplit : total = electronic + photon) (hmin : total = F) :
    photon = 0 ∧ electronic = F := by
  constructor <;> linarith

/-- The zero-coupling attainment criterion. `Joint` denotes pure total
states and `Electronic` electronic density matrices. The predicate
`ElectronicPureAtPair` includes rank one and the fixed constraints.

The vacuum-kernel theorem for `dΓ(omega)` and pure-marginal factorization
justify `vacuumPurity`. Vacuum tensor embedding justifies `vacuumEmbedding`.
The common value `F` must already be identified with the electronic mixed
search. This theorem does not assume existence of a pure minimizer.
-/
theorem zero_coupling_attainment_iff
    {Joint Electronic : Type*}
    (JointAtPair : Joint → Prop) (ElectronicPureAtPair : Electronic → Prop)
    (marginal : Joint → Electronic)
    (jointEnergy : Joint → ℝ) (electronicEnergy : Electronic → ℝ)
    (radiation : Joint → ℝ) (F : ℝ)
    (hph : ∀ ψ, JointAtPair ψ → 0 ≤ radiation ψ)
    (hfloor : ∀ ψ, JointAtPair ψ → F ≤ electronicEnergy (marginal ψ))
    (hsplit : ∀ ψ, JointAtPair ψ →
      jointEnergy ψ = electronicEnergy (marginal ψ) + radiation ψ)
    (vacuumPurity : ∀ ψ, JointAtPair ψ → radiation ψ = 0 →
      ElectronicPureAtPair (marginal ψ))
    (vacuumEmbedding : ∀ γ, ElectronicPureAtPair γ →
      ∃ ψ, JointAtPair ψ ∧ jointEnergy ψ = electronicEnergy γ) :
    (∃ ψ, JointAtPair ψ ∧ jointEnergy ψ = F) ↔
      ∃ γ, ElectronicPureAtPair γ ∧ electronicEnergy γ = F := by
  constructor
  · rintro ⟨ψ, hψ, hmin⟩
    obtain ⟨hzero, hel⟩ := zero_radiation_of_minimal_energy
      (hph ψ hψ) (hfloor ψ hψ) (hsplit ψ hψ) hmin
    exact ⟨marginal ψ, vacuumPurity ψ hψ hzero, hel⟩
  · rintro ⟨γ, hγ, hmin⟩
    obtain ⟨ψ, hψ, henergy⟩ := vacuumEmbedding γ hγ
    exact ⟨ψ, hψ, henergy.trans hmin⟩

end GptLean.Nonattainment
