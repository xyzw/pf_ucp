import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Algebra and limiting arguments in `thm-unrestricted-attainment`.

The real energies below stand for finite expectation values. Photon moments
in the final theorem are extended nonnegative reals and may be infinite.
No Pauli–Fierz
operators or density matrices are constructed here. In particular the exact
current repair, its energy estimate, and the retained-limit principle with
photon loss are paper-specific inputs. They are explicit hypotheses, not
axioms or purported standard background facts. The integrated layer-cake
estimate used below is proved in the companion `HardLayerCake` module from
an explicit photon moment representation and the soft-energy profile bound.

The file checks both the optimized-scale absorption and the fixed scale
`R = κ⁻¹` actually chosen near the end of the manuscript proof. At the fixed
scale one must make `aκ` small, rather than merely `κ * aκ` small.
-/

namespace GptLean.Attainment

open Filter Topology
open scoped ENNReal

/-- The square-root term is absorbed with an explicit constant. -/
theorem sqrt_young {s b : ℝ} (hs : 0 ≤ s) :
    b * Real.sqrt s ≤ s / 4 + b ^ 2 := by
  nlinarith [sq_nonneg (Real.sqrt s / 2 - b), Real.sq_sqrt hs]

/-- Scalar core of `unrestricted-soft-energy-gain`.
`a` is the coefficient of soft energy and `b` that of its square root. -/
theorem soft_energy_gain {energy repaired soft a b remainder : ℝ}
    (hs : 0 ≤ soft) (ha : a ≤ 1 / 4)
    (hrepair : repaired ≤ energy - soft + remainder + a * soft + b * Real.sqrt soft) :
    repaired ≤ energy - soft / 2 + remainder + b ^ 2 := by
  have hmul := mul_le_mul_of_nonneg_right ha hs
  have hyoung := sqrt_young (b := b) hs
  nlinarith

/-- The norm splitting used before the absorption step. -/
theorem sqrt_soft_bound {soft a b : ℝ}
    (hs : 0 ≤ soft) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a ^ 2 * soft + b ^ 2) ≤ a * Real.sqrt soft + b := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have heq := congrArg (fun s : ℝ => a ^ 2 * s) (Real.sq_sqrt hs)
    nlinarith [mul_nonneg (mul_nonneg ha (Real.sqrt_nonneg soft)) hb]

/-- Fixed-cluster-scale repair. This verifies that choosing `R = κ⁻¹`
still suffices, provided `C * e² * a² ≤ 1/4`. The manuscript instead
references the preceding optimized-scale estimate at this point. -/
theorem fixed_scale_soft_energy_gain
    {energy repaired soft C e a b κ : ℝ}
    (hs : 0 ≤ soft) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hsmall : C * e ^ 2 * a ^ 2 ≤ 1 / 4)
    (hbound : a ^ 2 ≤ 1)
    (hrepair : repaired ≤ energy - soft +
      C * (κ ^ 2 + 2 * e ^ 2 * b ^ 2 + e ^ 2 * a ^ 2 * soft +
        e * κ * a * Real.sqrt soft + e * κ * b)) :
    repaired ≤ energy - soft / 2 +
      (C + C * e / 2 + C ^ 2 * e ^ 2) * κ ^ 2 +
      (2 * C * e ^ 2 + C * e / 2) * b ^ 2 := by
  have hyoung : e * κ * b ≤ e / 2 * (κ ^ 2 + b ^ 2) := by
    nlinarith [mul_nonneg he (sq_nonneg (κ - b))]
  have hg := soft_energy_gain (energy := energy) (repaired := repaired)
    (a := C * e ^ 2 * a ^ 2)
    (b := C * e * κ * a)
    (remainder := C * (κ ^ 2 + 2 * e ^ 2 * b ^ 2 + e * κ * b))
    hs hsmall (by
      convert hrepair using 1
      ring)
  have hbnd : (C * e * κ * a) ^ 2 ≤ C ^ 2 * e ^ 2 * κ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hbound
      (show 0 ≤ C ^ 2 * e ^ 2 * κ ^ 2 by positivity)]
  have hyoungC := mul_le_mul_of_nonneg_left hyoung hC
  nlinarith

/-- Fixed-scale gain directly from the cost before splitting its square root.
This is the scalar repair of the manuscript's optimized-scale citation. -/
theorem raw_fixed_scale_soft_energy_gain
    {energy repaired soft C e a b κ : ℝ}
    (hs : 0 ≤ soft) (hC : 0 ≤ C) (he : 0 ≤ e)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hκ : 0 ≤ κ)
    (hsmall : C * e ^ 2 * a ^ 2 ≤ 1 / 4) (hbound : a ^ 2 ≤ 1)
    (hrepair : repaired ≤ energy - soft +
      C * (κ ^ 2 + 2 * e ^ 2 * b ^ 2 + e ^ 2 * a ^ 2 * soft +
        e * κ * Real.sqrt (a ^ 2 * soft + b ^ 2))) :
    repaired ≤ energy - soft / 2 +
      (C + C * e / 2 + C ^ 2 * e ^ 2) * κ ^ 2 +
      (2 * C * e ^ 2 + C * e / 2) * b ^ 2 := by
  apply fixed_scale_soft_energy_gain hs hC he hsmall hbound
  have hsplit := mul_le_mul_of_nonneg_left (sqrt_soft_bound hs ha hb)
    (show 0 ≤ C * e * κ by positivity)
  nlinarith

/-- Comparing a feasible repaired state with the constrained-search infimum
turns the energy gain into the uniform soft-energy bound. -/
theorem soft_energy_of_near_minimizer {F energy repaired soft err : ℝ}
    (hfloor : F ≤ repaired)
    (hgain : repaired ≤ energy - soft / 2 + err) :
    soft ≤ 2 * (energy - F) + 2 * err := by
  linarith

/-- At a true minimizer the excess energy disappears. -/
theorem optimizer_soft_energy {F repaired soft err : ℝ}
    (hfloor : F ≤ repaired)
    (hgain : repaired ≤ F - soft / 2 + err) : soft ≤ 2 * err := by
  linarith

/-- Algebra after Tonelli and integration of the soft-energy bound.
The integrated estimate `hnumber` is proved from the photon moment
representation and actual cutoff profiles in `HardLayerCake.lean`. This
lemma isolates only the final algebraic simplification. -/
theorem near_minimizer_number_bound {number energy κ κ₀ excess C : ℝ}
    (hd : 0 ≤ excess) (hκ₀ : 0 < κ₀)
    (hnumber : number ≤ energy / κ₀ +
      2 * excess * (1 / κ - 1 / κ₀) + C) :
    number ≤ energy / κ₀ + 2 * excess / κ + C := by
  have hnonneg : 0 ≤ 2 * excess / κ₀ := by positivity
  have hid : 2 * excess * (1 / κ - 1 / κ₀) =
      2 * excess / κ - 2 * excess / κ₀ := by ring
  rw [hid] at hnumber
  linarith

/-- The manuscript's cutoff choice, indexed from zero without a division
by zero at the first term. -/
noncomputable def cutoff (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  max (Real.sqrt (d n)) (1 / ((n : ℝ) + 1))

theorem cutoff_pos (d : ℕ → ℝ) (n : ℕ) : 0 < cutoff d n := by
  exact lt_of_lt_of_le (by positivity) (le_max_right _ _)

theorem cutoff_tendsto_zero {d : ℕ → ℝ}
    (hd : Tendsto d atTop (𝓝 0)) :
    Tendsto (cutoff d) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => Real.sqrt (d n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hd
  change Tendsto (fun n => max (Real.sqrt (d n)) (1 / ((n : ℝ) + 1))) atTop (𝓝 0)
  simpa only [max_self] using hs.max
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem excess_div_cutoff_le_sqrt {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) (n : ℕ) :
    d n / cutoff d n ≤ Real.sqrt (d n) := by
  rw [div_le_iff₀ (cutoff_pos d n)]
  have h := mul_le_mul_of_nonneg_left (le_max_left (Real.sqrt (d n))
    (1 / ((n : ℝ) + 1))) (Real.sqrt_nonneg (d n))
  dsimp [cutoff]
  nlinarith [Real.sq_sqrt (hd n)]

theorem excess_div_cutoff_tendsto_zero {d : ℕ → ℝ}
    (hd : ∀ n, 0 ≤ d n) (hlim : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n => d n / cutoff d n) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => Real.sqrt (d n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hlim
  exact squeeze_zero (fun n => div_nonneg (hd n) (cutoff_pos d n).le)
    (excess_div_cutoff_le_sqrt hd) hs

/-- The cutoff eventually lies in every positive permitted interval. -/
theorem cutoff_eventually_small {d : ℕ → ℝ} {κ₀ : ℝ}
    (hd : Tendsto d atTop (𝓝 0)) (hκ₀ : 0 < κ₀) :
    ∀ᶠ n in atTop, 0 < cutoff d n ∧ cutoff d n < κ₀ := by
  filter_upwards [((cutoff_tendsto_zero hd).eventually (gt_mem_nhds hκ₀))] with n hn
  exact ⟨cutoff_pos d n, hn⟩

/-- Discarding a finite prefix makes every chosen cutoff admissible. -/
theorem cutoff_small_on_tail {d : ℕ → ℝ} {κ₀ : ℝ}
    (hd : Tendsto d atTop (𝓝 0)) (hκ₀ : 0 < κ₀) :
    ∃ n₀ : ℕ, ∀ n, 0 < cutoff d (n + n₀) ∧ cutoff d (n + n₀) < κ₀ := by
  obtain ⟨n₀, hn₀⟩ := (eventually_atTop.1 (cutoff_eventually_small hd hκ₀))
  exact ⟨n₀, fun n => hn₀ (n + n₀) (Nat.le_add_left n₀ n)⟩

/-- The error in the fixed-scale gain vanishes with the cutoff and the
infrared norm `b`. Its infrared convergence is an explicit analytic input. -/
theorem repair_error_tendsto_zero {d b : ℕ → ℝ} {A B : ℝ}
    (hd : Tendsto d atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun n => A * cutoff d n ^ 2 + B * b n ^ 2) atTop (𝓝 0) := by
  simpa using (((cutoff_tendsto_zero hd).pow 2).const_mul A).add
    ((hb.pow 2).const_mul B)

/-- A repaired feasible sequence remains minimizing when its nonnegative
soft-energy subtraction is dropped and its error tends to zero. -/
theorem repaired_energy_tendsto {energy repaired err : ℕ → ℝ} {F : ℝ}
    (henergy : Tendsto energy atTop (𝓝 F))
    (herr : Tendsto err atTop (𝓝 0))
    (hlower : ∀ n, F ≤ repaired n)
    (hupper : ∀ n, repaired n ≤ energy n + err n) :
    Tendsto repaired atTop (𝓝 F) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using henergy.add herr) hlower hupper

/-- The layer-cake estimate and the cutoff choice give a uniform mean-number
bound on the repaired sequence. -/
theorem repaired_numbers_bounded {energy d number : ℕ → ℝ} {F κ₀ C : ℝ}
    (henergy : Tendsto energy atTop (𝓝 F))
    (hd : ∀ n, 0 ≤ d n) (hlim : Tendsto d atTop (𝓝 0))
    (hnumber : ∀ n, number n ≤ energy n / κ₀ + 2 * (d n / cutoff d n) + C) :
    ∃ M : ℝ, ∀ n, number n ≤ M := by
  have ht : Tendsto (fun n => energy n / κ₀ + 2 * (d n / cutoff d n) + C)
      atTop (𝓝 (F / κ₀ + C)) := by
    simpa using ((henergy.div_const κ₀).add
      ((excess_div_cutoff_tendsto_zero hd hlim).const_mul 2)).add_const C
  obtain ⟨M, hM⟩ := ht.bddAbove_range
  exact ⟨M, fun n => (hnumber n).trans (hM (Set.mem_range_self n))⟩

/-- A paper-specific retained-limit interface for photon loss. It abstracts
the conclusion of `thm-continuum-compactness` on a fixed constraint fiber.

This is a definition of an unproved input, not an assertion that it holds.
Electronic tightness is part of instantiating the fixed constraint fiber.
The real-valued energies restrict this interface to finite-energy sequences.
The retained-number bound is also an explicit input. This is needed for
finite mean photon number, rather than only existence of a minimizer.
-/
def PhotonLossInput (State : Type*) (feasible : State → Prop)
    (energy : State → ℝ) (number : State → ℝ≥0∞) : Prop :=
  ∀ (s : ℕ → State) (L M : ℝ),
    (∀ n, feasible (s n)) →
    (∃ E : ℝ, ∀ n, energy (s n) ≤ E) →
    (∀ n, number (s n) ≤ ENNReal.ofReal M) →
    Tendsto (fun n => energy (s n)) atTop (𝓝 L) →
    ∃ state, feasible state ∧ energy state ≤ L ∧ number state ≤ ENNReal.ofReal M

/-- Conditional direct-method conclusion. All finite-dimensional algebra and
sequence arguments are proved above. Applying this to Pauli–Fierz states
still requires proving the exact feasible repair estimates and `hloss`.
-/
theorem attainment_from_repaired_sequence
    {State : Type*} {feasible : State → Prop} {energy : State → ℝ}
    {number : State → ℝ≥0∞}
    {original repaired : ℕ → State} {F κ₀ C : ℝ} {err : ℕ → ℝ}
    (hfloor : ∀ state, feasible state → F ≤ energy state)
    (hfeasible : ∀ n, feasible (repaired n))
    (horiginal : ∀ n, feasible (original n))
    (hmin : Tendsto (fun n => energy (original n)) atTop (𝓝 F))
    (herr : Tendsto err atTop (𝓝 0))
    (hrepair : ∀ n, energy (repaired n) ≤ energy (original n) + err n)
    (hnumber : ∀ n, number (repaired n) ≤ ENNReal.ofReal (energy (original n) / κ₀ +
      2 * ((energy (original n) - F) /
        cutoff (fun j => energy (original j) - F) n) + C))
    (hloss : PhotonLossInput State feasible energy number) :
    ∃ state, feasible state ∧ energy state = F ∧ number state < ⊤ := by
  have hd : ∀ n, 0 ≤ energy (original n) - F :=
    fun n => sub_nonneg.mpr (hfloor _ (horiginal n))
  have hdl : Tendsto (fun n => energy (original n) - F) atTop (𝓝 0) := by
    simpa using hmin.sub_const F
  have hrep := repaired_energy_tendsto hmin herr
    (fun n => hfloor _ (hfeasible n)) hrepair
  obtain ⟨M, hM⟩ := repaired_numbers_bounded (κ₀ := κ₀) (C := C) hmin hd hdl
    (fun _ => le_rfl)
  have hnb : ∀ n, number (repaired n) ≤ ENNReal.ofReal M :=
    fun n => (hnumber n).trans (ENNReal.ofReal_le_ofReal (hM n))
  obtain ⟨E, hE⟩ := hrep.bddAbove_range
  obtain ⟨state, hf, he, hn⟩ := hloss repaired F M hfeasible
    ⟨E, fun n => hE (Set.mem_range_self n)⟩ hnb hrep
  exact ⟨state, hf, le_antisymm he (hfloor state hf),
    hn.trans_lt ENNReal.ofReal_lt_top⟩

end GptLean.Attainment
