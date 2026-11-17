import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Soft-photon purification in the current manuscript.

This file proves the quantitative passage from the removal and one-photon
tag estimates to arbitrarily accurate pure representatives and uniformly
number-bounded pure minimizing sequences. The analytic constructions of
the removal channel and tag vectors are explicit hypotheses, not axioms
or consequences of generic Pauli–Fierz theory.

Manuscript labels
* exact-soft-removal-cost
* many-electron-soft-tag-cost
* many-electron-soft-tag-number
* many-electron-pure-approximation
* pure-minimizing-sequence-number-bound
-/

namespace GptLean.SoftPurification

open Filter Topology
open scoped ENNReal

/-- The error in the current, optimized soft-removal lemma. -/
noncomputable def removalError (e k a b E : ℝ) : ℝ :=
  k ^ 2 + e ^ 2 * b ^ 2 + e * k * Real.sqrt (a ^ 2 * E + b ^ 2) +
    e ^ 2 * k ^ 2 * (a ^ 2 * E + b ^ 2)

theorem removalError_nonneg {e k a b E : ℝ}
    (he : 0 ≤ e) (hk : 0 ≤ k) (hE : 0 ≤ E) :
    0 ≤ removalError e k a b E := by
  unfold removalError
  positivity

theorem removalError_mono {e k a b S E : ℝ}
    (he : 0 ≤ e) (hk : 0 ≤ k) (hSE : S ≤ E) :
    removalError e k a b S ≤ removalError e k a b E := by
  have hinner : a ^ 2 * S + b ^ 2 ≤ a ^ 2 * E + b ^ 2 := by
    exact add_le_add (mul_le_mul_of_nonneg_left hSE (sq_nonneg a)) le_rfl
  have hsqrt := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinner)
    (mul_nonneg he hk)
  have hquad := mul_le_mul_of_nonneg_left hinner
    (mul_nonneg (sq_nonneg e) (sq_nonneg k))
  unfold removalError
  linarith

theorem removalError_tendsto {k a b : ℕ → ℝ}
    (hk : Tendsto k atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) (e E : ℝ) :
    Tendsto (fun n => removalError e (k n) (a n) (b n) E) atTop (𝓝 0) := by
  have hinner : Tendsto (fun n => a n ^ 2 * E + b n ^ 2) atTop (𝓝 0) := by
    simpa using ((ha.pow 2).mul_const E).add (hb.pow 2)
  have hsqrt : Tendsto (fun n => Real.sqrt (a n ^ 2 * E + b n ^ 2))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hinner
  have hcross := (hk.const_mul e).mul hsqrt
  have hquad := ((hk.pow 2).const_mul (e ^ 2)).mul hinner
  simpa [removalError] using
    (((hk.pow 2).add ((hb.pow 2).const_mul (e ^ 2))).add hcross).add hquad

/-- The vacuum energy must be subtracted when computing the tag cost.
The coefficient is N e² b², rather than 3 N e² b² / 2. -/
theorem tag_cost {Etag Ehard Evac k N e b : ℝ}
    (hvac : Evac = Ehard + N * e ^ 2 / 2 * b ^ 2)
    (htag : Etag ≤ Ehard + k + 3 * N * e ^ 2 / 2 * b ^ 2) :
    Etag ≤ Evac + k + N * e ^ 2 * b ^ 2 := by
  linarith

/-- The hard cutoff specialization uses bκ² = 2πκ². -/
theorem hard_cutoff_tag_cost (k N e : ℝ) :
    k + N * e ^ 2 * (2 * Real.pi * k ^ 2) =
      k + 2 * Real.pi * N * e ^ 2 * k ^ 2 := by ring

/-- CCR norm identity plus the one-photon annihilation bound gives factor 3.
The norm identity and sector estimate are standard Fock inputs. -/
theorem one_photon_variance {fieldNormSq kernelNormSq vectorNormSq annihNormSq : ℝ}
    (hCCR : fieldNormSq = kernelNormSq * vectorNormSq + 2 * annihNormSq)
    (hsector : annihNormSq ≤ kernelNormSq * vectorNormSq) :
    fieldNormSq ≤ 3 * kernelNormSq * vectorNormSq := by linarith

/-- Hard radiation energy dominates κ times hard photon number. -/
theorem tag_number_bound {number hardNumber radiation k : ℝ}
    (hk : 0 < k) (htag : number = 1 + hardNumber)
    (hgap : k * hardNumber ≤ radiation) :
    number ≤ 1 + k⁻¹ * radiation := by
  have h : hardNumber ≤ radiation / k := by
    apply (le_div_iff₀ hk).mpr
    nlinarith
  rw [htag]
  simpa [div_eq_mul_inv, mul_comm] using add_le_add_left h 1

/-- The tag-number argument with an a priori possibly infinite photon moment.
The input gap estimate is the standard hard-sector spectral inequality. -/
theorem tag_number_finite {number hardNumber radiation k : ℝ≥0∞}
    (hk : k ≠ 0) (hfinite : radiation ≠ ⊤)
    (htag : number = 1 + hardNumber) (hgap : hardNumber ≤ radiation / k) :
    number < ⊤ := by
  rw [htag]
  exact ENNReal.add_lt_top.mpr ⟨by simp,
    hgap.trans_lt (ENNReal.div_lt_top hfinite hk)⟩

/-- Errors after removal and tagging vanish for any fixed finite state energy. -/
theorem total_error_tendsto {k a b : ℕ → ℝ}
    (hk : Tendsto k atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) (C e E N : ℝ) :
    Tendsto (fun n => C * removalError e (k n) (a n) (b n) E +
      k n + N * e ^ 2 * b n ^ 2) atTop (𝓝 0) := by
  simpa using (((removalError_tendsto hk ha hb e E).const_mul C).add hk).add
    ((hb.pow 2).const_mul (N * e ^ 2))

/-- The main approximation theorem, conditional only on explicitly displayed
removal and tag interfaces. No approximate constraint is silently made exact. -/
theorem pure_approximation
    {Mixed Pure Pair : Type*}
    (mixedEnergy : Mixed → ℝ) (pureEnergy : Pure → ℝ)
    (mixedPair : Mixed → Pair) (purePair : Pure → Pair)
    (remove : Mixed → ℕ → Mixed) (tag : Mixed → ℕ → Pure)
    (softEnergy : Mixed → ℕ → ℝ) (k a b : ℕ → ℝ)
    (C e N : ℝ) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hk0 : ∀ n, 0 ≤ k n)
    (hk : Tendsto k atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0))
    (hsoft : ∀ m n, 0 ≤ softEnergy m n ∧ softEnergy m n ≤ mixedEnergy m)
    (hremovePair : ∀ m n, mixedPair (remove m n) = mixedPair m)
    (htagPair : ∀ m n, purePair (tag m n) = mixedPair (remove m n))
    (hremoveEnergy : ∀ m n, mixedEnergy (remove m n) ≤ mixedEnergy m - softEnergy m n +
      C * removalError e (k n) (a n) (b n) (softEnergy m n))
    (htagEnergy : ∀ m n, pureEnergy (tag m n) ≤ mixedEnergy (remove m n) +
      k n + N * e ^ 2 * b n ^ 2) :
    ∀ m δ, 0 < δ → ∃ p, purePair p = mixedPair m ∧
      pureEnergy p ≤ mixedEnergy m + δ := by
  intro m δ hδ
  have hsmall := (total_error_tendsto hk ha hb C e (mixedEnergy m) N).eventually
    (gt_mem_nhds hδ)
  obtain ⟨n, hn⟩ := hsmall.exists
  refine ⟨tag m n, (htagPair m n).trans (hremovePair m n), ?_⟩
  have hmono := mul_le_mul_of_nonneg_left
    (removalError_mono (a := a n) (b := b n) he (hk0 n) (hsoft m n).2) hC
  have hrem := hremoveEnergy m n
  have ht := htagEnergy m n
  have hS := (hsoft m n).1
  linarith

/-- Once a mixed minimizer has finite photon number, the same tag construction
gives pure minimizing sequences with the article's bound 1 + Tr(N Γ*).
The energy lower bound is the defining infimum property, not attainment. -/
theorem pure_minimizing_sequence
    {Pure Pair : Type*} (energy number : Pure → ℝ) (pair : Pure → Pair)
    (p : ℕ → Pure) (d : Pair) (F mixedNumber : ℝ) (err : ℕ → ℝ)
    (herr : Tendsto err atTop (𝓝 0))
    (hp : ∀ n, pair (p n) = d)
    (hlower : ∀ n, F ≤ energy (p n))
    (hupper : ∀ n, energy (p n) ≤ F + err n)
    (hnumber : ∀ n, number (p n) ≤ 1 + mixedNumber) :
    (∀ n, pair (p n) = d) ∧ Tendsto (fun n => energy (p n)) atTop (𝓝 F) ∧
      (∀ n, number (p n) ≤ 1 + mixedNumber) := by
  refine ⟨hp, ?_, hnumber⟩
  have hu : Tendsto (fun n => F + err n) atTop (𝓝 F) := by
    simpa using herr.const_add F
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu hlower hupper

end GptLean.SoftPurification
