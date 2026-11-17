import GptLean.RemovalAssembly
import GptLean.MainResults

/-!
From the localized conditional construction to the removal estimate used
by the main results. The data below retain the physical constraints and
photon marginal, but replace a premise asserting the final energy bound
by the IMS estimate and individual repaired-cluster estimates.

The construction of physical localized and conditional states, their
form-domain membership, and the trace/energy decomposition remain inputs.
The countable summation, summability of output energy and choice of a
single output with the optimized cost are proved here.
-/

namespace GptLean.SoftRemoval

open GptLean.RemovalAssembly GptLean.RemovalEstimates
open Filter Topology

variable {M D F P : Type*}

/-- One free-scale output, with countably many subnormalized components.
The vacuum contribution is absorbed into C along with the repair and IMS
constants. These are local analytic interfaces, not a final removal bound. -/
structure LocalizedOutput (B : DFT.StateModel M D) (m : M)
    (marginal : M → F) (target : F) (Esoft C e k R a b : ℝ) where
  state : M
  pair_eq : B.density state = B.density m
  marginal_eq : marginal state = target
  inputEnergy : ℕ → ℝ
  outputEnergy : ℕ → ℝ
  softEnergy : ℕ → ℝ
  mass : ℕ → ℝ
  mass_nonneg : ∀ i, 0 ≤ mass i
  soft_nonneg : ∀ i, 0 ≤ softEnergy i
  output_nonneg : ∀ i, 0 ≤ outputEnergy i
  input_summable : Summable inputEnergy
  soft_summable : Summable softEnergy
  mass_summable : Summable mass
  mass_total : ∑' i, mass i = 1
  soft_total : ∑' i, softEnergy i = Esoft
  output_total : B.energy state = ∑' i, outputEnergy i
  ims : ∑' i, inputEnergy i ≤ B.energy m + C * (R ^ 2)⁻¹
  local_cost : ∀ i, outputEnergy i ≤ inputEnergy i - softEnergy i +
    (C * e ^ 2 * k ^ 2 * R ^ 2) * (a ^ 2 * softEnergy i + b ^ 2 * mass i) +
    (C * e * k) * Real.sqrt (mass i * (a ^ 2 * softEnergy i + b ^ 2 * mass i)) +
    (C * e ^ 2 * b ^ 2) * mass i

theorem LocalizedOutput.energy_bound {B : DFT.StateModel M D} {m : M}
    {marginal : M → F} {target : F} {Esoft C e k R a b : ℝ}
    (I : LocalizedOutput B m marginal target Esoft C e k R a b)
    (hC : 0 ≤ C) (he : 0 ≤ e) (hk : 0 ≤ k) :
    B.energy I.state ≤ B.energy m - Esoft +
      C * scaleError e k R b (a ^ 2 * Esoft + b ^ 2) := by
  rw [I.output_total]
  exact (countable_energy_bound hC he hk I.mass_nonneg I.soft_nonneg
    I.output_nonneg I.input_summable I.soft_summable I.mass_summable
    I.mass_total I.soft_total I.ims I.local_cost).2

/-- The same chosen state has the optimized energy estimate, exact pair
and prescribed hard marginal tensored with the soft vacuum. -/
theorem optimized_output {B : DFT.StateModel M D} (m : M)
    (marginal : M → F) (target : F) {Esoft C e k a b : ℝ}
    (hC : 0 ≤ C) (he : 0 ≤ e) (hk : 0 < k) (hk1 : k ≤ 1) (hE : 0 ≤ Esoft)
    (I : ∀ R, 1 ≤ R → k * R ≤ 1 →
      LocalizedOutput B m marginal target Esoft C e k R a b) :
    ∃ r, B.density r = B.density m ∧ marginal r = target ∧
      B.energy r ≤ B.energy m - Esoft +
        (3 * C) * SoftPurification.removalError e k a b Esoft := by
  obtain ⟨R, hR, hkR, hcost⟩ := exists_optimized_scale (a := a) (b := b) he hk hk1 hE
  let out := I R hR hkR
  refine ⟨out.state, out.pair_eq, out.marginal_eq, ?_⟩
  have h := out.energy_bound hC he hk.le
  have hmul := mul_le_mul_of_nonneg_left hcost hC
  nlinarith

/-- Connecting the new localized construction with the previous main
functional theorem. Pure soft tags are still a separate construction.
They are required only for states with the prescribed vacuum marginal. -/
theorem exactRecovery_of_localized
    (A : DFT.StateModel P D) (B : DFT.StateModel M D)
    (marginal : ℕ → M → F) (target : M → ℕ → F)
    (soft : M → ℕ → ℝ) (k a b : ℕ → ℝ) (C e N : ℝ)
    (hC : 0 ≤ C) (he : 0 ≤ e)
    (hk : ∀ n, 0 < k n) (hk1 : ∀ n, k n ≤ 1)
    (hk0 : Tendsto k atTop (𝓝 0)) (ha0 : Tendsto a atTop (𝓝 0))
    (hb0 : Tendsto b atTop (𝓝 0))
    (hsoft : ∀ m n, 0 ≤ soft m n ∧ soft m n ≤ B.energy m)
    (I : ∀ m n R, 1 ≤ R → k n * R ≤ 1 →
      LocalizedOutput B m (marginal n) (target m n) (soft m n) C e (k n) R (a n) (b n))
    (htag : ∀ m n r, marginal n r = target m n →
      ∃ p, A.density p = B.density r ∧
        A.energy p ≤ B.energy r + k n + N * e ^ 2 * b n ^ 2) :
    DFT.ExactRecovery A B := by
  classical
  have hr (m : M) (n : ℕ) := optimized_output m (marginal n) (target m n)
    hC he (hk n) (hk1 n) (hsoft m n).1 (I m n)
  choose remove hpair hmarg hcost using hr
  have ht (m : M) (n : ℕ) := htag m n (remove m n) (hmarg m n)
  choose tag htagpair htagcost using ht
  exact MainResults.exactRecovery A B
    { remove := remove
      tag := tag
      softEnergy := soft
      k := k
      a := a
      b := b
      C := 3 * C
      e := e
      N := N
      C_nonneg := by positivity
      e_nonneg := he
      k_nonneg := fun n => (hk n).le
      k_zero := hk0
      a_zero := ha0
      b_zero := hb0
      soft_bounds := hsoft
      remove_pair := hpair
      tag_pair := htagpair
      remove_cost := hcost
      tag_cost := htagcost }

end GptLean.SoftRemoval
