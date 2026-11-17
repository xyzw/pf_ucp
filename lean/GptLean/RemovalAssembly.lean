import GptLean.RemovalEstimates
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Countable localization and the actual cluster-scale optimization in
Steps 5 and 6 of lem-exact-soft-removal. No finite localization index is
assumed. Summability of the repaired energies follows from their bounds.
-/

namespace GptLean.RemovalAssembly

open GptLean.RemovalEstimates

/-- Cauchy–Schwarz for the countably many localization weights, including
the summability conclusion needed before using a real-valued tsum. -/
theorem summable_sqrt_mul {ι : Type*} {p B : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hB : ∀ i, 0 ≤ B i)
    (hps : Summable p) (hBs : Summable B) :
    Summable (fun i => Real.sqrt (p i * B i)) ∧
      (∑' i, Real.sqrt (p i * B i)) ≤
        Real.sqrt (∑' i, p i) * Real.sqrt (∑' i, B i) := by
  have hfinite (s : Finset ι) :
      (∑ i ∈ s, Real.sqrt (p i * B i)) ≤
        Real.sqrt (∑' i, p i) * Real.sqrt (∑' i, B i) := by
    calc
      _ = ∑ i ∈ s, Real.sqrt (p i) * Real.sqrt (B i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Real.sqrt_mul (hp i) _
      _ ≤ Real.sqrt (∑ i ∈ s, p i) * Real.sqrt (∑ i ∈ s, B i) :=
        Real.sum_sqrt_mul_sqrt_le s hp hB
      _ ≤ _ := by
        gcongr
        · exact hps.sum_le_tsum s (fun i _ => hp i)
        · exact hBs.sum_le_tsum s (fun i _ => hB i)
  exact ⟨summable_of_sum_le (fun i => Real.sqrt_nonneg _) hfinite,
    Real.tsum_le_of_sum_le (fun i => Real.sqrt_nonneg _) hfinite⟩

theorem tsum_B {ι : Type*} {p E : ι → ℝ} {a b Esoft : ℝ}
    (hps : Summable p) (hEs : Summable E)
    (hp : ∑' i, p i = 1) (hE : ∑' i, E i = Esoft) :
    (∑' i, (a ^ 2 * E i + b ^ 2 * p i)) = a ^ 2 * Esoft + b ^ 2 := by
  rw [Summable.tsum_add (hEs.mul_left _) (hps.mul_left _),
    tsum_mul_left, tsum_mul_left, hp, hE, mul_one]

/-- Summing subnormalized output energies over all localized clusters.
The IMS and per-cluster repair estimates are the analytic inputs. -/
theorem countable_energy_bound {ι : Type*} {T T' E p : ι → ℝ}
    {T₀ Esoft C e k R a b : ℝ}
    (hC : 0 ≤ C) (he : 0 ≤ e) (hk : 0 ≤ k)
    (hp0 : ∀ i, 0 ≤ p i) (hE0 : ∀ i, 0 ≤ E i)
    (hT'0 : ∀ i, 0 ≤ T' i)
    (hTs : Summable T) (hEs : Summable E) (hps : Summable p)
    (hp : ∑' i, p i = 1) (hE : ∑' i, E i = Esoft)
    (hIMS : ∑' i, T i ≤ T₀ + C * (R ^ 2)⁻¹)
    (hlocal : ∀ i, T' i ≤ T i - E i +
      (C * e ^ 2 * k ^ 2 * R ^ 2) * (a ^ 2 * E i + b ^ 2 * p i) +
      (C * e * k) * Real.sqrt (p i * (a ^ 2 * E i + b ^ 2 * p i)) +
      (C * e ^ 2 * b ^ 2) * p i) :
    Summable T' ∧ (∑' i, T' i) ≤ T₀ - Esoft +
      C * scaleError e k R b (a ^ 2 * Esoft + b ^ 2) := by
  let B := fun i => a ^ 2 * E i + b ^ 2 * p i
  have hB0 : ∀ i, 0 ≤ B i := fun i =>
    add_nonneg (mul_nonneg (sq_nonneg _) (hE0 i))
      (mul_nonneg (sq_nonneg _) (hp0 i))
  have hBs : Summable B := (hEs.mul_left _).add (hps.mul_left _)
  have hBsum : ∑' i, B i = a ^ 2 * Esoft + b ^ 2 := tsum_B hps hEs hp hE
  obtain ⟨hs, hsqrt⟩ := summable_sqrt_mul hp0 hB0 hps hBs
  rw [hp, Real.sqrt_one, one_mul, hBsum] at hsqrt
  have hmajor := (((hTs.sub hEs).add
    (hBs.mul_left (C * e ^ 2 * k ^ 2 * R ^ 2))).add
      (hs.mul_left (C * e * k))).add (hps.mul_left (C * e ^ 2 * b ^ 2))
  have houts : Summable T' := Summable.of_nonneg_of_le hT'0 hlocal hmajor
  refine ⟨houts, ?_⟩
  have hsum := houts.tsum_le_tsum hlocal hmajor
  rw [Summable.tsum_add (((hTs.sub hEs).add (hBs.mul_left _)).add (hs.mul_left _))
      (hps.mul_left _),
    Summable.tsum_add ((hTs.sub hEs).add (hBs.mul_left _)) (hs.mul_left _),
    Summable.tsum_add (hTs.sub hEs) (hBs.mul_left _),
    hTs.tsum_sub hEs, tsum_mul_left, tsum_mul_left, tsum_mul_left,
    hp, hE, hBsum, mul_one] at hsum
  have hroot := mul_le_mul_of_nonneg_left hsqrt
    (show 0 ≤ C * e * k by positivity)
  unfold scaleError
  nlinarith

/-- Balancing R⁻² and t²R² on the admissible interval 1 ≤ R ≤ k⁻¹.
All three regimes, including zero t and both endpoints, are checked. -/
theorem exists_cluster_scale {k t : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) (ht : 0 ≤ t) :
    ∃ R : ℝ, 1 ≤ R ∧ k * R ≤ 1 ∧
      (R ^ 2)⁻¹ + t ^ 2 * R ^ 2 ≤ 2 * (k ^ 2 + t + t ^ 2) := by
  by_cases hsmall : t ≤ k ^ 2
  · refine ⟨k⁻¹, (one_le_inv₀ hk).2 hk1, by simp [hk.ne'], ?_⟩
    have hratio : t * k⁻¹ ≤ k := by
      exact (mul_inv_le_iff₀ hk).2 (by nlinarith)
    have hsquare : (t * k⁻¹) ^ 2 ≤ k ^ 2 :=
      pow_le_pow_left₀ (by positivity) hratio 2
    rw [mul_pow] at hsquare
    simp only [inv_pow, inv_inv] at *
    nlinarith [sq_nonneg t]
  · by_cases hlarge : 1 ≤ t
    · refine ⟨1, le_rfl, by simpa using hk1, ?_⟩
      simp only [one_pow, inv_one, mul_one]
      nlinarith [sq_nonneg k]
    · have htpos : 0 < t := lt_of_lt_of_le (sq_pos_of_pos hk) (le_of_not_ge hsmall)
      have htle : t ≤ 1 := le_of_not_ge hlarge
      refine ⟨(Real.sqrt t)⁻¹, ?_, ?_, ?_⟩
      · apply (one_le_inv₀ (Real.sqrt_pos.mpr htpos)).2
        exact (Real.sqrt_le_one).2 htle
      · have hroot : k ≤ Real.sqrt t := (Real.le_sqrt hk.le ht).2 (le_of_not_ge hsmall)
        exact (mul_inv_le_iff₀ (Real.sqrt_pos.mpr htpos)).2 (by simpa using hroot)
      · rw [inv_pow, Real.sq_sqrt ht, inv_inv]
        have hid : t ^ 2 * t⁻¹ = t := by field_simp
        rw [hid]
        nlinarith [sq_nonneg k, sq_nonneg t]

/-- The optimized error used by the current attainment proof is obtained
from the free-scale estimate, with a universal factor of three. -/
theorem exists_optimized_scale {e k a b E : ℝ}
    (he : 0 ≤ e) (hk : 0 < k) (hk1 : k ≤ 1) (hE : 0 ≤ E) :
    ∃ R : ℝ, 1 ≤ R ∧ k * R ≤ 1 ∧
      scaleError e k R b (a ^ 2 * E + b ^ 2) ≤
        3 * GptLean.SoftPurification.removalError e k a b E := by
  have hS : 0 ≤ a ^ 2 * E + b ^ 2 := by positivity
  obtain ⟨R, hR, hkR, hbound⟩ := exists_cluster_scale hk hk1
    (show 0 ≤ e * k * Real.sqrt (a ^ 2 * E + b ^ 2) by positivity)
  refine ⟨R, hR, hkR, ?_⟩
  have ht : (e * k * Real.sqrt (a ^ 2 * E + b ^ 2)) ^ 2 =
      e ^ 2 * k ^ 2 * (a ^ 2 * E + b ^ 2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hS]
  rw [ht] at hbound
  unfold scaleError GptLean.SoftPurification.removalError
  have hlinear : 0 ≤ e * k * Real.sqrt (a ^ 2 * E + b ^ 2) := by positivity
  have hquad : 0 ≤ e ^ 2 * k ^ 2 * (a ^ 2 * E + b ^ 2) := by positivity
  have hvac : 0 ≤ e ^ 2 * b ^ 2 := by positivity
  nlinarith [sq_nonneg k]

end GptLean.RemovalAssembly
