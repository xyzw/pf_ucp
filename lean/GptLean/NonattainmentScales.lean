import GptLean.Nonattainment
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The scale choices and vanishing metric error in the thin-loop proof.

The cutoff moduli enter only through their right limits at zero. Their
integral definitions, the perimeter bound, and the PF comparison estimates
are separate analytic inputs. The choices and limits below are proved here.
-/

namespace GptLean.Nonattainment

open Filter Topology

/-- The narrow ellipse axis can satisfy both cutoff-modulus constraints. -/
theorem exists_thin_axis {d₀ d₁ : ℝ → ℝ}
    (h₀ : Tendsto d₀ (𝓝[>] 0) (𝓝 0))
    (h₁ : Tendsto d₁ (𝓝[>] 0) (𝓝 0))
    {b : ℝ} (hb : 0 < b) :
    ∃ a : ℝ, 0 < a ∧ a ≤ b ^ 3 ∧ d₀ (2 * a) + d₁ (2 * a) ≤ b ^ 2 := by
  have hs : ∀ᶠ x in 𝓝[>] (0 : ℝ), d₀ x + d₁ x < b ^ 2 := by
    exact (h₀.add h₁).eventually (gt_mem_nhds (by simpa using sq_pos_of_pos hb))
  have hx : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < 2 * b ^ 3 :=
    (eventually_lt_nhds (show (0 : ℝ) < 2 * b ^ 3 by positivity)).filter_mono
      nhdsWithin_le_nhds
  have hpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  obtain ⟨x, hxpos, hxsmall, hsum⟩ :=
    (Filter.Eventually.and hpos (Filter.Eventually.and hx hs)).exists
  refine ⟨x / 2, by positivity, by linarith, ?_⟩
  simpa only [show (2 : ℝ) * (x / 2) = x by ring] using hsum.le

/-- Choose a narrow axis at every positive large-axis scale. -/
theorem exists_thin_axis_sequence {d₀ d₁ : ℝ → ℝ}
    (h₀ : Tendsto d₀ (𝓝[>] 0) (𝓝 0))
    (h₁ : Tendsto d₁ (𝓝[>] 0) (𝓝 0))
    {b : ℕ → ℝ} (hb : ∀ n, 0 < b n) :
    ∃ a : ℕ → ℝ, ∀ n,
      0 < a n ∧ a n ≤ b n ^ 3 ∧ d₀ (2 * a n) + d₁ (2 * a n) ≤ b n ^ 2 := by
  classical
  choose a ha using fun n => exists_thin_axis h₀ h₁ (hb n)
  exact ⟨a, ha⟩

/-- The selected narrow axes also shrink to zero. -/
theorem thin_axis_tendsto_zero {a b : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hab : ∀ n, a n ≤ b n ^ 3)
    (hb : Tendsto b atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  apply squeeze_zero ha hab
  simpa using hb.pow 3

/-- The tube radius and maximum curvature give the stated metric error. -/
theorem thin_radius_metric_identity {a b : ℝ} (ha : a ≠ 0) :
    (b / a ^ 2) * (a ^ 2 * b ^ 3 / 10) = b ^ 4 / 10 := by
  field_simp [ha]

/-- The chosen radius fits inside the tubular-neighborhood scale. -/
theorem thin_radius_lt_curvature_radius {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hb₁ : b < 1) :
    0 < a ^ 2 * b ^ 3 / 10 ∧ a ^ 2 * b ^ 3 / 10 < a ^ 2 / b := by
  have hb₄ : b ^ 4 < 1 := pow_lt_one₀ hb.le hb₁ (by norm_num)
  constructor
  · positivity
  · apply (lt_div_iff₀ hb).2
    nlinarith [mul_pos (sq_pos_of_pos ha) (show 0 < 10 - b ^ 4 by linarith)]

/-- The perimeter lower bound is enough to control the metric error. -/
theorem thin_metric_error_bound {b L : ℝ} (hb : 0 < b) (hL : 4 * b ≤ L) :
    0 ≤ (b ^ 4 / 10) / L ^ 2 ∧ (b ^ 4 / 10) / L ^ 2 ≤ b ^ 2 / 160 := by
  have hLp : 0 < L := by linarith
  have hsq : 16 * b ^ 2 ≤ L ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hL) (show 0 ≤ L + 4 * b by linarith)]
  constructor
  · positivity
  · apply (div_le_iff₀ (sq_pos_of_pos hLp)).2
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg b)]

/-- No upper estimate for the shrinking perimeter is needed here. -/
theorem thin_metric_error_tendsto_zero {b L : ℕ → ℝ}
    (hbpos : ∀ n, 0 < b n) (hL : ∀ n, 4 * b n ≤ L n)
    (hb : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun n => (b n ^ 4 / 10) / L n ^ 2) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => (thin_metric_error_bound (hbpos n) (hL n)).1)
    (fun n => (thin_metric_error_bound (hbpos n) (hL n)).2)
  simpa using (hb.pow 2).div_const 160

/-- Exact factorization isolates the small ratio `ε / L²`. -/
theorem thin_metric_gap_identity {ε L : ℝ} (hm : 1 - ε ≠ 0) (hp : 1 + ε ≠ 0) :
    Real.pi ^ 2 / L ^ 2 * (1 / (1 - ε) ^ 2 - 1 / (1 + ε) ^ 2) =
      (4 * Real.pi ^ 2) * (ε / L ^ 2) / ((1 - ε) ^ 2 * (1 + ε) ^ 2) := by
  by_cases hL : L = 0
  · simp [hL]
  · field_simp [hm, hp, hL]
    ring

/-- The upper and lower metric corrections have a vanishing gap. -/
theorem thin_energy_gap_tendsto_zero {b L τ : ℕ → ℝ}
    (hbpos : ∀ n, 0 < b n) (hb₁ : ∀ n, b n < 1)
    (hL : ∀ n, 4 * b n ≤ L n) (hb : Tendsto b atTop (𝓝 0))
    (hτ : Tendsto τ atTop (𝓝 0)) :
    Tendsto (fun n => Real.pi ^ 2 / L n ^ 2 *
      (1 / (1 - b n ^ 4 / 10) ^ 2 - 1 / (1 + b n ^ 4 / 10) ^ 2) + τ n)
      atTop (𝓝 0) := by
  have hε : Tendsto (fun n => b n ^ 4 / 10) atTop (𝓝 0) := by
    simpa using (hb.pow 4).div_const 10
  have hden : Tendsto (fun n => (1 - b n ^ 4 / 10) ^ 2 *
      (1 + b n ^ 4 / 10) ^ 2) atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using ((hone.sub hε).pow 2).mul ((hone.add hε).pow 2)
  have hratio := thin_metric_error_tendsto_zero hbpos hL hb
  have hlim := ((hratio.const_mul (4 * Real.pi ^ 2)).div hden (by norm_num)).add hτ
  simp only [mul_zero, zero_div, zero_add] at hlim
  convert hlim using 1
  ext n
  congr 1
  apply thin_metric_gap_identity
  · have hsmall : b n ^ 4 < 1 := pow_lt_one₀ (hbpos n).le (hb₁ n) (by norm_num)
    linarith
  · positivity

/-- The concrete metric gap supplies the radiation-forcing theorem. -/
theorem radiation_tendsto_zero_of_thin_scales {b L τ E : ℕ → ℝ} (e C : ℝ)
    (hbpos : ∀ n, 0 < b n) (hb₁ : ∀ n, b n < 1)
    (hL : ∀ n, 4 * b n ≤ L n) (hb : Tendsto b atTop (𝓝 0))
    (hτ : Tendsto τ atTop (𝓝 0)) (hE : ∀ n, 0 ≤ E n)
    (hcomparison : ∀ n, E n - (2 * Real.pi * e * C * b n) *
      (1 + Real.sqrt (E n)) ≤ Real.pi ^ 2 / L n ^ 2 *
        (1 / (1 - b n ^ 4 / 10) ^ 2 - 1 / (1 + b n ^ 4 / 10) ^ 2) + τ n) :
    Tendsto E atTop (𝓝 0) := by
  apply radiation_tendsto_zero hE
    (by simpa using hb.const_mul (2 * Real.pi * e * C))
    (thin_energy_gap_tendsto_zero hbpos hb₁ hL hb hτ)
    hcomparison

end GptLean.Nonattainment
