import PfHk.CarlemanAlgebra
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Decay and parameter choices for the Carleman weights

These lemmas prove the radius and parameter smallness used in the appendix
of `pf_ucp.tex` from standard real-analysis results in Mathlib. They do not
assume the corresponding physical multiplier or commutator estimates.
The physical radial-gauge realization remains a separate obligation.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace PfHk.CarlemanWeights

set_option backward.isDefEq.respectTransparency.types false

/-- The second derivative of the logarithmic Carleman weight. -/
def beta (α t : ℝ) : ℝ := α * (α + 1) * t ^ (-α - 2)

/-- The convexified logarithmic weight in cylinder coordinates. -/
def weight (α t : ℝ) : ℝ := t + t ^ (-α)

/-- Its first derivative. -/
def weightPrime (α t : ℝ) : ℝ := 1 - α * t ^ (-α - 1)

/-- Differentiating the weight on the positive cylinder. -/
theorem weight_hasDerivAt (α : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (weight α) (weightPrime α t) t := by
  unfold weight weightPrime
  have hp := Real.hasDerivAt_rpow_const (x := t) (p := -α) (Or.inl ht.ne')
  convert (hasDerivAt_id t).add hp using 1 <;> first | rfl | ring

/-- The explicit convexity coefficient is the second derivative. -/
theorem weightPrime_hasDerivAt (α : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (weightPrime α) (beta α t) t := by
  unfold weightPrime beta
  have hp := Real.hasDerivAt_rpow_const (x := t) (p := -α - 1) (Or.inl ht.ne')
  convert (hasDerivAt_const t (1 : ℝ)).sub (hp.const_mul α) using 1 <;>
    first | rfl | (rw [show -α - 1 - 1 = -α - 2 by ring]; ring)

/-- Bernoulli's inequality for the base two. -/
theorem one_add_le_two_rpow {p : ℝ} (hp : 1 ≤ p) : 1 + p ≤ (2 : ℝ) ^ p := by
  have h := one_add_mul_self_le_rpow_one_add (s := (1 : ℝ)) (by norm_num) hp
  rwa [one_add_one_eq_two, mul_one] at h

/-- For every positive exponent, `f'` is positive and at most one on the
half-cylinder `t ≥ 2`. No upper bound on `α` is needed. -/
theorem weightPrime_pos_le_one {α t : ℝ} (hα : 0 < α) (ht : 2 ≤ t) :
    0 < weightPrime α t ∧ weightPrime α t ≤ 1 := by
  have ht0 : 0 < t := by linarith
  have hb : 1 + (α + 1) ≤ (2 : ℝ) ^ (α + 1) := one_add_le_two_rpow (by linarith)
  have hmono : (2 : ℝ) ^ (α + 1) ≤ t ^ (α + 1) :=
    Real.rpow_le_rpow (by norm_num) ht (by linarith)
  have hpos : 0 < t ^ (α + 1) := Real.rpow_pos_of_pos ht0 _
  have hinv : t ^ (-α - 1) = (t ^ (α + 1))⁻¹ := by
    rw [show -α - 1 = -(α + 1) by ring, Real.rpow_neg ht0.le]
  have hprod : α * (t ^ (α + 1))⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hpos]
    linarith
  have hnonneg : 0 ≤ α * (t ^ (α + 1))⁻¹ := mul_nonneg hα.le (inv_nonneg.mpr hpos.le)
  unfold weightPrime
  rw [hinv]
  constructor <;> linarith

/-- Uniform positive lower and upper bounds on `f'` once the cylinder
coordinate dominates the exponent, `t ≥ max 2 (4 α)`. -/
theorem weightPrime_bounds {α t : ℝ} (hα : 0 < α) (ht : 2 ≤ t) (hαt : 4 * α ≤ t) :
    3 / 4 ≤ weightPrime α t ∧ weightPrime α t ≤ 1 := by
  have ht0 : 0 < t := by linarith
  have hp : t ^ (-α - 1) ≤ t ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  rw [Real.rpow_neg_one] at hp
  have hpow0 : 0 ≤ t ^ (-α - 1) := Real.rpow_nonneg ht0.le _
  have hquarter : α * t⁻¹ ≤ 1 / 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ ht0]
    linarith
  have hproduct : α * t ^ (-α - 1) ≤ α * t⁻¹ := mul_le_mul_of_nonneg_left hp hα.le
  have hnonneg := mul_nonneg hα.le hpow0
  unfold weightPrime
  constructor <;> linarith

/-- The precise lower bounds needed by `cylinder_absorption` follow from
the preceding first-derivative bounds. -/
theorem commutator_weight_bounds {α t : ℝ} (hα : 0 < α)
    (ht : 2 ≤ t) (hαt : 4 * α ≤ t) :
    2 ≤ 4 * (weightPrime α t) ^ 2 ∧ 2 ≤ 4 * weightPrime α t := by
  obtain ⟨hlo, hhi⟩ := weightPrime_bounds hα ht hαt
  constructor <;> nlinarith

/-- A radius below `exp (-(4 α + 2))` places the cylinder coordinate above
the exponent threshold used in the annular comparison of `β`. -/
theorem alpha_threshold_of_radius {α R : ℝ} (hR : 0 < R)
    (hαR : R ≤ Real.exp (-(4 * α + 2))) : 4 * α + 2 ≤ -Real.log R := by
  have h := Real.log_le_log hR hαR
  rw [Real.log_exp] at h
  linarith

/-- The radius-to-weight ratio in the cylinder coordinate `t = -log r`. -/
def cylinderRatio (α a t : ℝ) : ℝ := (Real.exp (-t)) ^ a / beta α t

/-- Positive convexity weight for positive exponent and positive cylinder
coordinate. -/
theorem beta_pos {α t : ℝ} (hα : 0 < α) (ht : 0 < t) : 0 < beta α t := by
  unfold beta
  positivity

/-- Rewriting the ratio exhibits an exponentially decaying factor times
an ordinary real power. -/
theorem cylinderRatio_eq {α a t : ℝ} (ht : 0 < t) :
    cylinderRatio α a t =
      (t ^ (α + 2) * Real.exp (-a * t)) / (α * (α + 1)) := by
  unfold cylinderRatio beta
  rw [← Real.exp_mul]
  rw [show -α - 2 = -(α + 2) by ring, Real.rpow_neg ht.le]
  rw [show -t * a = -a * t by ring]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- Exponential decay dominates the logarithmic weight for every positive
radius exponent `a`. No upper bound on `α` is needed for this decay fact. -/
theorem cylinderRatio_tendsto_zero (α : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (cylinderRatio α a) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (α + 2) a ha).div_const (α * (α + 1))
  have hh : Tendsto (fun t : ℝ =>
      (t ^ (α + 2) * Real.exp (-a * t)) / (α * (α + 1))) atTop (𝓝 0) := by
    simpa only [zero_div] using h
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (cylinderRatio_eq ht).symm

/-- Arbitrarily small radius-to-weight ratio on an entire punctured ball.
The selected radius also lies below `exp (-2)`, as required in the paper. -/
theorem exists_radius_small (α : ℝ) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < Real.exp (-2) ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → r ^ a / beta α (-Real.log r) < ε := by
  have hevent := (cylinderRatio_tendsto_zero α ha).eventually_lt_const hε
  obtain ⟨T, hT⟩ := eventually_atTop.1 hevent
  let t₀ : ℝ := max T 3
  refine ⟨Real.exp (-t₀), Real.exp_pos _, ?_, ?_⟩
  · apply Real.exp_lt_exp.mpr
    have ht₀ : 3 ≤ t₀ := le_max_right _ _
    linarith
  · intro r hr hrr₀
    have hlog : Real.log r ≤ -t₀ := by
      have hh := Real.log_le_log hr hrr₀
      simpa only [Real.log_exp] using hh
    have hge : T ≤ -Real.log r := by
      have ht : T ≤ t₀ := le_max_left _ _
      linarith
    have hh := hT (-Real.log r) hge
    simpa only [cylinderRatio, neg_neg, Real.exp_log hr] using hh

/-- The supremum used for the radius selection, expressed directly in
physical radii. -/
def radiusSup (α a r₀ : ℝ) : ℝ :=
  sSup ((fun r : ℝ => r ^ a / beta α (-Real.log r)) '' Ioc 0 r₀)

/-- The small radius may be chosen so that the supremum itself is small.
This avoids replacing a uniform radius bound by a merely pointwise limit. -/
theorem exists_radiusSup_small (α : ℝ) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < Real.exp (-2) ∧ radiusSup α a r₀ ≤ ε := by
  obtain ⟨r₀, hr₀, hupper, hsmall⟩ := exists_radius_small α ha hε
  refine ⟨r₀, hr₀, hupper, ?_⟩
  apply csSup_le
  · exact ⟨_, ⟨r₀, ⟨hr₀, le_rfl⟩, rfl⟩⟩
  · rintro y ⟨r, hr, rfl⟩
    exact (hsmall r hr.1 hr.2).le

/-- A finite linear combination of the two decaying parameter factors in
the scalar perturbation estimate tends to zero. -/
theorem perturbation_coefficient_tendsto {a : ℝ} (ha : 0 < a) (A B : ℝ) :
    Tendsto (fun τ : ℝ => A * τ ^ (-a) + B * τ ^ (-3 : ℝ)) atTop (𝓝 0) := by
  have h₁ := (tendsto_rpow_neg_atTop ha).const_mul A
  have h₂ := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).const_mul B
  simpa only [mul_zero, add_zero] using h₁.add h₂

/-- One parameter threshold works for every larger value of the Carleman
parameter. The constants `A` and `B` include the already fixed local norms
and radius suprema. -/
theorem exists_parameter_small {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (A B : ℝ) :
    ∃ τ₀ : ℝ, 1 ≤ τ₀ ∧ ∀ τ : ℝ, τ₀ ≤ τ →
      A * τ ^ (-a) + B * τ ^ (-3 : ℝ) < ε := by
  have hevent := (perturbation_coefficient_tendsto ha A B).eventually_lt_const hε
  obtain ⟨T, hT⟩ := eventually_atTop.1 hevent
  refine ⟨max T 1, le_max_right _ _, ?_⟩
  intro τ hτ
  exact hT τ ((le_max_left T 1).trans hτ)

/-- The scalar `p > 2` hypothesis gives the threshold needed to absorb
`ucp-scalar-smallness`. -/
theorem exists_scalar_parameter_small {p ε : ℝ} (hp : 2 < p) (hε : 0 < ε)
    (A B : ℝ) :
    ∃ τ₀ : ℝ, 1 ≤ τ₀ ∧ ∀ τ : ℝ, τ₀ ≤ τ →
      A * τ ^ (-(3 - 6 / p)) + B * τ ^ (-3 : ℝ) < ε := by
  exact exists_parameter_small (CarlemanAlgebra.scalar_parameter_exponent hp) hε A B

end PfHk.CarlemanWeights
