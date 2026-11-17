import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Numerical steps in the Pauli–Fierz Carleman argument

This module proves real inequalities used in the appendix of `pf_ucp.tex`.
It does not assert a Carleman estimate for a physical operator. In particular,
the construction of a radial gauge, the cylinder integration identity, and
the bounds on the resulting operator-valued forms are not proved here.

The cylinder lemmas take the exact numerical identity and its individual
estimates as explicit hypotheses. They check the absorption step without
assuming its conclusion. `sym` and `skew` stand for squared norms. `radial`,
`mass`, `angular`, and `radiation` stand for the nonnegative weighted energy
integrals. `weightedMass` and `weightedRadiation` include the additional
factors `(f')²` and `f'` in the exact commutator identity.
-/

namespace PfHk.CarlemanAlgebra

/-- The angular multiplier estimate absorbs the angular variation once
its coefficient is small. Each remaining error has its own hypothesis. -/
theorem angular_variation_absorbed
    {sym mass angular radiation variation C ε δR δM : ℝ}
    (hsym : 0 ≤ sym) (hmass : 0 ≤ mass) (hradiation : 0 ≤ radiation)
    (hε : 0 ≤ ε)
    (hmultiplier : angular ≤ C * (sym + mass))
    (hvariation : |variation| ≤ ε * angular + δR * radiation + δM * mass)
    (hεC : ε * C ≤ 1 / 8)
    (hδR : δR ≤ 1 / 4) (hδM : δM ≤ 1 / 8) :
    2 * |variation| ≤ sym / 4 + mass / 2 + radiation / 2 := by
  have hmul := mul_le_mul_of_nonneg_left hmultiplier hε
  have hs := mul_le_mul_of_nonneg_right hεC hsym
  have hm := mul_le_mul_of_nonneg_right hεC hmass
  have hR := mul_le_mul_of_nonneg_right hδR hradiation
  have hM := mul_le_mul_of_nonneg_right hδM hmass
  nlinarith

/-- Absorption of the radiation derivative, separately from the angular
variation and the fourth derivative of the weight. -/
theorem radiation_variation_absorbed
    {mass radiation variation ε δ : ℝ}
    (hmass : 0 ≤ mass) (hradiation : 0 ≤ radiation)
    (hvariation : |variation| ≤ ε * radiation + δ * mass)
    (hε : ε ≤ 1 / 4) (hδ : δ ≤ 1 / 8) :
    2 * |variation| ≤ radiation / 2 + mass / 4 := by
  have hR := mul_le_mul_of_nonneg_right hε hradiation
  have hM := mul_le_mul_of_nonneg_right hδ hmass
  linarith

/-- Numerical absorption of the exact cylinder identity
`pf-cylinder-commutator`. The factors involving `f'` have lower bounds
listed explicitly, and no sign is assumed for the three error integrals. -/
theorem cylinder_absorption
    {source sym skew radial mass angular radiation weightedMass weightedRadiation
      fourth angularVariation radiationVariation C : ℝ}
    (hsym : 0 ≤ sym) (hskew : 0 ≤ skew) (hradial : 0 ≤ radial)
    (hmass : 0 ≤ mass) (hradiation : 0 ≤ radiation) (hC : 0 ≤ C)
    (hidentity : source = sym + skew + 4 * radial + 4 * weightedMass - fourth -
      2 * angularVariation + 4 * weightedRadiation - 2 * radiationVariation)
    (hweightedMass : 2 * mass ≤ 4 * weightedMass)
    (hweightedRadiation : 2 * radiation ≤ 4 * weightedRadiation)
    (hmultiplier : angular ≤ C * (sym + mass))
    (hfourth : |fourth| ≤ mass / 4)
    (hangular : 2 * |angularVariation| ≤ sym / 4 + mass / 2 + radiation / 2)
    (hradiationVariation :
      2 * |radiationVariation| ≤ radiation / 2 + mass / 4) :
    0 ≤ source ∧
      sym / 2 + skew + radial + mass + radiation ≤ source ∧
      radial + mass + angular + radiation ≤ (1 + 2 * C) * source := by
  have hf := le_abs_self fourth
  have ha := le_abs_self angularVariation
  have ht := le_abs_self radiationVariation
  have hretained : sym / 2 + skew + radial + mass + radiation ≤ source := by
    linarith
  have hsource : 0 ≤ source := by linarith
  have hsm : sym + mass ≤ 2 * source := by linarith
  have hang := mul_le_mul_of_nonneg_left hsm hC
  have hbase : radial + mass + radiation ≤ source := by linarith
  refine ⟨hsource, hretained, ?_⟩
  nlinarith

/-- The free-cylinder numerical argument assembled from the angular
multiplier and separate smallness conditions. The small coefficients are
chosen by the radius and Carleman parameter in the analytic argument. -/
theorem free_cylinder_absorption
    {source sym skew radial mass angular radiation weightedMass weightedRadiation
      fourth angularVariation radiationVariation C εK δKR δKM εT δTM : ℝ}
    (hsym : 0 ≤ sym) (hskew : 0 ≤ skew) (hradial : 0 ≤ radial)
    (hmass : 0 ≤ mass) (hradiation : 0 ≤ radiation) (hC : 0 ≤ C)
    (hidentity : source = sym + skew + 4 * radial + 4 * weightedMass - fourth -
      2 * angularVariation + 4 * weightedRadiation - 2 * radiationVariation)
    (hweightedMass : 2 * mass ≤ 4 * weightedMass)
    (hweightedRadiation : 2 * radiation ≤ 4 * weightedRadiation)
    (hmultiplier : angular ≤ C * (sym + mass))
    (hfourth : |fourth| ≤ mass / 4)
    (hK : |angularVariation| ≤ εK * angular + δKR * radiation + δKM * mass)
    (hεK : 0 ≤ εK) (hεKC : εK * C ≤ 1 / 8)
    (hδKR : δKR ≤ 1 / 4) (hδKM : δKM ≤ 1 / 8)
    (hT : |radiationVariation| ≤ εT * radiation + δTM * mass)
    (hεT : εT ≤ 1 / 4) (hδTM : δTM ≤ 1 / 8) :
    0 ≤ source ∧
      sym / 2 + skew + radial + mass + radiation ≤ source ∧
      radial + mass + angular + radiation ≤ (1 + 2 * C) * source := by
  exact cylinder_absorption hsym hskew hradial hmass hradiation hC hidentity
    hweightedMass hweightedRadiation hmultiplier hfourth
    (angular_variation_absorbed hsym hmass hradiation hεK hmultiplier hK
      hεKC hδKR hδKM)
    (radiation_variation_absorbed hmass hradiation hT hεT hδTM)

/-- The factor four in `ucp-external-source-control` and in the scalar
perturbation argument follows from two elementary norm-square estimates. -/
theorem perturbation_absorption {F G R : ℝ}
    (htriangle : F ≤ 2 * G + 2 * R) (hsmall : R ≤ F / 4) : F ≤ 4 * G := by
  linarith

/-- Any previously proved mixed estimate transfers to the perturbed source.
The estimate itself remains an explicit hypothesis. -/
theorem transfer_estimate {quantity C F G : ℝ}
    (hC : 0 ≤ C) (hestimate : quantity ≤ C * F) (hsource : F ≤ 4 * G) :
    quantity ≤ (4 * C) * G := by
  have h := mul_le_mul_of_nonneg_left hsource hC
  nlinarith

/-- Combined source absorption and transfer of a weighted estimate. -/
theorem perturbation_and_transfer {quantity C F G R : ℝ}
    (hC : 0 ≤ C) (hestimate : quantity ≤ C * F)
    (htriangle : F ≤ 2 * G + 2 * R) (hsmall : R ≤ F / 4) :
    F ≤ 4 * G ∧ quantity ≤ (4 * C) * G := by
  have hsource := perturbation_absorption htriangle hsmall
  exact ⟨hsource, transfer_estimate hC hestimate hsource⟩

/-- A useful general absorption form, with the retained fraction explicit. -/
theorem absorption_with_fraction {F G θ : ℝ}
    (hθ : θ < 1) (h : F ≤ G + θ * F) : F ≤ G / (1 - θ) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - θ)).2
  nlinarith

/-- The scalar multiplier order is strictly below the endpoint order. -/
theorem scalar_order {p : ℝ} (hp : 2 < p) : 0 < 3 / p ∧ 3 / p < 3 / 2 := by
  have hp0 : 0 < p := by linarith
  constructor
  · exact div_pos (by norm_num) hp0
  · apply (div_lt_iff₀ hp0).2
    linarith

/-- Positivity of the parameter-decay exponent used for scalar and
external-divergence perturbations. -/
theorem scalar_parameter_exponent {p : ℝ} (hp : 2 < p) : 0 < 3 - 6 / p := by
  have hp0 : 0 < p := by linarith
  have h : 6 / p < 3 := (div_lt_iff₀ hp0).2 (by linarith)
  linarith

/-- Positivity of the radius exponent in the scalar perturbation estimate. -/
theorem scalar_radius_exponent {p : ℝ} (hp : 2 < p) : 0 < 4 - 6 / p := by
  have h := scalar_parameter_exponent hp
  linarith

/-- The same exponents written in terms of the Sobolev order `s = 3/p`. -/
theorem scalar_exponents {p : ℝ} (hp : 2 < p) :
    0 < 3 - 2 * (3 / p) ∧ 0 < 4 - 2 * (3 / p) := by
  have h₁ := scalar_parameter_exponent hp
  have h₂ := scalar_radius_exponent hp
  have heq : 2 * (3 / p) = 6 / p := by ring
  rw [heq]
  exact ⟨h₁, h₂⟩

/-- Endpoint orders used for the external vector-potential perturbation.
The first-order estimate has no parameter gain, but has radius gain one. -/
theorem endpoint_exponents :
    (3 - 2 * (3 / 2 : ℝ) = 0) ∧ (4 - 2 * (3 / 2 : ℝ) = 1) ∧
    (3 - 2 * (1 / 2 : ℝ) = 2) ∧ (4 - 2 * (1 / 2 : ℝ) = 3) := by
  norm_num

/-- Iterating the numerical recurrence at successive dyadic radii.
This is the induction step in `ucp-infinite-order`, stated without any
assumptions about how the local mass function was obtained. -/
theorem geometric_recurrence {U : ℕ → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ n, U (n + 1) ≤ q * U n) (n : ℕ) :
    U n ≤ q ^ n * U 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      U (n + 1) ≤ q * U n := hstep n
      _ ≤ q * (q ^ n * U 0) := mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (n + 1) * U 0 := by rw [pow_succ]; ring

/-- A geometric recurrence on actual radii, for every natural vanishing
order. Neither a zero-set density theorem nor an energy estimate is assumed
implicitly by this numerical lemma. -/
theorem dyadic_radius_recurrence {U : ℝ → ℝ} {R : ℝ} (m : ℕ)
    (hstep : ∀ n : ℕ,
      U ((1 / 2 : ℝ) ^ (n + 1) * R) ≤
        (1 / 2 : ℝ) ^ m * U ((1 / 2 : ℝ) ^ n * R)) (n : ℕ) :
    U ((1 / 2 : ℝ) ^ n * R) ≤ ((1 / 2 : ℝ) ^ n) ^ m * U R := by
  have h := geometric_recurrence (U := fun n => U ((1 / 2 : ℝ) ^ n * R))
    (q := (1 / 2 : ℝ) ^ m) (by positivity) hstep n
  simpa only [pow_zero, one_mul, ← pow_mul, Nat.mul_comm m n] using h

end PfHk.CarlemanAlgebra
