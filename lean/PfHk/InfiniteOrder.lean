import PfHk.CarlemanAlgebra
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Infinite-order vanishing from a small doubling coefficient

These are actual real-radius estimates. They isolate the iteration in
`ucp-infinite-order` from the analytic arguments that supply its recurrence.
No Pauli–Fierz energy estimate, density theorem, or Sobolev inequality is
postulated as a conclusion here.

For a local mass function, the input recurrence follows in the paper from
Sobolev, Caccioppoli, and the density of the zero set. The present module
proves the subsequent passage to all radii and the energy-flatness transfer.
-/

namespace PfHk.InfiniteOrder

/-- An upper bound of order `m` on all sufficiently small positive radii. -/
def PowerBoundAtZero (U : ℝ → ℝ) (m : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧
    ∀ r : ℝ, 0 < r → r ≤ R → U r ≤ C * r ^ m

/-- Vanishing to every natural order. For nonnegative local mass functions,
this is the usual infinite-order estimate near radius zero. -/
def FlatAtZero (U : ℝ → ℝ) : Prop := ∀ m : ℕ, PowerBoundAtZero U m

/-- The coefficient in the local doubling recurrence can be made smaller
than every prescribed positive number by decreasing the radius. -/
def SmallDoublingCoefficient (U : ℝ → ℝ) : Prop :=
  ∀ q : ℝ, 0 < q → ∃ R : ℝ, 0 < R ∧
    ∀ r : ℝ, 0 < r → r ≤ R → U r ≤ q * U (2 * r)

/-- Geometric radii bracket every real radius between zero and `R`. -/
theorem exists_dyadic_bracket {R r : ℝ} (hR : 0 < R)
    (hr : 0 < r) (hrR : r ≤ R) :
    ∃ n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * R < r ∧
      r ≤ (1 / 2 : ℝ) ^ n * R := by
  obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr hR) ((div_le_one hR).2 hrR)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨n, (lt_div_iff₀ hR).1 hn₁, (div_le_iff₀ hR).1 hn₂⟩

/-- Passing from dyadic decay to a power bound on every intermediate radius.
The constant is explicit and strictly positive. -/
theorem power_bound_of_dyadic {U : ℝ → ℝ} {R : ℝ} (m : ℕ)
    (hR : 0 < R) (hUR : 0 ≤ U R) (hmono : Monotone U)
    (hdyadic : ∀ n : ℕ,
      U ((1 / 2 : ℝ) ^ n * R) ≤ ((1 / 2 : ℝ) ^ n) ^ m * U R) :
    ∀ r : ℝ, 0 < r → r ≤ R →
      U r ≤ ((2 / R) ^ m * (U R + 1)) * r ^ m := by
  intro r hr hrR
  obtain ⟨n, hnlo, hnhi⟩ := exists_dyadic_bracket hR hr hrR
  have hnear : (1 / 2 : ℝ) ^ n ≤ (2 / R) * r := by
    rw [pow_succ] at hnlo
    have hh : (1 / 2 : ℝ) ^ n ≤ (2 * r) / R :=
      (le_div_iff₀ hR).2 (by nlinarith)
    convert hh using 1
    ring
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (1 / 2 : ℝ) ^ n) hnear m
  calc
    U r ≤ U ((1 / 2 : ℝ) ^ n * R) := hmono hnhi
    _ ≤ ((1 / 2 : ℝ) ^ n) ^ m * U R := hdyadic n
    _ ≤ ((2 / R) * r) ^ m * U R := mul_le_mul_of_nonneg_right hpow hUR
    _ ≤ ((2 / R) * r) ^ m * (U R + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = ((2 / R) ^ m * (U R + 1)) * r ^ m := by rw [mul_pow]; ring

/-- A nonnegative monotone mass with an arbitrarily small doubling
coefficient vanishes to every natural order at zero. -/
theorem flat_of_small_doubling {U : ℝ → ℝ}
    (hnonnegative : ∀ r : ℝ, 0 < r → 0 ≤ U r)
    (hmono : Monotone U) (hsmall : SmallDoublingCoefficient U) :
    FlatAtZero U := by
  intro m
  obtain ⟨R, hR, hstep⟩ := hsmall ((1 / 2 : ℝ) ^ m) (by positivity)
  have hUR : 0 ≤ U R := hnonnegative R hR
  have hdyadic : ∀ n : ℕ,
      U ((1 / 2 : ℝ) ^ n * R) ≤ ((1 / 2 : ℝ) ^ n) ^ m * U R := by
    apply CarlemanAlgebra.dyadic_radius_recurrence m
    intro n
    have hpos : 0 < (1 / 2 : ℝ) ^ (n + 1) * R := by positivity
    have hle : (1 / 2 : ℝ) ^ (n + 1) * R ≤ R := by
      have hp : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hdouble : 2 * ((1 / 2 : ℝ) ^ (n + 1) * R) =
        (1 / 2 : ℝ) ^ n * R := by rw [pow_succ]; ring
    simpa only [hdouble] using hstep ((1 / 2 : ℝ) ^ (n + 1) * R) hpos hle
  refine ⟨(2 / R) ^ m * (U R + 1), by positivity, R, hR, ?_⟩
  exact power_bound_of_dyadic m hR hUR hmono hdyadic

/-- The Caccioppoli scaling transfers infinite-order mass decay to energy
when `E(r) ≤ K r⁻² U(2r)`. It consumes two additional orders of mass decay. -/
theorem energy_flat_of_mass_flat {U E : ℝ → ℝ} {K R₀ : ℝ}
    (hK : 0 < K) (hR₀ : 0 < R₀) (hflat : FlatAtZero U)
    (henergy : ∀ r : ℝ, 0 < r → r ≤ R₀ → E r ≤ K / r ^ 2 * U (2 * r)) :
    FlatAtZero E := by
  intro m
  obtain ⟨C, hC, R, hR, hbound⟩ := hflat (m + 2)
  refine ⟨K * C * 2 ^ (m + 2), by positivity, min R₀ (R / 2),
    lt_min hR₀ (by positivity), ?_⟩
  intro r hr hsmall
  have hr₀ : r ≤ R₀ := hsmall.trans (min_le_left _ _)
  have hrR : 2 * r ≤ R := by
    have hh := hsmall.trans (min_le_right R₀ (R / 2))
    linarith
  have hmass := hbound (2 * r) (by linarith) hrR
  calc
    E r ≤ K / r ^ 2 * U (2 * r) := henergy r hr hr₀
    _ ≤ K / r ^ 2 * (C * (2 * r) ^ (m + 2)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (K * C * 2 ^ (m + 2)) * r ^ m := by
      rw [mul_pow, pow_add r m 2]
      field_simp

/-- Natural orders imply every real order, so the preceding definition
recovers the full exponent convention used for infinite-order vanishing
in the paper. This also works for nonpositive orders. -/
theorem FlatAtZero.real_order {U : ℝ → ℝ} (hflat : FlatAtZero U) (m : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧
      ∀ r : ℝ, 0 < r → r ≤ R → U r ≤ C * r ^ m := by
  obtain ⟨n, hn⟩ := exists_nat_gt m
  obtain ⟨C, hC, R, hR, hbound⟩ := hflat n
  refine ⟨C, hC, min R 1, lt_min hR zero_lt_one, ?_⟩
  intro r hr hsmall
  have hrR : r ≤ R := hsmall.trans (min_le_left _ _)
  have hr1 : r ≤ 1 := hsmall.trans (min_le_right _ _)
  have hpower : r ^ n ≤ r ^ m := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 hn.le
  exact (hbound r hr hrR).trans (mul_le_mul_of_nonneg_left hpower hC.le)

end PfHk.InfiniteOrder
