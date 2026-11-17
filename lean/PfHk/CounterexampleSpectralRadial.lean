import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Tactic

/-! The radial hydrogen factorization and the angular estimate used by the
zero-coupling example. The radial integration-by-parts identities are the
usual half-line Sobolev core identities. The factorization and all estimates
depending on the magnetic parameter are proved here. -/

noncomputable section
namespace PfHk.CounterexampleSpectral

open MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

abbrev radialMeasure : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A zero-trace radial H1 profile, with its actual weak derivative and the
two multiplication coordinates. The IBP identities are standard radial
core calculus and contain neither a Coulomb parameter nor a magnetic one. -/
structure RadialProfile where
  value : Lp E 2 radialMeasure
  derivative : Lp E 2 radialMeasure
  inverseRadius : Lp E 2 radialMeasure
  rotationWeight : Lp E 2 radialMeasure
  inverseRadius_ae : inverseRadius =ᵐ[radialMeasure] fun r => r⁻¹ • value r
  rotationWeight_ae : rotationWeight =ᵐ[radialMeasure]
    fun r => (Real.sqrt (1 + r ^ 2))⁻¹ • value r
  weak : ∀ η : ℝ → ℝ, ContDiff ℝ ⊤ η → HasCompactSupport η →
    tsupport η ⊆ Set.Ioi 0 →
    (∫ r, deriv η r • value r ∂radialMeasure) =
      -(∫ r, η r • derivative r ∂radialMeasure)
  ibp_inverseRadius : inner ℝ derivative inverseRadius = (1 / 2 : ℝ) * ‖inverseRadius‖ ^ 2
  ibp_constant : inner ℝ derivative value = 0

variable {E}

def radialExcess (Z : ℝ) (u : RadialProfile E) : ℝ :=
  (1 / 2 : ℝ) * ‖u.derivative‖ ^ 2 - Z * inner ℝ u.inverseRadius u.value +
    (Z ^ 2 / 2) * ‖u.value‖ ^ 2

def radialFactor (Z : ℝ) (u : RadialProfile E) : Lp E 2 radialMeasure :=
  u.derivative - u.inverseRadius + Z • u.value

/-- The displayed hydrogenic factorization follows from the two radial
integration-by-parts identities, rather than being a spectral assumption. -/
theorem radial_factorization (Z : ℝ) (u : RadialProfile E) :
    radialExcess Z u = (1 / 2 : ℝ) * ‖radialFactor Z u‖ ^ 2 := by
  unfold radialExcess radialFactor
  rw [norm_add_sq_real, norm_sub_sq_real, real_inner_smul_right, inner_sub_left,
    u.ibp_inverseRadius, u.ibp_constant, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem radialExcess_nonneg (Z : ℝ) (u : RadialProfile E) : 0 ≤ radialExcess Z u := by
  rw [radial_factorization]
  positivity

theorem radialExcess_eq_zero_iff (Z : ℝ) (u : RadialProfile E) :
    radialExcess Z u = 0 ↔ radialFactor Z u = 0 := by
  rw [radial_factorization]
  simp

theorem radial_rotationWeight_le (u : RadialProfile E) :
    ‖u.rotationWeight‖ ^ 2 ≤ ‖u.inverseRadius‖ ^ 2 := by
  have hn : ‖u.rotationWeight‖ ≤ ‖u.inverseRadius‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [u.rotationWeight_ae, u.inverseRadius_ae,
      (ae_restrict_mem measurableSet_Ioi : ∀ᵐ r ∂radialMeasure, r ∈ Set.Ioi 0)]
      with r hr hi hpos
    rw [hr, hi, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
      abs_of_pos (inv_pos.mpr hpos)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply inv_anti₀ hpos
    exact (Real.le_sqrt (le_of_lt hpos) (by positivity)).2 (by nlinarith)
  nlinarith [norm_nonneg u.rotationWeight, norm_nonneg u.inverseRadius]

theorem radial_value_eq_zero_of_inverseRadius_eq_zero (u : RadialProfile E)
    (h : u.inverseRadius = 0) : u.value = 0 := by
  apply Lp.ext
  filter_upwards [u.inverseRadius_ae, Lp.coeFn_zero E 2 radialMeasure,
    (ae_restrict_mem measurableSet_Ioi : ∀ᵐ r ∂radialMeasure, r ∈ Set.Ioi 0)]
    with r hr hz hpos
  have hv : r⁻¹ • u.value r = 0 := by simpa only [h, hz, Pi.zero_apply] using hr.symm
  simpa only [hz, Pi.zero_apply] using
    (smul_eq_zero.mp hv).resolve_left (inv_ne_zero (ne_of_gt hpos))

/-- The standard one-dimensional weak ODE uniqueness principle, stated for
an arbitrary nonvanishing C1 integrating factor. It has no hydrogenic or
magnetic parameter among its hypotheses. -/
structure StandardRadialWeakODE : Prop where
  integrating_factor : ∀ (u : RadialProfile E) (f df : ℝ → ℝ),
    (∀ r, 0 < r → HasDerivAt f (df r) r) →
    ContinuousOn df (Set.Ioi 0) →
    (∀ r, 0 < r → f r ≠ 0) →
    (u.derivative =ᵐ[radialMeasure] fun r => (df r / f r) • u.value r) →
    ∃ c : E, u.value =ᵐ[radialMeasure] fun r => f r • c

theorem radial_kernel (O : StandardRadialWeakODE (E := E)) (Z : ℝ)
    (u : RadialProfile E) (h : radialExcess Z u = 0) :
    ∃ c : E, u.value =ᵐ[radialMeasure]
      fun r => (r * Real.exp (-Z * r)) • c := by
  have hf : radialFactor Z u = 0 := (radialExcess_eq_zero_iff Z u).mp h
  apply O.integrating_factor u (fun r => r * Real.exp (-Z * r))
    (fun r => (1 - Z * r) * Real.exp (-Z * r))
  · intro r _
    have hd := (hasDerivAt_id r).mul (((hasDerivAt_id r).const_mul (-Z)).exp)
    convert hd using 1 <;> try rfl
    all_goals
      simp only [id_eq, one_mul, mul_one]
      ring
  · exact (by fun_prop : Continuous
      (fun r : ℝ => (1 - Z * r) * Real.exp (-Z * r))).continuousOn
  · intro r hr
    exact mul_ne_zero (ne_of_gt hr) (Real.exp_ne_zero _)
  · filter_upwards [u.inverseRadius_ae,
      Lp.coeFn_sub u.derivative u.inverseRadius,
      Lp.coeFn_add (u.derivative - u.inverseRadius) (Z • u.value),
      Lp.coeFn_smul Z u.value,
      Lp.coeFn_zero E 2 radialMeasure,
      (ae_restrict_mem measurableSet_Ioi : ∀ᵐ r ∂radialMeasure, r ∈ Set.Ioi 0)]
      with r hi hs ha hsm hz hr
    have hfactor : u.derivative r - r⁻¹ • u.value r + Z • u.value r = 0 := by
      have hp := congrArg (fun f : Lp E 2 radialMeasure => f r) hf
      simpa only [radialFactor, ha, Pi.add_apply, hs, Pi.sub_apply, hsm,
        Pi.smul_apply, hi, hz, Pi.zero_apply] using hp
    have hd : u.derivative r = (r⁻¹ - Z) • u.value r := by
      rw [sub_smul]
      calc
        u.derivative r = (u.derivative r - r⁻¹ • u.value r + Z • u.value r) +
            (r⁻¹ • u.value r - Z • u.value r) := by abel
        _ = r⁻¹ • u.value r - Z • u.value r := by rw [hfactor, zero_add]
    rw [hd]
    congr 1
    have hr0 : 0 < r := hr
    field_simp [ne_of_gt hr0, Real.exp_ne_zero]

/-- A spherical-harmonic index. -/
def AngularIndex := {p : ℕ × ℤ // |p.2| ≤ (p.1 : ℤ)}

def degree (c : AngularIndex) : ℕ := c.val.1
def order (c : AngularIndex) : ℤ := c.val.2

def zeroChannel : AngularIndex := ⟨(0, 0), by simp⟩

theorem order_abs_le_degree (c : AngularIndex) : |(order c : ℝ)| ≤ degree c := by
  exact_mod_cast c.property

theorem degree_pos_of_ne_zero {c : AngularIndex} (h : c ≠ zeroChannel) : 0 < degree c := by
  by_contra hn
  have hl : c.val.1 = 0 := Nat.eq_zero_of_not_pos hn
  have hm : c.val.2 = 0 := by
    have hb : |c.val.2| ≤ 0 := by simpa only [hl, Nat.cast_zero] using c.property
    exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
  apply h
  apply Subtype.ext
  exact Prod.ext hl hm

def centrifugal (c : AngularIndex) : ℝ := (degree c : ℝ) * (degree c + 1) / 2

theorem centrifugal_nonneg (c : AngularIndex) : 0 ≤ centrifugal c := by
  unfold centrifugal
  positivity

theorem order_abs_le_centrifugal (c : AngularIndex) :
    |(order c : ℝ)| ≤ centrifugal c := by
  by_cases hl : degree c = 0
  · have hm := order_abs_le_degree c
    simpa [centrifugal, hl] using hm
  · have h1 : (1 : ℝ) ≤ degree c := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hl
    have hm := order_abs_le_degree c
    unfold centrifugal
    nlinarith

def angularEnergy (t : ℝ) (c : AngularIndex) (u : RadialProfile E) : ℝ :=
  centrifugal c * ‖u.inverseRadius‖ ^ 2 + t * order c * ‖u.rotationWeight‖ ^ 2

theorem angular_lower_bound (t : ℝ) (c : AngularIndex) (u : RadialProfile E) :
    (1 - |t|) * centrifugal c * ‖u.inverseRadius‖ ^ 2 ≤ angularEnergy t c u := by
  have hw := radial_rotationWeight_le u
  have hm := order_abs_le_centrifugal c
  have htm : -(t * (order c : ℝ)) ≤ |t| * centrifugal c := by
    calc
      -(t * (order c : ℝ)) ≤ |t * (order c : ℝ)| := neg_le_abs _
      _ = |t| * |(order c : ℝ)| := abs_mul _ _
      _ ≤ |t| * centrifugal c := mul_le_mul_of_nonneg_left hm (abs_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right htm (sq_nonneg ‖u.rotationWeight‖)
  have hw' := mul_le_mul_of_nonneg_left hw
    (mul_nonneg (abs_nonneg t) (centrifugal_nonneg c))
  unfold angularEnergy
  nlinarith

theorem angularEnergy_nonneg {t : ℝ} (ht : |t| ≤ 1)
    (c : AngularIndex) (u : RadialProfile E) : 0 ≤ angularEnergy t c u :=
  (mul_nonneg (mul_nonneg (sub_nonneg.mpr ht) (centrifugal_nonneg c))
    (sq_nonneg _)).trans (angular_lower_bound t c u)

theorem radial_value_eq_zero_of_angular_zero {t : ℝ} (ht : |t| < 1)
    {c : AngularIndex} (hc : c ≠ zeroChannel) (u : RadialProfile E)
    (h : angularEnergy t c u = 0) : u.value = 0 := by
  have hp : 0 < (1 - |t|) * centrifugal c := by
    apply mul_pos (sub_pos.mpr ht)
    unfold centrifugal
    have hd : (0 : ℝ) < degree c := by exact_mod_cast degree_pos_of_ne_zero hc
    positivity
  have hb := angular_lower_bound t c u
  have hz : ‖u.inverseRadius‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖u.inverseRadius‖]
  apply radial_value_eq_zero_of_inverseRadius_eq_zero u
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

end PfHk.CounterexampleSpectral
