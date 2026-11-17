import PfHk.CounterexampleSpectral

/-! Parameter-free cylindrical Sobolev profiles and the shifted radial
square used by the spinful counterexample. The cylindrical Fourier
transform is unitary after multiplication by the square root of the
cylindrical radius. The derivative coordinates below are conjugated by
that unitary map. Only the ordinary radial integration-by-parts identity
is included in a profile. The hydrogen factorization and angular
estimates are proved rather than supplied as background assumptions. -/

noncomputable section
namespace PfHk.SpinfulCounterexampleSpectral

open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

abbrev cylindricalMeasure : Measure (ℝ × ℝ) :=
  (volume : Measure (ℝ × ℝ)).restrict {p | 0 < p.1}

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radial, meridional and multiplication coordinates of one circular
Fourier mode. The measure is `ds dz` on `s > 0`, with `sqrt s` incorporated
in the unitary transform. `radial` is the transform of the ordinary
three-dimensional radial derivative and `meridional` its orthogonal
component in the `(s,z)` plane. -/
structure CylindricalProfile (m : ℤ) where
  value : Lp E 2 cylindricalMeasure
  radial : Lp E 2 cylindricalMeasure
  meridional : Lp E 2 cylindricalMeasure
  inverseRadius : Lp E 2 cylindricalMeasure
  inverseCylinder : Lp E 2 cylindricalMeasure
  rotationWeight : Lp E 2 cylindricalMeasure
  inverseRadius_ae : inverseRadius =ᵐ[cylindricalMeasure]
    fun p => (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹ • value p
  inverseCylinder_ae : inverseCylinder =ᵐ[cylindricalMeasure]
    fun p => if m = 0 then 0 else p.1⁻¹ • value p
  rotationWeight_ae : rotationWeight =ᵐ[cylindricalMeasure]
    fun p => (Real.sqrt (1 + p.1 ^ 2))⁻¹ • value p
  radial_ibp : inner ℝ radial value = -inner ℝ inverseRadius value

variable {E}

def modeKinetic (m : ℤ) (u : CylindricalProfile E m) : ℝ :=
  (1 / 2 : ℝ) * (‖u.radial‖ ^ 2 + ‖u.meridional‖ ^ 2 +
    (m : ℝ) ^ 2 * ‖u.inverseCylinder‖ ^ 2)

def modeExcess (Z : ℝ) (m : ℤ) (u : CylindricalProfile E m) : ℝ :=
  modeKinetic m u - Z * inner ℝ u.inverseRadius u.value +
    (Z ^ 2 / 2) * ‖u.value‖ ^ 2

def modeFactor {m : ℤ} (Z : ℝ) (u : CylindricalProfile E m) : Lp E 2 cylindricalMeasure :=
  u.radial + Z • u.value

/-- Completing the radial square follows from parameter-free IBP. -/
theorem mode_factorization (Z : ℝ) (m : ℤ) (u : CylindricalProfile E m) :
    modeExcess Z m u = (1 / 2 : ℝ) * ‖modeFactor Z u‖ ^ 2 +
      (1 / 2 : ℝ) * ‖u.meridional‖ ^ 2 +
      (1 / 2 : ℝ) * (m : ℝ) ^ 2 * ‖u.inverseCylinder‖ ^ 2 := by
  unfold modeExcess modeKinetic modeFactor
  rw [norm_add_sq_real, real_inner_smul_right, u.radial_ibp,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem mode_excess_nonneg (Z : ℝ) (m : ℤ) (u : CylindricalProfile E m) :
    0 ≤ modeExcess Z m u := by
  rw [mode_factorization]
  positivity

theorem mode_angular_le (Z : ℝ) (m : ℤ) (u : CylindricalProfile E m) :
    (m : ℝ) ^ 2 * ‖u.inverseCylinder‖ ^ 2 ≤ 2 * modeExcess Z m u := by
  rw [mode_factorization]
  nlinarith [sq_nonneg ‖modeFactor Z u‖, sq_nonneg ‖u.meridional‖]

theorem rotation_weight_le {m : ℤ} (hm : m ≠ 0) (u : CylindricalProfile E m) :
    ‖u.rotationWeight‖ ^ 2 ≤ ‖u.inverseCylinder‖ ^ 2 := by
  have hn : ‖u.rotationWeight‖ ≤ ‖u.inverseCylinder‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [u.rotationWeight_ae, u.inverseCylinder_ae,
      (ae_restrict_mem (measurableSet_lt measurable_const measurable_fst) :
        ∀ᵐ p ∂cylindricalMeasure, 0 < p.1)] with p hw hi hp
    rw [hw, hi, ite_eq_right_iff.mpr (fun h => (hm h).elim), norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
      abs_of_pos (inv_pos.mpr hp)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply inv_anti₀ hp
    exact (Real.le_sqrt (le_of_lt hp) (by positivity)).2 (by nlinarith)
  nlinarith [norm_nonneg u.rotationWeight, norm_nonneg u.inverseCylinder]

theorem integer_abs_le_square (m : ℤ) : |(m : ℝ)| ≤ (m : ℝ) ^ 2 := by
  by_cases hm : m = 0
  · simp [hm]
  · have hm' : (1 : ℤ) ≤ |m| := by
      have h := abs_pos.mpr hm
      omega
    have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast hm'
    nlinarith [sq_abs (m : ℝ)]

/-- The integer spacing of circular Fourier modes is the reason the
linear angular perturbation is controlled by angular kinetic energy. -/
theorem mode_rotation_abs_le (Z : ℝ) (m : ℤ) (u : CylindricalProfile E m) :
    |(m : ℝ) * ‖u.rotationWeight‖ ^ 2| ≤ 2 * modeExcess Z m u := by
  by_cases hm : m = 0
  · subst m
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mode_excess_nonneg Z 0 u)
  rw [abs_mul, abs_of_nonneg (sq_nonneg ‖u.rotationWeight‖)]
  calc
    |(m : ℝ)| * ‖u.rotationWeight‖ ^ 2 ≤
        (m : ℝ) ^ 2 * ‖u.rotationWeight‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (integer_abs_le_square m) (sq_nonneg _)
    _ ≤ (m : ℝ) ^ 2 * ‖u.inverseCylinder‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (rotation_weight_le hm u) (sq_nonneg _)
    _ ≤ 2 * modeExcess Z m u := mode_angular_le Z m u

end PfHk.SpinfulCounterexampleSpectral
