import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
The weighted-density step in the proof of `thm-vector-uniqueness`.
These statements use actual measurable functions and their Lebesgue norms.
No Fourier uniqueness or exponential decay conclusion is an assumption.
-/

noncomputable section

namespace PfHk.WeightedDensity

set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Taking a square root halves the power in the integrability exponent. -/
theorem sqrt_memLp {f : X → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ f x) :
    MemLp (fun x => Real.sqrt (f x)) (p / (1 / 2)) μ := by
  have h := hf.norm_rpow_div (1 / 2)
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h
  apply h.ae_eq
  filter_upwards [hpos] with x hx
  rw [Real.norm_of_nonneg hx, Real.sqrt_eq_rpow]

/-- The exponential moment and the unweighted `L³` bound give the
half-weighted density in `L^(3/2)`. This is the integrability content of
the interpolation inequality in the proof of
`prop-vector-uniqueness`, with a general nonnegative weight. -/
theorem half_weight_memLp {ρ w : X → ℝ}
    (hρ : MemLp ρ 3 μ) (hρpos : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hwpos : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hweighted : Integrable (fun x => w x * ρ x) μ) :
    MemLp (fun x => Real.sqrt (w x) * ρ x) (3 / 2) μ := by
  have h₁ : MemLp (fun x => Real.sqrt (w x * ρ x)) 2 μ := by
    convert sqrt_memLp (memLp_one_iff_integrable.mpr hweighted) ?_ using 1 <;>
      try norm_num [div_eq_mul_inv]
    filter_upwards [hρpos, hwpos] with x hx hy using mul_nonneg hy hx
  have h₂ : MemLp (fun x => Real.sqrt (ρ x)) 6 μ := by
    convert sqrt_memLp hρ hρpos using 1
    norm_num [div_eq_mul_inv]
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) 6 (3 / 2) := by
    exact ENNReal.HolderTriple.of_toReal
      ⟨by norm_num [ENNReal.toReal_div], by norm_num, by norm_num⟩
  have hmul : MemLp
      (fun x => Real.sqrt (w x * ρ x) * Real.sqrt (ρ x)) (3 / 2) μ :=
    h₂.mul' h₁
  apply hmul.ae_eq
  filter_upwards [hρpos, hwpos] with x hx hy
  rw [Real.sqrt_mul hy, mul_assoc, Real.mul_self_sqrt hx]

/-- Multiplication by an `L³` vector potential preserves integrability
of the half-weighted density. -/
theorem half_weight_mul_integrable {ρ w A : X → ℝ}
    (hρ : MemLp ρ 3 μ) (hρpos : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hwpos : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hweighted : Integrable (fun x => w x * ρ x) μ)
    (hA : MemLp A 3 μ) :
    Integrable (fun x => (Real.sqrt (w x) * ρ x) * A x) μ := by
  have : ENNReal.HolderTriple (3 / 2 : ℝ≥0∞) 3 1 := by
    exact ENNReal.HolderTriple.of_toReal
      ⟨by norm_num [ENNReal.toReal_div], by norm_num, by norm_num⟩
  exact memLp_one_iff_integrable.mp (hA.mul' (half_weight_memLp hρ hρpos hwpos hweighted))

/-- A weight at least one also controls its square root in `L¹`. -/
theorem half_weight_integrable {ρ w : X → ℝ}
    (hρ : AEStronglyMeasurable ρ μ) (hw : AEStronglyMeasurable w μ)
    (hρpos : ∀ᵐ x ∂μ, 0 ≤ ρ x) (hwone : ∀ᵐ x ∂μ, 1 ≤ w x)
    (hweighted : Integrable (fun x => w x * ρ x) μ) :
    Integrable (fun x => Real.sqrt (w x) * ρ x) μ := by
  apply hweighted.mono' ((Real.continuous_sqrt.comp_aestronglyMeasurable hw).mul hρ)
  filter_upwards [hρpos, hwone] with x hx hy
  change ‖Real.sqrt (w x) * ρ x‖ ≤ w x * ρ x
  rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hx)]
  apply mul_le_mul_of_nonneg_right _ hx
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by linarith, by nlinarith⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The half-weighted current is integrable for a vector potential
written as the sum of an `L³` function and an essentially bounded one. -/
theorem half_weight_smul_integrable {ρ w : X → ℝ} {A₃ Ainf : X → V}
    (hρ : MemLp ρ 3 μ) (hw : AEStronglyMeasurable w μ)
    (hρpos : ∀ᵐ x ∂μ, 0 ≤ ρ x) (hwone : ∀ᵐ x ∂μ, 1 ≤ w x)
    (hweighted : Integrable (fun x => w x * ρ x) μ)
    (hA₃ : MemLp A₃ 3 μ) (hAinf : MemLp Ainf ∞ μ) :
    Integrable (fun x => (Real.sqrt (w x) * ρ x) • (A₃ x + Ainf x)) μ := by
  have hp : ∀ᵐ x ∂μ, 0 ≤ w x := hwone.mono fun _ hx => le_trans (by norm_num) hx
  have : ENNReal.HolderTriple (3 / 2 : ℝ≥0∞) 3 1 := by
    exact ENNReal.HolderTriple.of_toReal
      ⟨by norm_num [ENNReal.toReal_div], by norm_num, by norm_num⟩
  have h₃ : Integrable (fun x => (Real.sqrt (w x) * ρ x) • A₃ x) μ :=
    memLp_one_iff_integrable.mp (hA₃.smul (half_weight_memLp hρ hρpos hp hweighted))
  have h₁ := memLp_one_iff_integrable.mpr
    (half_weight_integrable hρ.1 hw hρpos hwone hweighted)
  have hinf : Integrable (fun x => (Real.sqrt (w x) * ρ x) • Ainf x) μ :=
    memLp_one_iff_integrable.mp (hAinf.smul h₁)
  exact (h₃.add hinf).congr (ae_of_all _ fun x => (smul_add _ _ _).symm)

section Exponential

variable [NormedAddCommGroup X]

/-- The paper's weighted density has exponent `α/2`. -/
theorem exponential_density_memLp {ρ : X → ℝ} {α : ℝ}
    (hρ : MemLp ρ 3 μ) (hρpos : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hmoment : Integrable (fun x => Real.exp (α * ‖x‖) * ρ x) μ) :
    MemLp (fun x => Real.exp (α * ‖x‖ / 2) * ρ x) (3 / 2) μ := by
  simpa only [← Real.exp_half] using
    half_weight_memLp hρ hρpos (ae_of_all _ fun x => (Real.exp_pos _).le) hmoment

variable [BorelSpace X]

/-- An exponential moment of the density passes to the density-weighted
vector potential at half the exponent. This proves the finiteness assertion
of `b-exponential-moment` for an arbitrary `L³ + L∞` decomposition. -/
theorem exponential_current_integrable {ρ : X → ℝ} {α : ℝ} {A₃ Ainf : X → V}
    (hα : 0 ≤ α) (hρ : MemLp ρ 3 μ) (hρpos : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hmoment : Integrable (fun x => Real.exp (α * ‖x‖) * ρ x) μ)
    (hA₃ : MemLp A₃ 3 μ) (hAinf : MemLp Ainf ∞ μ) :
    Integrable (fun x => (Real.exp (α * ‖x‖ / 2) * ρ x) • (A₃ x + Ainf x)) μ := by
  have hw : AEStronglyMeasurable (fun x : X => Real.exp (α * ‖x‖)) μ :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).aestronglyMeasurable
  have hwone : ∀ᵐ x ∂μ, 1 ≤ Real.exp (α * ‖x‖) :=
    ae_of_all _ fun x => Real.one_le_exp (mul_nonneg hα (norm_nonneg _))
  simpa only [← Real.exp_half] using
    half_weight_smul_integrable hρ hw hρpos hwone hmoment hA₃ hAinf

end Exponential

end PfHk.WeightedDensity
