import GptLean.NormWeakH1
import GptLean.RepresentabilityHardy

/-!
The norm chain rule and the ordinary scalar Hardy inequality give a
Hilbert-valued covariant Hardy bound. The field action is an actual vector
whose expectation is real, as supplied by a symmetric field operator.
The covariant bound is proved from that symmetry, without assuming a
diamagnetic inequality.
-/

noncomputable section

namespace GptLean.Repair

open MeasureTheory Filter SymmetricLift
open scoped ENNReal Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The gradient of a vector's norm is bounded by its covariant derivative
when the field expectation is real. -/
theorem normGradient_le_covariant (f d a : H) (e : ℝ)
    (ha : (inner ℂ f a).im = 0) :
    ‖(inner ℂ f d).re / ‖f‖‖ ≤ ‖(-Complex.I) • d - (e : ℂ) • a‖ := by
  by_cases hf : f = 0
  · subst f
    simp
  have hp : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have him : (inner ℂ f ((-Complex.I) • d - (e : ℂ) • a)).im =
      -(inner ℂ f d).re := by
    rw [inner_sub_right, inner_smul_right, inner_smul_right, Complex.sub_im,
      Complex.mul_im, Complex.mul_im]
    simp [ha]
  have hi := (Complex.abs_im_le_norm
    (inner ℂ f ((-Complex.I) • d - (e : ℂ) • a))).trans
      (norm_inner_le_norm f ((-Complex.I) • d - (e : ℂ) • a))
  rw [him, abs_neg] at hi
  rw [norm_div, norm_norm, Real.norm_eq_abs, div_le_iff₀ hp, mul_comm]
  exact hi

variable [CompleteSpace H]

/-- Explicit scalar norm gradient of a Hilbert-valued field. -/
def normGradient {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → H)
    (df : Fin d → EuclideanSpace ℝ (Fin d) → H) (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ := (inner ℂ (f x) (df i x)).re / ‖f x‖

theorem normGradient_weakH1Local {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → H}
    {df : Fin d → EuclideanSpace ℝ (Fin d) → H}
    (hweak : HasWeakH1Local f df) :
    HasWeakH1Local (fun x => ‖f x‖) (normGradient f df) := by
  letI := InnerProductSpace.rclikeToReal ℂ H
  exact NormWeakH1.norm_weakH1Local hweak

/-- Global square integrability follows from the covariant derivative,
including on the zero set of the source. -/
theorem normGradient_memLp_of_covariant {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → H}
    {df a D : Fin d → EuclideanSpace ℝ (Fin d) → H}
    (hf : MemLp f 2 volume) (hdf : ∀ i, MemLp (df i) 2 volume)
    (hD : ∀ i, MemLp (D i) 2 volume) (e : ℝ)
    (ha : ∀ i, ∀ᵐ x ∂volume, (inner ℂ (f x) (a i x)).im = 0)
    (hcov : ∀ i, ∀ᵐ x ∂volume,
      D i x = (-Complex.I) • df i x - (e : ℂ) • a i x) (i : Fin d) :
    MemLp (normGradient f df i) 2 volume := by
  have hm : AEStronglyMeasurable (normGradient f df i) volume :=
    ((Complex.continuous_re.measurable.comp_aemeasurable
      (hf.1.inner (𝕜 := ℂ) (hdf i).1).aemeasurable).div
        hf.1.norm.aemeasurable).aestronglyMeasurable
  apply (hD i).norm.mono' hm
  filter_upwards [ha i, hcov i] with x hx hDx
  simpa only [normGradient, hDx, norm_norm] using normGradient_le_covariant
    (f x) (df i x) (a i x) e hx

/-- Scalar Hardy applied to the norm has the exact constant four and is
controlled solely by covariant derivative norms. -/
theorem covariant_hardy (Hardy : Representability.StandardScalarHardy)
    {f : EuclideanSpace ℝ (Fin 3) → H}
    {df a D : Fin 3 → EuclideanSpace ℝ (Fin 3) → H}
    (hweak : HasWeakH1Local f df)
    (hf : MemLp f 2 volume) (hdf : ∀ i, MemLp (df i) 2 volume)
    (hD : ∀ i, MemLp (D i) 2 volume) (e : ℝ)
    (ha : ∀ i, ∀ᵐ x ∂volume, (inner ℂ (f x) (a i x)).im = 0)
    (hcov : ∀ i, ∀ᵐ x ∂volume,
      D i x = (-Complex.I) • df i x - (e : ℂ) • a i x)
    (y : EuclideanSpace ℝ (Fin 3)) :
    Integrable (fun x => (‖x - y‖ ^ 2)⁻¹ * ‖f x‖ ^ 2) volume ∧
      (∫ x, (‖x - y‖ ^ 2)⁻¹ * ‖f x‖ ^ 2) ≤
        4 * ∑ i : Fin 3, (eLpNorm (D i) 2 volume).toReal ^ 2 := by
  obtain ⟨hint, hbound⟩ := Hardy.estimate (fun x => ‖f x‖) (normGradient f df)
    (normGradient_weakH1Local hweak) hf.norm
    (normGradient_memLp_of_covariant hf hdf hD e ha hcov) y
  simp only [norm_norm] at hint hbound
  refine ⟨hint, hbound.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply pow_le_pow_left₀ ENNReal.toReal_nonneg
  apply ENNReal.toReal_mono (hD i).2.ne
  apply eLpNorm_mono_ae
  filter_upwards [ha i, hcov i] with x hx hDx
  rw [hDx]
  exact normGradient_le_covariant (f x) (df i x) (a i x) e hx

end GptLean.Repair
