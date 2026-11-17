import PfHk.OrdinaryCoordinateH1Multiplier
import PfHk.ScalarSqrtLp
import PfHk.PhysicalLocalEnergySobolev

/-! Coordinate scalar form estimates from the actual ordinary H1 graph.
The critical L^(3/2) bound is derived from the proved three-dimensional
Hilbert-valued Sobolev theorem, Hölder, and Fubini. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.ScalarCoordinateFormBound

open MeasureTheory GptLean GptLean.ElectronicH1Space
open GptLean.PhysicalSourceCoordinates PfHk.CoordinateSobolev
open scoped ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
set_option maxHeartbeats 200000

variable {N : ℕ}

def complexH1 (f : Configuration N → ℝ) (g : (Fin N × Fin 3) → Configuration N → ℝ)
    (hw : SymmetricLift.HasWeakH1Local f g) (hf : MemLp f 2 volume)
    (hg : ∀ i, MemLp (g i) 2 volume) : H1 ℂ (Fin N × Fin 3) :=
  ofFunctions (fun x => (f x : ℂ)) (fun i x => (g i x : ℂ)) hf.ofReal
    (fun i => (hg i).ofReal) (Repair.weakH1Local_map Complex.ofRealCLM hw)

theorem complexH1_value_ae (f : Configuration N → ℝ) (g : (Fin N × Fin 3) → Configuration N → ℝ)
    (hw : SymmetricLift.HasWeakH1Local f g) (hf : MemLp f 2 volume)
    (hg : ∀ i, MemLp (g i) 2 volume) :
    (value (complexH1 f g hw hf hg) : Configuration N → ℂ) =ᵐ[volume]
      (fun x => (f x : ℂ)) := (hf.ofReal (K := ℂ)).coeFn_toLp

private theorem real_complex_norm_sq (r : ℝ) : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem complexH1_norm_bound (f : Configuration N → ℝ)
    (g : (Fin N × Fin 3) → Configuration N → ℝ)
    (hw : SymmetricLift.HasWeakH1Local f g) (hf : MemLp f 2 volume)
    (hg : ∀ i, MemLp (g i) 2 volume) :
    ‖complexH1 f g hw hf hg‖ ^ 2 ≤
      (∫ x, f x ^ 2) + ∑ i, ∫ x, g i x ^ 2 := by
  have hv : ‖value (complexH1 f g hw hf hg)‖ ^ 2 = ∫ x, f x ^ 2 := by
    change ‖(hf.ofReal (K := ℂ)).toLp _‖ ^ 2 = _
    exact (Repair.toL2_norm_sq _).trans (integral_congr_ae (Filter.Eventually.of_forall
      fun x => real_complex_norm_sq (f x)))
  have hd : derivativeEnergy (complexH1 f g hw hf hg) = ∑ i, ∫ x, g i x ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    change ‖((hg i).ofReal (K := ℂ)).toLp _‖ ^ 2 = _
    exact (Repair.toL2_norm_sq _).trans (integral_congr_ae (Filter.Eventually.of_forall
      fun x => real_complex_norm_sq (g i x)))
  exact (OrdinaryCoordinateH1Multiplier.h1_norm_sq_bound _).trans_eq (congrArg₂ (· + ·) hv hd)

attribute [local irreducible] complexH1 value derivative gradient

theorem square_multiplier (n : Fin N) (b : Position → ℝ) (hb : MemLp b 3 volume)
    (f : Configuration N → ℝ) (g : (Fin N × Fin 3) → Configuration N → ℝ)
    (hw : SymmetricLift.HasWeakH1Local f g) (hf : MemLp f 2 volume)
    (hg : ∀ i, MemLp (g i) 2 volume) :
    Integrable (fun x => coordinateCoefficient n b x ^ 2 * f x ^ 2) volume ∧
    (∫ x, coordinateCoefficient n b x ^ 2 * f x ^ 2) ≤
      OrdinaryCoordinateH1Multiplier.constant ℂ n * (eLpNorm b 3 volume).toReal ^ 2 *
        ((∫ x, f x ^ 2) + ∑ i, ∫ x, g i x ^ 2) := by
  let u := complexH1 f g hw hf hg
  have hex := OrdinaryCoordinateH1Multiplier.multiplier n b hb u
  let hm := Classical.choose hex
  have hbound := Classical.choose_spec hex
  have he : (fun x => ‖coordinateCoefficient n b x • value u x‖ ^ 2) =ᵐ[volume]
      (fun x => coordinateCoefficient n b x ^ 2 * f x ^ 2) := by
    filter_upwards [complexH1_value_ae f g hw hf hg] with x hx
    change value u x = (f x : ℂ) at hx
    rw [hx, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_complex_norm_sq]
  have hi := hm.norm.integrable_sq.congr he
  refine ⟨hi, ?_⟩
  have hn := (Repair.toL2_norm_sq hm).trans (integral_congr_ae he)
  exact hn.symm.le.trans (hbound.trans (mul_le_mul_of_nonneg_left
    (complexH1_norm_bound f g hw hf hg)
    (mul_nonneg (OrdinaryCoordinateH1Multiplier.constant_nonneg n) (sq_nonneg _))))

theorem critical_multiplier (n : Fin N) (c : Position → ℝ) (hc : MemLp c (3 / 2) volume)
    (f : Configuration N → ℝ) (g : (Fin N × Fin 3) → Configuration N → ℝ)
    (hw : SymmetricLift.HasWeakH1Local f g) (hf : MemLp f 2 volume)
    (hg : ∀ i, MemLp (g i) 2 volume) :
    Integrable (fun x => |coordinateCoefficient n c x| * f x ^ 2) volume ∧
    (∫ x, |coordinateCoefficient n c x| * f x ^ 2) ≤
      OrdinaryCoordinateH1Multiplier.constant ℂ n * (eLpNorm c (3 / 2) volume).toReal *
        ((∫ x, f x ^ 2) + ∑ i, ∫ x, g i x ^ 2) := by
  have h := square_multiplier n (ScalarSqrtLp.amplitude c)
    (ScalarSqrtLp.amplitude_memLp hc) f g hw hf hg
  simpa only [coordinateCoefficient, ScalarSqrtLp.amplitude_sq,
    ScalarSqrtLp.amplitude_norm_sq] using h

theorem coordinate_ae {P : Position → Prop} (n : Fin N) (h : ∀ᵐ x ∂volume, P x) :
    ∀ᵐ x ∂volume, P (split n x).1 :=
  (split_measurePreserving n).quasiMeasurePreserving.ae
    (Measure.quasiMeasurePreserving_fst.ae h)

theorem bounded_multiplier (n : Fin N) (b : Position → ℝ) (hb : MemLp b ∞ volume)
    (f : Configuration N → ℝ) (hf : MemLp f 2 volume) :
    Integrable (fun x => |coordinateCoefficient n b x| * f x ^ 2) volume ∧
    (∫ x, |coordinateCoefficient n b x| * f x ^ 2) ≤
      (eLpNorm b ∞ volume).toReal * ∫ x, f x ^ 2 := by
  have hbn : ∀ᵐ x ∂volume, |b x| ≤ (eLpNorm b ∞ volume).toReal := by
    filter_upwards [ae_le_eLpNormEssSup (f := b) (μ := volume)] with x hx
    have h := ENNReal.toReal_mono hb.eLpNorm_ne_top hx
    simpa only [eLpNorm_exponent_top, toReal_enorm, Real.norm_eq_abs] using h
  have he : ∀ᵐ x ∂volume, |coordinateCoefficient n b x| * f x ^ 2 ≤
      (eLpNorm b ∞ volume).toReal * f x ^ 2 :=
    (coordinate_ae n hbn).mono fun x hx => mul_le_mul_of_nonneg_right hx (sq_nonneg _)
  have hi : Integrable (fun x => |coordinateCoefficient n b x| * f x ^ 2) volume :=
    (hf.integrable_sq.const_mul _).mono'
      ((coordinateCoefficient_measurable n hb.aestronglyMeasurable).norm.mul
        (hf.aestronglyMeasurable.pow 2))
      (he.mono fun x hx => (Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))).le.trans hx)
  exact ⟨hi, (integral_mono_ae hi (hf.integrable_sq.const_mul _) he).trans_eq
    (integral_const_mul _ _)⟩

end PfHk.ScalarCoordinateFormBound

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
