import PfHk.OrdinaryCoordinateH1Multiplier
import PfHk.ScalarSqrtLp
import PfHk.ScalarCoefficientNormAlgebra
import PfHk.ScalarCoordinateFormBound
import GptLean.TransformationsPotentials

/-! Actual L2 coordinate multiplication and scalar form integrability for
L3+L-infinity vector and L^(3/2)+L-infinity scalar coefficients. -/

noncomputable section
namespace PfHk.LpSumCoordinateDomain

open MeasureTheory GptLean GptLean.ElectronicH1Space GptLean.PhysicalPairDuality
open GptLean.PhysicalSourceCoordinates PfHk.CoordinateSobolev
open scoped ENNReal

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem bounded_ae {b : X → ℝ} (hb : MemLp b ∞ μ) :
    ∀ᵐ x ∂μ, |b x| ≤ (eLpNorm b ∞ μ).toReal := by
  filter_upwards [ae_le_eLpNormEssSup (f := b) (μ := μ)] with x hx
  have h := ENNReal.toReal_mono hb.eLpNorm_ne_top hx
  simpa only [eLpNorm_exponent_top, toReal_enorm, Real.norm_eq_abs] using h

variable {N : ℕ}

theorem bounded_coordinate (n : Fin N) (b : Position → ℝ) (hb : MemLp b ∞ volume) :
    MemLp (coordinateCoefficient n b) ∞ volume :=
  memLp_top_of_bound (coordinateCoefficient_measurable n hb.aestronglyMeasurable) _
    (by simpa only [Real.norm_eq_abs, coordinateCoefficient] using ScalarCoordinateFormBound.coordinate_ae n (bounded_ae hb))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem split_multiplier (n : Fin N) (a b c : Position → ℝ)
    (hb : MemLp b ∞ volume) (hc : MemLp c 3 volume)
    (ha : a =ᵐ[volume] fun x => b x + c x) (u : H1 H (Fin N × Fin 3)) :
    MemLp (fun X => coordinateCoefficient n a X • value u X) 2 volume := by
  let hbmul := Classical.choose (ScalarCoefficientNormAlgebra.bounded_multiplier
    (coordinateCoefficient n b) (bounded_coordinate n b hb) (value u))
  have hex := OrdinaryCoordinateH1Multiplier.multiplier n c hc u
  let hcmul := Classical.choose hex
  apply (hbmul.add hcmul).ae_eq
  filter_upwards [ScalarCoordinateFormBound.coordinate_ae n ha] with X hX
  change b (split n X).1 • value u X + c (split n X).1 • value u X =
    a (split n X).1 • value u X
  rw [hX, add_smul]

theorem vector_multiplier (A : VectorPotential) (n : Fin N) (i : Fin 3)
    (u : H1 H (Fin N × Fin 3)) :
    MemLp (fun X => coordinateCoefficient n (fun x => A.val x i) X • value u X) 2 volume := by
  let b : Position → ℝ := fun x => (parts A).1 x i
  let c : Position → ℝ := fun x => (parts A).2 x i
  have hb : MemLp b ∞ volume := (EuclideanSpace.proj i : PhysicalPairSpace.Vector →L[ℝ] ℝ).comp_memLp' (Lp.memLp (parts A).1)
  have hc : MemLp c 3 volume := (EuclideanSpace.proj i : PhysicalPairSpace.Vector →L[ℝ] ℝ).comp_memLp' (Lp.memLp (parts A).2)
  apply split_multiplier n _ b c hb hc _ u
  filter_upwards [TransformationsPotentials.coeFn_parts A] with x hx
  exact congrArg (fun y : PhysicalPairSpace.Vector => y i) hx

private theorem bounded_density (b : Configuration N → ℝ) (hb : MemLp b ∞ volume)
    (u : L2 H (Fin N × Fin 3)) : Integrable (fun X => |b X| * ‖u X‖ ^ 2) volume := by
  apply ((Lp.memLp u).norm.integrable_sq.const_mul (eLpNorm b ∞ volume).toReal).mono'
    (hb.aestronglyMeasurable.norm.mul ((Lp.aestronglyMeasurable u).norm.pow 2))
  filter_upwards [bounded_ae hb] with X hX
  change ‖|b X| * ‖u X‖ ^ 2‖ ≤ (eLpNorm b ∞ volume).toReal * ‖u X‖ ^ 2
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right hX (sq_nonneg _)

private theorem critical_density (n : Fin N) (c : Position → ℝ)
    (hc : MemLp c (3 / 2) volume) (u : H1 H (Fin N × Fin 3)) :
    Integrable (fun X => |coordinateCoefficient n c X| * ‖value u X‖ ^ 2) volume := by
  have hex := OrdinaryCoordinateH1Multiplier.multiplier n (ScalarSqrtLp.amplitude c)
    (ScalarSqrtLp.amplitude_memLp hc) u
  let hm := Classical.choose hex
  apply hm.norm.integrable_sq.congr
  filter_upwards [] with X
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, coordinateCoefficient,
    ScalarSqrtLp.amplitude_sq]

theorem scalar_density (v : ScalarPotential) (n : Fin N) (u : H1 H (Fin N × Fin 3)) :
    Integrable (fun X => |coordinateCoefficient n (v.val : Position → ℝ) X| * ‖value u X‖ ^ 2) volume := by
  have hb := bounded_density (coordinateCoefficient n ((parts v).1 : Position → ℝ))
    (bounded_coordinate n _ (Lp.memLp (parts v).1)) (value u)
  have hc := critical_density n ((parts v).2 : Position → ℝ) (Lp.memLp (parts v).2) u
  apply (hb.add hc).mono'
    ((coordinateCoefficient_measurable n v.val.aestronglyMeasurable).norm.mul
      ((Lp.aestronglyMeasurable (value u)).norm.pow 2))
  filter_upwards [ScalarCoordinateFormBound.coordinate_ae n (TransformationsPotentials.coeFn_parts v)] with X hX
  change ‖|coordinateCoefficient n (v.val : Position → ℝ) X| * ‖value u X‖ ^ 2‖ ≤
    |coordinateCoefficient n ((parts v).1 : Position → ℝ) X| * ‖value u X‖ ^ 2 +
    |coordinateCoefficient n ((parts v).2 : Position → ℝ) X| * ‖value u X‖ ^ 2
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
  change |v.val (split n X).1| * ‖value u X‖ ^ 2 ≤ _
  rw [hX]
  exact (mul_le_mul_of_nonneg_right (abs_add_le _ _) (sq_nonneg _)).trans_eq (add_mul _ _ _)

end PfHk.LpSumCoordinateDomain
