import PfHk.ScalarCommutatorEstimate
import PfHk.L2ScalarNorm
import PfHk.DyadicIntegralBounds
import GptLean.Repair.TraceChannel

/-! Variable derivative weights in the actual cutoff commutator estimate.
This retains the exponential weight pointwise, avoiding an exponential loss
from replacing it by its supremum over an annulus. -/

noncomputable section
namespace PfHk.PhysicalCutoffCommutator

open MeasureTheory GptLean.ElectronicH1Space

set_option maxHeartbeats 20000
set_option Elab.async false

private theorem weighted_two_sum {J : Type*} (S : Finset J) (c g l : J → ℝ)
    (d p : ℝ) :
    (∑ j ∈ S, c j * (2 * g j * d + (1 / 2 : ℝ) * l j * p)) =
      2 * ((∑ j ∈ S, c j * g j) * d) +
        (1 / 2 : ℝ) * ((∑ j ∈ S, c j * l j) * p) := by
  calc
    _ = ∑ j ∈ S, ((2 * d) * (c j * g j) + ((1 / 2 : ℝ) * p) * (c j * l j)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring

variable {I H : Type} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem scalar_weighted_variable_commutator_bound
    (a : TwiceDifferentiableMultiplier I) (ψ : L2 H I) (D : I → L2 H I)
    (w G L : EuclideanSpace ℝ I → ℝ)
    (hwm : AEStronglyMeasurable w volume) (hw : ∀ x, 0 ≤ w x)
    (hgrad : ∀ x, (∑ i, a.scalar.gradient i x ^ 2) ≤ G x)
    (hlap : ∀ x, laplacian a x ^ 2 ≤ L x)
    (hGI : Integrable (fun x => w x * G x * (∑ i, ‖D i x‖ ^ 2)) volume)
    (hLI : Integrable (fun x => w x * L x * ‖ψ x‖ ^ 2) volume) :
    Integrable (fun x => w x * ‖scalarCommutator a ψ D x‖ ^ 2) volume ∧
      (∫ x, w x * ‖scalarCommutator a ψ D x‖ ^ 2) ≤
        2 * (∫ x, w x * G x * (∑ i, ‖D i x‖ ^ 2)) +
          (1 / 2 : ℝ) * (∫ x, w x * L x * ‖ψ x‖ ^ 2) := by
  let f := fun x => w x * ‖scalarCommutator a ψ D x‖ ^ 2
  let b := fun x => 2 * (w x * G x * (∑ i, ‖D i x‖ ^ 2)) +
    (1 / 2 : ℝ) * (w x * L x * ‖ψ x‖ ^ 2)
  have hbi : Integrable b volume := (hGI.const_mul 2).add (hLI.const_mul (1 / 2))
  have hfb : f ≤ᵐ[volume] b := by
    filter_upwards [scalar_commutator_norm_sq_ae a ψ D] with x hx
    have hg := mul_le_mul_of_nonneg_right (hgrad x)
      (Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg ‖D i x‖)
    have hl := mul_le_mul_of_nonneg_right (hlap x) (sq_nonneg ‖ψ x‖)
    have hc : ‖scalarCommutator a ψ D x‖ ^ 2 ≤
        2 * G x * (∑ i, ‖D i x‖ ^ 2) + (1 / 2 : ℝ) * L x * ‖ψ x‖ ^ 2 := by
      exact hx.trans (add_le_add (by nlinarith only [hg]) (by nlinarith only [hl]))
    have hwc := mul_le_mul_of_nonneg_left hc (hw x)
    dsimp [f, b]
    exact hwc.trans_eq (by ring)
  have hfi : Integrable f volume := hbi.mono'
    (hwm.mul ((Lp.aestronglyMeasurable (scalarCommutator a ψ D)).norm.pow 2)) (by
      filter_upwards [hfb] with x hx
      change |w x * ‖scalarCommutator a ψ D x‖ ^ 2| ≤ b x
      rw [abs_of_nonneg (mul_nonneg (hw x) (sq_nonneg _))]
      exact hx)
  refine ⟨hfi, (integral_mono_ae hfi hbi hfb).trans_eq ?_⟩
  rw [integral_add (hGI.const_mul 2) (hLI.const_mul (1 / 2)),
    integral_const_mul, integral_const_mul]

/-- Summed derivative bounds control the actual finite family of cutoff
commutators. The scalar weights remain at the integration point. -/
theorem scalar_commutator_sum_bound {J : Type*} (S : Finset J)
    (a : J → TwiceDifferentiableMultiplier I) (c : J → ℝ)
    (hc : ∀ j ∈ S, 0 ≤ c j) (ψ : L2 H I) (D : I → L2 H I)
    (G L : EuclideanSpace ℝ I → ℝ)
    (hgrad : ∀ x, (∑ j ∈ S, c j * (∑ i, (a j).scalar.gradient i x ^ 2)) ≤ G x)
    (hlap : ∀ x, (∑ j ∈ S, c j * laplacian (a j) x ^ 2) ≤ L x)
    (hGI : Integrable (fun x => G x * (∑ i, ‖D i x‖ ^ 2)) volume)
    (hLI : Integrable (fun x => L x * ‖ψ x‖ ^ 2) volume) :
    (∑ j ∈ S, c j * (∫ x, ‖scalarCommutator (a j) ψ D x‖ ^ 2)) ≤
      2 * (∫ x, G x * (∑ i, ‖D i x‖ ^ 2)) +
        (1 / 2 : ℝ) * (∫ x, L x * ‖ψ x‖ ^ 2) := by
  classical
  let q := fun j x => c j * ‖scalarCommutator (a j) ψ D x‖ ^ 2
  let b := fun x => 2 * (G x * (∑ i, ‖D i x‖ ^ 2)) +
    (1 / 2 : ℝ) * (L x * ‖ψ x‖ ^ 2)
  have hqi (j : J) : Integrable (q j) volume :=
    (Lp.memLp (scalarCommutator (a j) ψ D)).norm.integrable_sq.const_mul _
  have hbi : Integrable b volume := (hGI.const_mul 2).add (hLI.const_mul (1 / 2))
  have hall : ∀ᵐ x ∂volume, ∀ j : S,
      ‖scalarCommutator (a j) ψ D x‖ ^ 2 ≤
        2 * (∑ i, (a j).scalar.gradient i x ^ 2) * (∑ i, ‖D i x‖ ^ 2) +
        (1 / 2 : ℝ) * laplacian (a j) x ^ 2 * ‖ψ x‖ ^ 2 :=
    ae_all_iff.mpr fun j => scalar_commutator_norm_sq_ae (a j) ψ D
  have hsum : (fun x => ∑ j ∈ S, q j x) ≤ᵐ[volume] b := by
    filter_upwards [hall] with x hx
    calc
      _ ≤ ∑ j ∈ S, c j *
          (2 * (∑ i, (a j).scalar.gradient i x ^ 2) * (∑ i, ‖D i x‖ ^ 2) +
            (1 / 2 : ℝ) * laplacian (a j) x ^ 2 * ‖ψ x‖ ^ 2) :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hx ⟨j, hj⟩) (hc j hj)
      _ = 2 * ((∑ j ∈ S, c j * (∑ i, (a j).scalar.gradient i x ^ 2)) *
          (∑ i, ‖D i x‖ ^ 2)) +
          (1 / 2 : ℝ) * ((∑ j ∈ S, c j * laplacian (a j) x ^ 2) * ‖ψ x‖ ^ 2) := by
        exact weighted_two_sum S c _ _ _ _
      _ ≤ b x := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hgrad x)
            (Finset.sum_nonneg fun i _ => sq_nonneg ‖D i x‖)) (by norm_num))
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hlap x)
            (sq_nonneg ‖ψ x‖)) (by norm_num))
  calc
    _ = ∫ x, ∑ j ∈ S, q j x := by
      rw [integral_finsetSum S (fun j _ => hqi j)]
      simp only [q, integral_const_mul]
    _ ≤ ∫ x, b x := integral_mono_ae (integrable_finsetSum S (fun j _ => hqi j)) hbi hsum
    _ = _ := by
      rw [integral_add (hGI.const_mul 2) (hLI.const_mul (1 / 2))]
      simp only [integral_const_mul]

theorem scalar_multiplier_norm_sum_bound {J : Type*} (S : Finset J)
    (a : J → TwiceDifferentiableMultiplier I) (c : J → ℝ)
    (f : L2 H I) (W : EuclideanSpace ℝ I → ℝ)
    (hweight : ∀ x, (∑ j ∈ S, c j * (a j).scalar.weight x ^ 2) ≤ W x)
    (hWI : Integrable (fun x => W x * ‖f x‖ ^ 2) volume) :
    (∑ j ∈ S, c j * ‖(a j).scalar.multiplier (H := H) f‖ ^ 2) ≤
      ∫ x, W x * ‖f x‖ ^ 2 := by
  classical
  have hall : ∀ᵐ x ∂volume, ∀ j : S,
      (a j).scalar.multiplier (H := H) f x = (a j).scalar.weight x • f x :=
    ae_all_iff.mpr fun j => scalar_multiplier_ae (a j).scalar f
  have hsum : (fun x => ∑ j ∈ S,
      c j * ‖(a j).scalar.multiplier (H := H) f x‖ ^ 2) ≤ᵐ[volume]
      (fun x => W x * ‖f x‖ ^ 2) := by
    filter_upwards [hall] with x hx
    calc
      _ = (∑ j ∈ S, c j * (a j).scalar.weight x ^ 2) * ‖f x‖ ^ 2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hx ⟨j, hj⟩, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hweight x) (sq_nonneg _)
  have hh := DyadicFractional.finite_weighted_integral_bound S c
    (fun j x => ‖(a j).scalar.multiplier (H := H) f x‖ ^ 2)
    (fun x => W x * ‖f x‖ ^ 2)
    (fun j _ => (Lp.memLp ((a j).scalar.multiplier (H := H) f)).norm.integrable_sq)
    hWI hsum
  have hnorm (j : J) : ‖(a j).scalar.multiplier (H := H) f‖ ^ 2 =
      ∫ x, ‖(a j).scalar.multiplier (H := H) f x‖ ^ 2 := by
    have h := GptLean.Repair.toL2_norm_sq (Lp.memLp ((a j).scalar.multiplier (H := H) f))
    simpa only [Lp.toLp_coeFn] using h
  simpa only [← hnorm] using hh


end PfHk.PhysicalCutoffCommutator
