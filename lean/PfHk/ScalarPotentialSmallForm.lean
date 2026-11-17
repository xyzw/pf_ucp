import PfHk.ScalarCoordinateFormBound

/-! Infinitesimal scalar form bounds from actual L^(3/2)+L-infinity
one-body coefficients. The bounded/small split is constructed by simple
function approximation. No physical multiplier estimate is assumed. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.ScalarPotentialSmallForm

open MeasureTheory GptLean GptLean.PhysicalPairDuality
open GptLean.PhysicalSourceCoordinates PfHk.CoordinateSobolev
open PfHk.ScalarCoordinateFormBound PfHk.PhysicalLocalEnergy
open scoped ENNReal

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

variable {N : ℕ}

private theorem split_multiplier (n : Fin N) (v b c : Position → ℝ)
    (hb : MemLp b ∞ volume) (hc : MemLp c (3 / 2) volume)
    (hv : v =ᵐ[volume] fun x => b x + c x)
    (f : Configuration N → ℝ) (g : (Fin N × Fin 3) → Configuration N → ℝ)
    (hw : SymmetricLift.HasWeakH1Local f g) (hf : MemLp f 2 volume)
    (hg : ∀ i, MemLp (g i) 2 volume) :
    Integrable (fun x => |coordinateCoefficient n v x| * f x ^ 2) volume ∧
    (∫ x, |coordinateCoefficient n v x| * f x ^ 2) ≤
      (eLpNorm b ∞ volume).toReal * (∫ x, f x ^ 2) +
      OrdinaryCoordinateH1Multiplier.constant ℂ n * (eLpNorm c (3 / 2) volume).toReal *
        ((∫ x, f x ^ 2) + ∑ i, ∫ x, g i x ^ 2) := by
  obtain ⟨hib, hbb⟩ := bounded_multiplier n b hb f hf
  obtain ⟨hic, hcb⟩ := critical_multiplier n c hc f g hw hf hg
  have hvmeas := (hb.aestronglyMeasurable.add hc.aestronglyMeasurable).congr hv.symm
  have hle : ∀ᵐ x ∂volume, |coordinateCoefficient n v x| * f x ^ 2 ≤
      |coordinateCoefficient n b x| * f x ^ 2 + |coordinateCoefficient n c x| * f x ^ 2 := by
    filter_upwards [coordinate_ae n hv] with x hx
    change v (split n x).1 = b (split n x).1 + c (split n x).1 at hx
    change |v (split n x).1| * f x ^ 2 ≤ _
    rw [hx]
    exact (mul_le_mul_of_nonneg_right (abs_add_le _ _) (sq_nonneg _)).trans_eq (add_mul _ _ _)
  have hi : Integrable (fun x => |coordinateCoefficient n v x| * f x ^ 2) volume :=
    (hib.add hic).mono'
      ((coordinateCoefficient_measurable n hvmeas).norm.mul (hf.aestronglyMeasurable.pow 2))
      (hle.mono fun x hx => (Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))).le.trans hx)
  refine ⟨hi, (integral_mono_ae hi (hib.add hic) hle).trans ?_⟩
  exact (integral_add hib hic).le.trans (add_le_add hbb hcb)

/-- Arbitrary measurable amplitudes dominated by the one-body absolute
potential sum have arbitrarily small kinetic form bound. -/
theorem negative_bound_of_scalarPotential
    (v : Fin N → Position → ℝ)
    (hv : ∀ n, ∃ p : ScalarPotential, v n =ᵐ[volume] (p.val : Position → ℝ))
    (w : Configuration N → ℝ) (hw : AEStronglyMeasurable w volume)
    (hdom : ∀ᵐ x ∂volume, w x ^ 2 ≤ ∑ n, |coordinateCoefficient n (v n) x|)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ScalarMultiplierBound w ε C := by
  classical
  let K : ℝ := ∑ n : Fin N, OrdinaryCoordinateH1Multiplier.constant ℂ n
  have hK : 0 ≤ K := Finset.sum_nonneg fun n _ =>
    OrdinaryCoordinateH1Multiplier.constant_nonneg n
  let δ : ℝ := ε / (K + 1)
  have hδ : 0 < δ := div_pos hε (by linarith only [hK])
  have hsplit : ∀ n : Fin N, ∃ b c : Position → ℝ,
      MemLp b ∞ volume ∧ MemLp c (3 / 2) volume ∧
      v n =ᵐ[volume] (fun x => b x + c x) ∧ (eLpNorm c (3 / 2) volume).toReal < δ := by
    intro n
    obtain ⟨p, hp⟩ := hv n
    obtain ⟨b, c, hb, hc, he, hn⟩ := ScalarLpDecomposition.small_parts p
      (ENNReal.div_ne_top (by norm_num) (by norm_num)) hδ
    exact ⟨b, c, hb, hc, hp.trans he, hn⟩
  choose b c hb hc he hn using hsplit
  let B : ℝ := ∑ n : Fin N, (eLpNorm (b n) ∞ volume).toReal
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  refine ⟨B + ε, add_nonneg hB hε.le, ?_⟩
  intro f g hfg hf hg
  let M : ℝ := ∫ x, f x ^ 2
  let G : ℝ := ∑ i, ∫ x, g i x ^ 2
  have hM : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
  have hG : 0 ≤ G := Finset.sum_nonneg fun i _ => integral_nonneg fun _ => sq_nonneg _
  have hparts := fun n => split_multiplier n (v n) (b n) (c n) (hb n) (hc n) (he n)
    f g hfg hf hg
  have hi : Integrable (fun x => ∑ n, |coordinateCoefficient n (v n) x| * f x ^ 2) volume :=
    integrable_finsetSum _ fun n _ => (hparts n).1
  have hle : ∀ᵐ x ∂volume, w x ^ 2 * f x ^ 2 ≤
      ∑ n, |coordinateCoefficient n (v n) x| * f x ^ 2 :=
    hdom.mono fun x hx => (mul_le_mul_of_nonneg_right hx (sq_nonneg _)).trans_eq
      (Finset.sum_mul _ _ _)
  have hiw : Integrable (fun x => w x ^ 2 * f x ^ 2) volume :=
    hi.mono' ((hw.pow 2).mul (hf.aestronglyMeasurable.pow 2))
      (hle.mono fun x hx => (Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))).le.trans hx)
  have hsum : (∫ x, ∑ n, |coordinateCoefficient n (v n) x| * f x ^ 2) ≤
      B * M + K * δ * (M + G) := by
    rw [integral_finsetSum _ fun n _ => (hparts n).1]
    have hterm : ∀ n : Fin N, (∫ x, |coordinateCoefficient n (v n) x| * f x ^ 2) ≤
        (eLpNorm (b n) ∞ volume).toReal * M +
        OrdinaryCoordinateH1Multiplier.constant ℂ n * δ * (M + G) := by
      intro n
      exact (hparts n).2.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hn n).le (OrdinaryCoordinateH1Multiplier.constant_nonneg (H := ℂ) n))
          (add_nonneg hM hG)))
    exact (Finset.sum_le_sum fun n _ => hterm n).trans_eq (by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, B, K])
  have hKδ : K * δ ≤ ε := by
    have heq : (K + 1) * δ = ε := mul_div_cancel₀ ε (by linarith only [hK] : K + 1 ≠ 0)
    exact (mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1) hδ.le).trans_eq heq
  have hfinal : B * M + K * δ * (M + G) ≤ ε * G + (B + ε) * M := by
    calc
      B * M + K * δ * (M + G) ≤ B * M + ε * (M + G) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hKδ (add_nonneg hM hG))
      _ = ε * G + (B + ε) * M := by ring
  exact (integral_mono_ae hiw hi hle).trans (hsum.trans hfinal)

end PfHk.ScalarPotentialSmallForm

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
