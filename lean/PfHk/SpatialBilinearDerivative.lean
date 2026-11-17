import PfHk.L2OperatorDerivative
import PfHk.StrongOperatorDerivative
import GptLean.PhysicalFockSpatialField

/-! Strong differentiation of bounded, spatially varying bilinear maps
on L2. The parameter and the L2 argument may both move. -/

noncomputable section
namespace PfHk.SpatialBilinearDerivative

open MeasureTheory Filter GptLean.PhysicalFock
open scoped ENNReal Topology
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {X K Q H : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  (B : K →L[ℂ] Q →L[ℂ] H)

def operator (a : X → K) (ha : AEStronglyMeasurable a μ)
    (M : ℝ) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ M) : Lp Q 2 μ →L[ℂ] Lp H 2 μ :=
  spatialOperator μ (fun x => B (a x)) (B.continuous.comp_aestronglyMeasurable ha)
    (‖B‖ * M) (hb.mono fun x hx =>
      (B.le_opNorm (a x)).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg B)))

theorem operator_ae (a : X → K) (ha : AEStronglyMeasurable a μ)
    (M : ℝ) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ M) (q : Lp Q 2 μ) :
    operator μ B a ha M hb q =ᵐ[μ] fun x => B (a x) (q x) :=
  spatialOperator_ae _ _ _ _ _ _

theorem operator_norm_le (a : X → K) (ha : AEStronglyMeasurable a μ)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ M) :
    ‖operator μ B a ha M hb‖ ≤ ‖B‖ * M := by
  apply ContinuousLinearMap.opNorm_le_bound (operator μ B a ha M hb)
    (mul_nonneg (norm_nonneg B) hM)
  intro q
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [operator_ae μ B a ha M hb q, hb] with x hx hk
  rw [hx]
  exact ((B (a x)).le_opNorm (q x)).trans
    (mul_le_mul_of_nonneg_right ((B.le_opNorm (a x)).trans
      (mul_le_mul_of_nonneg_left hk (norm_nonneg _))) (norm_nonneg _))

theorem operator_hasDerivAt
    (a : ℝ → X → K) (ha : ∀ s, AEStronglyMeasurable (a s) μ)
    (M : ℝ → ℝ) (hb : ∀ s, ∀ᵐ x ∂μ, ‖a s x‖ ≤ M s)
    (da : X → K) (hda : AEStronglyMeasurable da μ)
    (D : ℝ) (hdaBound : ∀ᵐ x ∂μ, ‖da x‖ ≤ D)
    (q : Lp Q 2 μ) (t : ℝ)
    (hd : ∀ᵐ x ∂μ, HasDerivAt (fun s => a s x) (da x) t)
    (hslope : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ∀ᵐ x ∂μ,
      ‖h⁻¹ • (a (t + h) x - a t x)‖ ≤ D) :
    L2OperatorDerivative.HasL2DerivAt
      (fun s => operator μ B (a s) (ha s) (M s) (hb s) q)
      (operator μ B da hda D hdaBound q) t := by
  let f : ℝ → X → H := fun s x => B (a s x) (q x)
  let g : X → H := fun x => B (da x) (q x)
  have hf (s : ℝ) : MemLp (f s) 2 μ :=
    (Lp.memLp (operator μ B (a s) (ha s) (M s) (hb s) q)).ae_eq
      (operator_ae μ B (a s) (ha s) (M s) (hb s) q)
  have hg : MemLp g 2 μ :=
    (Lp.memLp (operator μ B da hda D hdaBound q)).ae_eq
      (operator_ae μ B da hda D hdaBound q)
  have h := L2OperatorDerivative.hasDerivAt_toLp
    (fun x => (B.flip (q x)).restrictScalars ℝ) q (norm_nonneg B)
    (fun x k => ((B k).le_opNorm (q x)).trans
      (mul_le_mul_of_nonneg_right (B.le_opNorm k) (norm_nonneg _)))
    hf hg hdaBound hd hslope
  have heq (s : ℝ) : operator μ B (a s) (ha s) (M s) (hb s) q = (hf s).toLp (f s) := by
    apply Lp.ext
    exact (operator_ae μ B (a s) (ha s) (M s) (hb s) q).trans (hf s).coeFn_toLp.symm
  have hdeq : operator μ B da hda D hdaBound q = hg.toLp g := by
    apply Lp.ext
    exact (operator_ae μ B da hda D hdaBound q).trans hg.coeFn_toLp.symm
  simp only [heq, hdeq]
  convert! h using 1

end PfHk.SpatialBilinearDerivative
