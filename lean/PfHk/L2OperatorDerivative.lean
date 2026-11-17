import PfHk.L2ParameterDerivative

/-! Strong L2 differentiation through a bounded fiberwise linear map.
This isolates the dominated-convergence argument from any Fock model. -/

noncomputable section
namespace PfHk.L2OperatorDerivative

open MeasureTheory Filter
open scoped ENNReal Topology
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {X K E Q : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Q]

/-- The ordinary strong derivative, with the L2 scalar instances selected
once at an abstract normed fiber. -/
abbrev HasL2DerivAt (f : ℝ → Lp E 2 μ) (g : Lp E 2 μ) (t : ℝ) : Prop :=
  HasDerivAt f g t

theorem hasDerivAt_toLp (A : X → K →L[ℝ] E) (q : Lp Q 2 μ)
    {B D : ℝ} (hB : 0 ≤ B)
    (hA : ∀ x k, ‖A x k‖ ≤ B * ‖k‖ * ‖q x‖)
    {a : ℝ → X → K} {da : X → K} {t : ℝ}
    (hf : ∀ s, MemLp (fun x => A x (a s x)) 2 μ)
    (hg : MemLp (fun x => A x (da x)) 2 μ)
    (hda : ∀ᵐ x ∂μ, ‖da x‖ ≤ D)
    (hd : ∀ᵐ x ∂μ, HasDerivAt (fun s => a s x) (da x) t)
    (hslope : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ∀ᵐ x ∂μ,
      ‖h⁻¹ • (a (t + h) x - a t x)‖ ≤ D) :
    HasDerivAt (fun s => (hf s).toLp (fun x => A x (a s x)))
      (hg.toLp (fun x => A x (da x))) t := by
  have hb : Integrable (fun x => (B * D) ^ 2 * ‖q x‖ ^ 2) μ :=
    ((Lp.memLp q).norm.integrable_sq).const_mul _
  apply L2ParameterDerivative.hasDerivAt_toLp hf hg hb
  · exact hd.mono fun x hx => (A x).hasFDerivAt.comp_hasDerivAt t hx
  · filter_upwards [hslope] with h hh
    filter_upwards [hh] with x hx
    rw [← map_sub, ← map_smul]
    have hn := (hA x (h⁻¹ • (a (t + h) x - a t x))).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx hB) (norm_nonneg _))
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (by ring)
  · filter_upwards [hda] with x hx
    have hn := (hA x (da x)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx hB) (norm_nonneg _))
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (by ring)

end PfHk.L2OperatorDerivative
