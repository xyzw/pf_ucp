import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Unimodular phase multipliers on vector-valued L².

For a measurable real function `θ`, multiplication by `exp (i θ)` is a
complex-linear isometric equivalence of `L²(X; E)` for every complex normed
space `E`. Its inverse is the phase of `-θ`. The phase commutes with every
operator that acts pointwise by complex-linear maps, in particular with
`ContinuousLinearMap.compLpL`. This is the scalar part of the gauge
transformation `gauge-unitary` in Appendix `app-transformation-properties`.
-/

noncomputable section

namespace GptLean.TransformationsPhase

open MeasureTheory
open scoped ENNReal

variable {X E F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The unimodular factor `exp (i θ(x))`. -/
def factor (θ : X → ℝ) (x : X) : ℂ := Complex.exp ((θ x : ℂ) * Complex.I)

omit [MeasurableSpace X] in
theorem norm_factor (θ : X → ℝ) (x : X) : ‖factor θ x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I (θ x)

omit [MeasurableSpace X] in
theorem factor_neg_mul (θ : X → ℝ) (x : X) : factor (-θ) x * factor θ x = 1 := by
  unfold factor
  rw [← Complex.exp_add]
  simp

omit [MeasurableSpace X] in
theorem factor_add (θ ψ : X → ℝ) (x : X) : factor (θ + ψ) x = factor θ x * factor ψ x := by
  unfold factor
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, Complex.ofReal_add]
  ring

theorem factor_aestronglyMeasurable {θ : X → ℝ} (hθ : AEStronglyMeasurable θ μ) :
    AEStronglyMeasurable (factor θ) μ := by
  have hc : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) := by fun_prop
  exact hc.comp_aestronglyMeasurable hθ

theorem neg_aestronglyMeasurable {θ : X → ℝ} (hθ : AEStronglyMeasurable θ μ) :
    AEStronglyMeasurable (-θ) μ := hθ.neg

theorem phase_memLp {θ : X → ℝ} (hθ : AEStronglyMeasurable θ μ) (u : Lp E 2 μ) :
    MemLp (fun x => factor θ x • u x) 2 μ := by
  apply (Lp.memLp u).of_le ((factor_aestronglyMeasurable hθ).smul (Lp.aestronglyMeasurable u))
  exact ae_of_all _ fun x => by
    change ‖factor θ x • u x‖ ≤ ‖u x‖
    rw [norm_smul, norm_factor, one_mul]

/-- The phase multiplier as a complex-linear map. -/
def phaseLinear {θ : X → ℝ} (hθ : AEStronglyMeasurable θ μ) : Lp E 2 μ →ₗ[ℂ] Lp E 2 μ where
  toFun u := (phase_memLp hθ u).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(phase_memLp hθ (u + v)).coeFn_toLp, (phase_memLp hθ u).coeFn_toLp,
      (phase_memLp hθ v).coeFn_toLp, Lp.coeFn_add u v,
      Lp.coeFn_add ((phase_memLp hθ u).toLp _) ((phase_memLp hθ v).toLp _)]
      with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₅, Pi.add_apply, h₂, h₃, h₄, Pi.add_apply, smul_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(phase_memLp hθ (c • u)).coeFn_toLp, (phase_memLp hθ u).coeFn_toLp,
      Lp.coeFn_smul c u, Lp.coeFn_smul c ((phase_memLp hθ u).toLp _)]
      with x h₁ h₂ h₃ h₄
    rw [h₁, RingHom.id_apply, h₄, Pi.smul_apply, h₂, h₃, Pi.smul_apply, smul_comm]

theorem phaseLinear_ae {θ : X → ℝ} (hθ : AEStronglyMeasurable θ μ) (u : Lp E 2 μ) :
    phaseLinear hθ u =ᵐ[μ] fun x => factor θ x • u x :=
  (phase_memLp hθ u).coeFn_toLp

theorem phaseLinear_neg_phaseLinear {θ : X → ℝ} (hθ : AEStronglyMeasurable θ μ)
    (u : Lp E 2 μ) : phaseLinear (neg_aestronglyMeasurable hθ) (phaseLinear hθ u) = u := by
  apply Lp.ext
  filter_upwards [phaseLinear_ae (neg_aestronglyMeasurable hθ) (phaseLinear hθ u),
    phaseLinear_ae hθ u] with x h₁ h₂
  rw [h₁, h₂, smul_smul, factor_neg_mul, one_smul]

theorem norm_phaseLinear_le {θ : X → ℝ} (hθ : AEStronglyMeasurable θ μ) (u : Lp E 2 μ) :
    ‖phaseLinear hθ u‖ ≤ ‖u‖ := by
  have h := Lp.norm_le_mul_norm_of_ae_le_mul (c := 1) (f := phaseLinear hθ u) (g := u)
    (by
      filter_upwards [phaseLinear_ae hθ u] with x hx
      rw [hx, norm_smul, norm_factor])
  simpa only [one_mul] using h

theorem norm_phaseLinear {θ : X → ℝ} (hθ : AEStronglyMeasurable θ μ) (u : Lp E 2 μ) :
    ‖phaseLinear hθ u‖ = ‖u‖ := by
  apply le_antisymm (norm_phaseLinear_le hθ u)
  calc ‖u‖ = ‖phaseLinear (neg_aestronglyMeasurable hθ) (phaseLinear hθ u)‖ := by
        rw [phaseLinear_neg_phaseLinear]
    _ ≤ ‖phaseLinear hθ u‖ := norm_phaseLinear_le _ _

/-- Multiplication by `exp (i θ)` as a linear isometric equivalence. -/
def phase {θ : X → ℝ} (hθ : AEStronglyMeasurable θ μ) : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 μ where
  toLinearMap := phaseLinear hθ
  invFun := phaseLinear (neg_aestronglyMeasurable hθ)
  left_inv u := phaseLinear_neg_phaseLinear hθ u
  right_inv u := by
    have h := phaseLinear_neg_phaseLinear (neg_aestronglyMeasurable hθ) u
    simp only [neg_neg] at h
    exact h
  norm_map' u := norm_phaseLinear hθ u

theorem phase_ae {θ : X → ℝ} (hθ : AEStronglyMeasurable θ μ) (u : Lp E 2 μ) :
    phase hθ u =ᵐ[μ] fun x => factor θ x • u x :=
  phaseLinear_ae hθ u

theorem phase_symm_apply {θ : X → ℝ} (hθ : AEStronglyMeasurable θ μ) (u : Lp E 2 μ) :
    (phase hθ).symm u = phase (neg_aestronglyMeasurable hθ) u := rfl

/-- The phase commutes with every operator acting pointwise by complex-linear maps. -/
theorem phase_commute_pointwise {θ : X → ℝ} (hθ : AEStronglyMeasurable θ μ)
    (T : Lp E 2 μ → Lp F 2 μ) (A : X → E →L[ℂ] F)
    (hT : ∀ u, T u =ᵐ[μ] fun x => A x (u x)) (u : Lp E 2 μ) :
    T (phase hθ u) = phase hθ (T u) := by
  apply Lp.ext
  filter_upwards [hT (phase hθ u), phase_ae hθ u, phase_ae hθ (T u), hT u]
    with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, map_smul]

theorem compLpL_phase {θ : X → ℝ} (hθ : AEStronglyMeasurable θ μ) (L : E →L[ℂ] F)
    (u : Lp E 2 μ) : L.compLpL 2 μ (phase hθ u) = phase hθ (L.compLpL 2 μ u) :=
  phase_commute_pointwise hθ (L.compLpL 2 μ) (fun _ => L) (fun v => L.coeFn_compLpL v) u

/-- Phases compose by adding their angles. -/
theorem phase_phase {θ ψ : X → ℝ} (hθ : AEStronglyMeasurable θ μ)
    (hψ : AEStronglyMeasurable ψ μ) (u : Lp E 2 μ) :
    phase hθ (phase hψ u) = phase (hθ.add hψ) u := by
  apply Lp.ext
  filter_upwards [phase_ae hθ (phase hψ u), phase_ae hψ u, phase_ae (hθ.add hψ) u]
    with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, smul_smul, factor_add]

/-- Two angles that agree almost everywhere give the same phase. -/
theorem phase_congr {θ ψ : X → ℝ} (hθ : AEStronglyMeasurable θ μ)
    (hψ : AEStronglyMeasurable ψ μ) (h : θ =ᵐ[μ] ψ) (u : Lp E 2 μ) :
    phase hθ u = phase hψ u := by
  apply Lp.ext
  filter_upwards [phase_ae hθ u, phase_ae hψ u, h] with x h₁ h₂ hx
  rw [h₁, h₂, factor, factor, hx]

end GptLean.TransformationsPhase
