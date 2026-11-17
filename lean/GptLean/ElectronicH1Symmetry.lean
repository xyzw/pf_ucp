import GptLean.ElectronicH1Reindex
import GptLean.ElectronicH1Complex
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Integration by parts on the actual Hilbert-valued electronic H1 graph. -/

noncomputable section

namespace GptLean.ElectronicH1Symmetry

open MeasureTheory ElectronicH1Space ElectronicH1Reindex
open scoped ENNReal ContDiff InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def innerBilinear : H →L[ℝ] H →L[ℝ] ℂ :=
  (LinearMap.mk₂ ℝ (inner ℂ)
    (fun u v w => inner_add_left u v w)
    (fun c u v => inner_smul_left_eq_smul u v c)
    (fun u v w => inner_add_right u v w)
    (fun c u v => inner_smul_right_eq_smul u v c)).mkContinuous₂ 1
    (fun u v => by
      change ‖⟪u, v⟫_ℂ‖ ≤ 1 * ‖u‖ * ‖v‖
      simpa only [one_mul] using norm_inner_le_norm u v)

omit [CompleteSpace H] in
theorem integrable_inner_of_memLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => ⟪f x, g x⟫_ℂ) μ := by
  apply (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [CompleteSpace H] in
theorem smooth_integration_by_parts
    (f g : EuclideanSpace ℝ I → H) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) (i : I) :
    (∫ x, ⟪f x, fderiv ℝ g x (EuclideanSpace.single i 1)⟫_ℂ) =
      -(∫ x, ⟪fderiv ℝ f x (EuclideanSpace.single i 1), g x⟫_ℂ) := by
  apply integral_bilinear_fderiv_right_eq_neg_left_of_integrable (B := innerBilinear)
  · exact integrable_inner_of_memLp
      (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hsf.fderiv_apply ℝ _))
      (hg.continuous.memLp_of_hasCompactSupport hsg)
  · exact integrable_inner_of_memLp
      (hf.continuous.memLp_of_hasCompactSupport hsf)
      (((hg.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hsg.fderiv_apply ℝ _))
  · exact integrable_inner_of_memLp (hf.continuous.memLp_of_hasCompactSupport hsf)
      (hg.continuous.memLp_of_hasCompactSupport hsg)
  · intro x _
    exact hf.differentiable (by simp) x
  · intro x _
    exact hg.differentiable (by simp) x

theorem smoothCore_integration_by_parts (u v : H1 H I)
    (hu : u ∈ genericSmoothCore H I) (hv : v ∈ genericSmoothCore H I) (i : I) :
    ⟪value u, derivative i v⟫_ℂ = -⟪derivative i u, value v⟫_ℂ := by
  obtain ⟨f, hf, hs, rfl⟩ := hu
  obtain ⟨g, hg, ht, rfl⟩ := hv
  rw [L2.inner_def, L2.inner_def]
  have hf₀ := (hf.continuous.memLp_of_hasCompactSupport hs (p := (2 : ℝ≥0∞)) (μ := volume)).coeFn_toLp
  have hf₁ := (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hs.fderiv_apply ℝ (EuclideanSpace.single i 1)) (p := (2 : ℝ≥0∞)) (μ := volume)).coeFn_toLp
  have hg₀ := (hg.continuous.memLp_of_hasCompactSupport ht (p := (2 : ℝ≥0∞)) (μ := volume)).coeFn_toLp
  have hg₁ := (((hg.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (ht.fderiv_apply ℝ (EuclideanSpace.single i 1)) (p := (2 : ℝ≥0∞)) (μ := volume)).coeFn_toLp
  have hleft : (∫ x, ⟪value (ofSmoothCompact f hf hs) x,
      derivative i (ofSmoothCompact g hg ht) x⟫_ℂ) =
      ∫ x, ⟪f x, fderiv ℝ g x (EuclideanSpace.single i 1)⟫_ℂ := by
    apply integral_congr_ae
    filter_upwards [hf₀, hg₁] with x hx hy
    exact congrArg₂ (fun a b : H => ⟪a, b⟫_ℂ) hx hy
  have hright : (∫ x, ⟪derivative i (ofSmoothCompact f hf hs) x,
      value (ofSmoothCompact g hg ht) x⟫_ℂ) =
      ∫ x, ⟪fderiv ℝ f x (EuclideanSpace.single i 1), g x⟫_ℂ := by
    apply integral_congr_ae
    filter_upwards [hf₁, hg₀] with x hx hy
    exact congrArg₂ (fun a b : H => ⟪a, b⟫_ℂ) hx hy
  exact hleft.trans ((smooth_integration_by_parts f g hf hg hs ht i).trans
    (congrArg Neg.neg hright).symm)

omit [CompleteSpace H] in
private theorem integration_by_parts_of_dense {Q : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (val der : Q →L[ℝ] H) (core : Set Q) (hd : Dense core)
    (hcore : ∀ u ∈ core, ∀ v ∈ core, ⟪val u, der v⟫_ℂ = -⟪der u, val v⟫_ℂ)
    (u v : Q) : ⟪val u, der v⟫_ℂ = -⟪der u, val v⟫_ℂ := by
  have hc : IsClosed {p : Q × Q | ⟪val p.1, der p.2⟫_ℂ = -⟪der p.1, val p.2⟫_ℂ} :=
    isClosed_eq ((val.continuous.comp continuous_fst).inner
      (der.continuous.comp continuous_snd))
      (((der.continuous.comp continuous_fst).inner (val.continuous.comp continuous_snd)).neg)
  exact (closure_minimal (fun p hp => hcore p.1 hp.1 p.2 hp.2) hc) ((hd.prod hd) (u, v))

theorem integration_by_parts (u v : H1 H I) (i : I) :
    ⟪value u, derivative i v⟫_ℂ = -⟪derivative i u, value v⟫_ℂ := by
  apply integration_by_parts_of_dense (H := L2 H I) (Q := H1 H I)
    (value (E := H) (I := I)) (derivative (E := H) i) (genericSmoothCore H I)
  · exact dense_genericSmoothCore
  intro u hu v hv
  exact smoothCore_integration_by_parts u v hu hv i

end GptLean.ElectronicH1Symmetry
