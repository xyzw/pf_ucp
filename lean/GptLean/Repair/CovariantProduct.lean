import GptLean.SymmetricLift.FullH1TensorLift
import GptLean.Repair.IntegratedChannel
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
Weak product rules for scalar repair multipliers. The weak derivative is
derived from compact smooth test functions. In particular the product rule
is not supplied as an extra identity for the repaired vector.

The smooth real multiplier case allows arbitrary weak H1 local fibre
fields. In the reverse direction, a weak H1 complex multiplier can act on
any smooth fibre field. This applies to the constructed nonsmooth lift on
a smooth source core. The coordinate channel's covariant derivative is
identified with the resulting distributional derivative. Extension to a
general physical form-domain source still requires the weighted core
approximation and unbounded-field domain arguments.
-/

noncomputable section

namespace GptLean.Repair

open MeasureTheory GptLean.SymmetricLift
open scoped ENNReal ContDiff

variable {I E F : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [DecidableEq I] in
private theorem continuous_memLp_top_restrict
    {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {k : EuclideanSpace ℝ I → 𝕜} (hk : Continuous k)
    {K : Set (EuclideanSpace ℝ I)} (hK : IsCompact K) :
    MemLp k ∞ (volume.restrict K) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hk.continuousOn
  apply memLp_top_of_bound hk.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC x hx

omit [DecidableEq I] [CompleteSpace E] in
private theorem local_test_integrable
    {f : EuclideanSpace ℝ I → E}
    (hf : ∀ K, IsCompact K → MemLp f 2 (volume.restrict K))
    {φ : EuclideanSpace ℝ I → ℝ} (hφ : Continuous φ)
    (hs : HasCompactSupport φ) : Integrable (fun x => φ x • f x) := by
  exact integrable_smul_of_memLp_on_support
    ((hφ.memLp_of_hasCompactSupport hs).restrict (tsupport φ))
    (hf _ hs) (fun x hx => image_eq_zero_of_notMem_tsupport hx)

/-- Bounded linear maps transport both the local L2 data and the actual
distributional identity. -/
theorem weakH1Local_map (L : E →L[ℝ] F)
    {f : EuclideanSpace ℝ I → E} {df : I → EuclideanSpace ℝ I → E}
    (hf : HasWeakH1Local f df) :
    HasWeakH1Local (fun x => L (f x)) (fun i x => L (df i x)) := by
  refine ⟨fun K hK => L.comp_memLp' (hf.function_memLp K hK),
    fun i K hK => L.comp_memLp' (hf.derivative_memLp i K hK), ?_⟩
  intro i φ hφ hs
  have hd : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have h := congrArg L (hf.weak i φ hφ hs)
  rw [← L.integral_comp_comm (local_test_integrable (hf.derivative_memLp i)
      hφ.continuous hs), map_neg,
    ← L.integral_comp_comm (local_test_integrable hf.function_memLp hd
      (hs.fderiv_apply ℝ _))] at h
  simpa only [map_smul] using h

omit [CompleteSpace E] in
/-- Addition preserves the compact-test formulation of weak H1. -/
theorem weakH1Local_add
    {f g : EuclideanSpace ℝ I → E} {df dg : I → EuclideanSpace ℝ I → E}
    (hf : HasWeakH1Local f df) (hg : HasWeakH1Local g dg) :
    HasWeakH1Local (fun x => f x + g x) (fun i x => df i x + dg i x) := by
  refine ⟨fun K hK => (hf.function_memLp K hK).add (hg.function_memLp K hK),
    fun i K hK => (hf.derivative_memLp i K hK).add (hg.derivative_memLp i K hK), ?_⟩
  intro i φ hφ hs
  have hd : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  simp only [smul_add]
  rw [integral_add (local_test_integrable (hf.derivative_memLp i) hφ.continuous hs)
      (local_test_integrable (hg.derivative_memLp i) hφ.continuous hs),
    integral_add (local_test_integrable hf.function_memLp hd (hs.fderiv_apply ℝ _))
      (local_test_integrable hg.function_memLp hd (hs.fderiv_apply ℝ _)),
    hf.weak i φ hφ hs, hg.weak i φ hφ hs, neg_add]

omit [CompleteSpace E] in
/-- The real scalar product rule follows by using `φ * k` as a test
function in the original weak identity. No global bound on `k` is needed. -/
theorem weakH1Local_smooth_real_smul
    {f : EuclideanSpace ℝ I → E} {df : I → EuclideanSpace ℝ I → E}
    (hf : HasWeakH1Local f df) {k : EuclideanSpace ℝ I → ℝ}
    (hk : ContDiff ℝ ∞ k) :
    HasWeakH1Local (fun x => k x • f x)
      (fun i x => k x • df i x +
        fderiv ℝ k x (EuclideanSpace.single i 1) • f x) := by
  have hdk (i : I) : Continuous (fun x => fderiv ℝ k x (EuclideanSpace.single i 1)) :=
    (hk.continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    exact (hf.function_memLp K hK).smul (continuous_memLp_top_restrict hk.continuous hK)
  · intro i K hK
    exact ((hf.derivative_memLp i K hK).smul
      (continuous_memLp_top_restrict hk.continuous hK)).add
      ((hf.function_memLp K hK).smul (continuous_memLp_top_restrict (hdk i) hK))
  · intro i φ hφ hs
    let v := EuclideanSpace.single i (1 : ℝ)
    have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have ha := local_test_integrable (hf.derivative_memLp i)
      (hφ.continuous.mul hk.continuous) (hs.mul_right (f' := k))
    have hb := local_test_integrable hf.function_memLp
      (hφ.continuous.mul (hdk i))
      (hs.mul_right (f' := fun x => fderiv ℝ k x v))
    have hc := local_test_integrable hf.function_memLp
      (hdφ.mul hk.continuous) ((hs.fderiv_apply ℝ v).mul_right (f' := k))
    change Integrable (fun x => (φ x * k x) • df i x) at ha
    change Integrable (fun x => (φ x * fderiv ℝ k x v) • f x) at hb
    change Integrable (fun x => (fderiv ℝ φ x v * k x) • f x) at hc
    have hprod (x) : fderiv ℝ (fun y => φ y * k y) x v =
        φ x * fderiv ℝ k x v + fderiv ℝ φ x v * k x := by
      rw [fderiv_fun_mul (hφ.differentiable (by simp) x) (hk.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    have hw := hf.weak i (fun x => φ x * k x) (hφ.mul hk) hs.mul_right
    change (∫ x, (φ x * k x) • df i x) =
      -(∫ x, fderiv ℝ (fun y => φ y * k y) x v • f x) at hw
    simp_rw [hprod, add_smul] at hw
    rw [integral_add hb hc] at hw
    simp only [smul_add, smul_smul]
    rw [integral_add ha hb]
    change (∫ x, (φ x * k x) • df i x) +
      (∫ x, (φ x * fderiv ℝ k x v) • f x) =
      -(∫ x, (fderiv ℝ φ x v * k x) • f x)
    rw [hw]
    abel

/-- A weak real scalar multiplier times a smooth fibre field has the
expected weak derivative. Duality reduces the vector test identity to
the scalar product rule above. This direction applies to nonsmooth lift
coordinates on a smooth source core. -/
theorem weakH1Local_real_smul_smooth
    {k : EuclideanSpace ℝ I → ℝ} {dk : I → EuclideanSpace ℝ I → ℝ}
    (hk : HasWeakH1Local k dk) {f : EuclideanSpace ℝ I → E}
    (hf : ContDiff ℝ ∞ f) :
    HasWeakH1Local (fun x => k x • f x)
      (fun i x => dk i x • f x +
        k x • fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  have hdf (i : I) : Continuous (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfun K (hK : IsCompact K) : MemLp (fun x => k x • f x) 2 (volume.restrict K) :=
    (continuous_memLp_top_restrict hf.continuous hK).smul (hk.function_memLp K hK)
  have hder i K (hK : IsCompact K) : MemLp
      (fun x => dk i x • f x + k x • fderiv ℝ f x (EuclideanSpace.single i 1))
      2 (volume.restrict K) :=
    ((continuous_memLp_top_restrict hf.continuous hK).smul (hk.derivative_memLp i K hK)).add
      ((continuous_memLp_top_restrict (hdf i) hK).smul (hk.function_memLp K hK))
  refine ⟨hfun, hder, ?_⟩
  intro i φ hφ hs
  have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  have hLf : ContDiff ℝ ∞ (fun x => L (f x)) := L.contDiff.comp hf
  have hdLf (x) : fderiv ℝ (fun y => L (f y)) x (EuclideanSpace.single i 1) =
      L (fderiv ℝ f x (EuclideanSpace.single i 1)) := by
    change fderiv ℝ (L ∘ f) x (EuclideanSpace.single i 1) = _
    rw [(L.hasFDerivAt.comp x (hf.differentiable (by simp) x).hasFDerivAt).fderiv]
    rfl
  have hw := (weakH1Local_smooth_real_smul hk hLf).weak i φ hφ hs
  rw [← L.integral_comp_comm (local_test_integrable (hder i) hφ.continuous hs),
    map_neg, ← L.integral_comp_comm (local_test_integrable hfun hdφ (hs.fderiv_apply ℝ _))]
  simpa only [hdLf, map_smul, map_add, smul_eq_mul, mul_comm] using hw

section Complex

variable {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace H] in
private theorem complex_smul_decomposition (c : ℂ) (u : H) :
    c.re • u + Complex.I • (c.im • u) = c • u := by
  calc
    c.re • u + Complex.I • (c.im • u) =
        ((c.re : ℂ) + Complex.I * (c.im : ℂ)) • u := by
      rw [add_smul, Complex.coe_smul]
      congr 1
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      rfl
    _ = c • u := by
      congr 1
      simpa only [mul_comm] using c.re_add_im

/-- The complex scalar version includes nonsmooth weak H1 multipliers.
Real and imaginary projection are bounded real linear maps, so both scalar
weak identities are inherited rather than postulated. -/
theorem weakH1Local_complex_smul_smooth
    {k : EuclideanSpace ℝ I → ℂ} {dk : I → EuclideanSpace ℝ I → ℂ}
    (hk : HasWeakH1Local k dk) {f : EuclideanSpace ℝ I → H}
    (hf : ContDiff ℝ ∞ f) :
    HasWeakH1Local (fun x => k x • f x)
      (fun i x => dk i x • f x +
        k x • fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  let L : H →L[ℝ] H := (Complex.I • ContinuousLinearMap.id ℂ H).restrictScalars ℝ
  have hr := weakH1Local_real_smul_smooth (weakH1Local_map Complex.reCLM hk) hf
  have hi := weakH1Local_map L
    (weakH1Local_real_smul_smooth (weakH1Local_map Complex.imCLM hk) hf)
  apply (weakH1Local_add hr hi).congr
  · exact Filter.Eventually.of_forall fun x => by
      change (k x).re • f x + Complex.I • ((k x).im • f x) = k x • f x
      exact complex_smul_decomposition _ _
  · intro i
    apply Filter.Eventually.of_forall
    intro x
    change (dk i x).re • f x + (k x).re • fderiv ℝ f x (EuclideanSpace.single i 1) +
      Complex.I • ((dk i x).im • f x +
        (k x).im • fderiv ℝ f x (EuclideanSpace.single i 1)) = _
    rw [smul_add]
    calc
      _ = ((dk i x).re • f x + Complex.I • ((dk i x).im • f x)) +
          ((k x).re • fderiv ℝ f x (EuclideanSpace.single i 1) +
            Complex.I • ((k x).im • fderiv ℝ f x (EuclideanSpace.single i 1))) := by abel
      _ = _ := by rw [complex_smul_decomposition, complex_smul_decomposition]

/-- For an actual weak H1 lift, every coordinate product with a smooth
source has a proved local weak derivative, including across the collision
set. The index type can be finite or infinite. -/
theorem coordinate_smul_hasWeakH1Local_of_smooth_source
    {ι : Type*} (b : HilbertBasis ι ℂ V)
    {z : EuclideanSpace ℝ I → V} {dz : I → EuclideanSpace ℝ I → V}
    (hz : HasWeakH1Local z dz) {ψ : EuclideanSpace ℝ I → H}
    (hψ : ContDiff ℝ ∞ ψ) (a : ι) :
    HasWeakH1Local (fun x => coordinate b (z x) a • ψ x)
      (fun i x => coordinate b (dz i x) a • ψ x +
        coordinate b (z x) a • fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
  exact weakH1Local_complex_smul_smooth
    (weakH1Local_map ((innerSL ℂ (b a)).restrictScalars ℝ) hz) hψ

/-- The natural-number indexed version uses the exact vector family of the
integrated trace-class channel. -/
theorem channelValue_hasWeakH1Local_of_smooth_source
    (b : HilbertBasis ℕ ℂ V)
    {z : EuclideanSpace ℝ I → V} {dz : I → EuclideanSpace ℝ I → V}
    (hz : HasWeakH1Local z dz) {ψ : EuclideanSpace ℝ I → H}
    (hψ : ContDiff ℝ ∞ ψ) (a : ℕ) :
    HasWeakH1Local (channelValue b z ψ a)
      (fun i x => coordinate b (dz i x) a • ψ x +
        coordinate b (z x) a • fderiv ℝ ψ x (EuclideanSpace.single i 1)) :=
  coordinate_smul_hasWeakH1Local_of_smooth_source b hz hψ a

/-- Compact support of the smooth source upgrades the local weak product
to globally square-integrable values and derivatives. Thus the actual
coordinate product has global H1 data. -/
theorem coordinate_smul_memLp_of_smooth_compact_source
    {ι : Type*} (b : HilbertBasis ι ℂ V)
    {z : EuclideanSpace ℝ I → V} {dz : I → EuclideanSpace ℝ I → V}
    (hz : HasWeakH1Local z dz) {ψ : EuclideanSpace ℝ I → H}
    (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ) (a : ι) :
    MemLp (fun x => coordinate b (z x) a • ψ x) 2 volume ∧
      ∀ i, MemLp (fun x => coordinate b (dz i x) a • ψ x +
        coordinate b (z x) a • fderiv ℝ ψ x (EuclideanSpace.single i 1)) 2 volume := by
  have h := coordinate_smul_hasWeakH1Local_of_smooth_source b hz hψ a
  have hglobal {f : EuclideanSpace ℝ I → H}
      (hf : MemLp f 2 (volume.restrict (tsupport ψ)))
      (hzero : ∀ x, x ∉ tsupport ψ → f x = 0) : MemLp f 2 volume := by
    have he : (tsupport ψ).indicator f = f := by
      funext x
      by_cases hx : x ∈ tsupport ψ
      · simp only [Set.indicator_of_mem hx]
      · simp only [Set.indicator_of_notMem hx, hzero x hx]
    rw [← he]
    exact (memLp_indicator_iff_restrict hs.measurableSet).mpr hf
  refine ⟨hglobal (h.function_memLp _ hs) ?_, fun i => hglobal (h.derivative_memLp i _ hs) ?_⟩
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, fderiv_of_notMem_tsupport ℝ hx]
    simp

/-- The covariant-coordinate identity has no countability assumption on
the basis. The fibre potential is complex-linear, and its physical domain
interpretation is kept separate. -/
theorem coordinate_covariant_derivative_smooth_source
    {ι : Type*} (b : HilbertBasis ι ℂ V)
    {z : EuclideanSpace ℝ I → V} {dz : I → EuclideanSpace ℝ I → V}
    (hz : HasWeakH1Local z dz) {ψ : EuclideanSpace ℝ I → H}
    (hψ : ContDiff ℝ ∞ ψ) (A : I → EuclideanSpace ℝ I → H →ₗ[ℂ] H) (a : ι) :
    ∃ dψa : I → EuclideanSpace ℝ I → H,
      HasWeakH1Local (fun x => coordinate b (z x) a • ψ x) dψa ∧
      ∀ i x, -Complex.I • dψa i x - A i x (coordinate b (z x) a • ψ x) =
        coordinate b (z x) a •
          (-Complex.I • fderiv ℝ ψ x (EuclideanSpace.single i 1) - A i x (ψ x)) -
          Complex.I • coordinate b (dz i x) a • ψ x := by
  refine ⟨_, coordinate_smul_hasWeakH1Local_of_smooth_source b hz hψ a, ?_⟩
  intro i x
  simp only [smul_add, smul_sub, map_smul, neg_smul, smul_smul]
  module

/-- The derivative used by the integrated channel is exactly the covariant
derivative of the weak product on a smooth source core. -/
theorem channel_covariant_derivative_smooth_source
    (b : HilbertBasis ℕ ℂ V)
    {z : EuclideanSpace ℝ I → V} {dz : I → EuclideanSpace ℝ I → V}
    (hz : HasWeakH1Local z dz) {ψ : EuclideanSpace ℝ I → H}
    (hψ : ContDiff ℝ ∞ ψ) (A : I → EuclideanSpace ℝ I → H →ₗ[ℂ] H) (a : ℕ) :
    ∃ dψa : I → EuclideanSpace ℝ I → H,
      HasWeakH1Local (channelValue b z ψ a) dψa ∧
      ∀ i x, -Complex.I • dψa i x - A i x (channelValue b z ψ a x) =
        channelDerivative b z (dz i)
          (fun y => -Complex.I • fderiv ℝ ψ y (EuclideanSpace.single i 1) - A i y (ψ y))
          ψ a x :=
  coordinate_covariant_derivative_smooth_source b hz hψ A a

end Complex

end GptLean.Repair
