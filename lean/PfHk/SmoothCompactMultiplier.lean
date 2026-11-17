import PfHk.SmoothCutoffBounds

/-! Ordinary compact smooth scalar functions define actual multipliers
with bounded first and second derivatives. -/

noncomputable section
namespace PfHk.SmoothCutoffBounds

open GptLean GptLean.ElectronicH1Multiplier PfHk.PhysicalCutoffCommutator
open Filter
open scoped Topology

set_option Elab.async false
set_option maxHeartbeats 60000

variable {I : Type} [Fintype I] [DecidableEq I]

theorem exists_twice_compact (f : EuclideanSpace ℝ I → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    ∃ a : TwiceDifferentiableMultiplier I, a.scalar.weight = f := by
  obtain ⟨B₀, hB₀⟩ := hf.continuous.bounded_above_of_compact_support hs
  obtain ⟨B₁, B₂, _, _, hbounds⟩ := standardSmoothRescaling I f hf hs
  have hid : scaled f 0 1 = f := by funext x; simp [scaled]
  obtain ⟨hfirst, hsecond⟩ := hbounds 0 1 zero_lt_one
  simp only [hid, div_one, one_pow] at hfirst hsecond
  have hfirstsmooth (i : I) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative f i) :=
    (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const
  let a : DifferentiableMultiplier I := {
    weight := f
    differentiable := hf.differentiable (by simp)
    bound := B₀
    bounded := fun x => by simpa only [Real.norm_eq_abs] using hB₀ x
    derivativeBound := B₁
    derivative_bounded := hfirst }
  let da : I → DifferentiableMultiplier I := fun i => {
    weight := coordinateDerivative f i
    differentiable := (hfirstsmooth i).differentiable (by simp)
    bound := B₁
    bounded := hfirst i
    derivativeBound := B₂
    derivative_bounded := hsecond i }
  exact ⟨⟨a, da, fun _ => rfl⟩, rfl⟩

def compactMultiplier (f : EuclideanSpace ℝ I → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    TwiceDifferentiableMultiplier I := Classical.choose (exists_twice_compact f hf hs)

theorem compactMultiplier_weight (f : EuclideanSpace ℝ I → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    (compactMultiplier f hf hs).scalar.weight = f :=
  Classical.choose_spec (exists_twice_compact f hf hs)

theorem compactMultiplier_gradient (f : EuclideanSpace ℝ I → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (i : I) (x : EuclideanSpace ℝ I) :
    (compactMultiplier f hf hs).scalar.gradient i x = coordinateDerivative f i x := by
  unfold DifferentiableMultiplier.gradient coordinateDerivative
  rw [compactMultiplier_weight]

theorem compactMultiplier_second (f : EuclideanSpace ℝ I → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (i j : I)
    (x : EuclideanSpace ℝ I) :
    ((compactMultiplier f hf hs).derivative i).gradient j x =
      coordinateDerivative (coordinateDerivative f i) j x := by
  unfold DifferentiableMultiplier.gradient coordinateDerivative
  rw [(compactMultiplier f hf hs).derivative_weight]
  unfold DifferentiableMultiplier.gradient
  rw [compactMultiplier_weight]

theorem smooth_product_off_point (η g : EuclideanSpace ℝ I → ℝ) (O : EuclideanSpace ℝ I)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hg : ∀ x, x ≠ O → ContDiffAt ℝ (⊤ : ℕ∞) g x)
    (hzero : η =ᶠ[𝓝 O] fun _ => 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => η x * g x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = O
  · subst x
    apply (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : EuclideanSpace ℝ I => (0 : ℝ)) O).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    rw [hy, zero_mul]
  · exact hη.contDiffAt.mul (hg x hx)

theorem coordinateDerivative_mul_at (f g : EuclideanSpace ℝ I → ℝ) (i : I)
    {x : EuclideanSpace ℝ I} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    coordinateDerivative (fun y => f y * g y) i x =
      f x * coordinateDerivative g i x + g x * coordinateDerivative f i x := by
  unfold coordinateDerivative
  rw [fderiv_fun_mul hf hg]
  rfl

theorem coordinateDerivative_differentiableAt (f : EuclideanSpace ℝ I → ℝ) (i : I)
    {x : EuclideanSpace ℝ I} (hf : ContDiffAt ℝ (2 : ℕ∞) f x) :
    DifferentiableAt ℝ (coordinateDerivative f i) x := by
  exact ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
    (by norm_num)

theorem coordinateDerivative_second_mul (f g : EuclideanSpace ℝ I → ℝ) (i j : I)
    {x : EuclideanSpace ℝ I} (hf : ContDiffAt ℝ (2 : ℕ∞) f x)
    (hg : ContDiffAt ℝ (2 : ℕ∞) g x) :
    coordinateDerivative (coordinateDerivative (fun y => f y * g y) i) j x =
      f x * coordinateDerivative (coordinateDerivative g i) j x +
      coordinateDerivative f j x * coordinateDerivative g i x +
      g x * coordinateDerivative (coordinateDerivative f i) j x +
      coordinateDerivative g j x * coordinateDerivative f i x := by
  have heq : coordinateDerivative (fun y => f y * g y) i =ᶠ[𝓝 x]
      fun y => f y * coordinateDerivative g i y + g y * coordinateDerivative f i y := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hfy hgy
    exact coordinateDerivative_mul_at f g i (hfy.differentiableAt (by norm_num))
      (hgy.differentiableAt (by norm_num))
  have hfd := hf.differentiableAt (by norm_num)
  have hgd := hg.differentiableAt (by norm_num)
  have hfdi := coordinateDerivative_differentiableAt f i hf
  have hgdi := coordinateDerivative_differentiableAt g i hg
  have hd := (hfd.hasFDerivAt.mul hgdi.hasFDerivAt).add
    (hgd.hasFDerivAt.mul hfdi.hasFDerivAt)
  change HasFDerivAt (fun y => f y * coordinateDerivative g i y +
    g y * coordinateDerivative f i y) _ x at hd
  change (fderiv ℝ (coordinateDerivative (fun y => f y * g y) i) x)
    (EuclideanSpace.single j 1) = _
  rw [heq.fderiv_eq, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    coordinateDerivative]
  ring

end PfHk.SmoothCutoffBounds
