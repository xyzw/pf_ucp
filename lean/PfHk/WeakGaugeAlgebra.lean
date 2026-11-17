import GptLean.TransformationsGaugeWeakPair

/-! The full weak gauge class is closed under zero, addition, and inversion.
Its action on density-current pairs therefore defines genuine gauge classes. -/

noncomputable section

namespace GptLean.TransformationsGauge

open MeasureTheory PhysicalPairSpace Repair
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 600000

namespace InLpThreeAddTop

theorem zero : InLpThreeAddTop (fun _ => 0) :=
  ⟨0, 0, MemLp.zero, MemLp.zero, ae_of_all _ fun _ => by simp⟩

theorem add {f g : Position → ℝ} (hf : InLpThreeAddTop f)
    (hg : InLpThreeAddTop g) : InLpThreeAddTop (fun x => f x + g x) := by
  obtain ⟨a, b, ha, hb, he⟩ := hf
  obtain ⟨c, d, hc, hd, hf⟩ := hg
  refine ⟨a + c, b + d, ha.add hc, hb.add hd, ?_⟩
  filter_upwards [he, hf] with x hx hy
  simp only [Pi.add_apply, hx, hy]
  ring

theorem locallyIntegrable {f : Position → ℝ} (hf : InLpThreeAddTop f) :
    LocallyIntegrable f volume :=
  finite_localMemLp_two_locallyIntegrable hf.local_memLp_two

end InLpThreeAddTop

namespace WeakSpatialGauge

def zero : WeakSpatialGauge where
  fn := fun _ => 0
  locallyIntegrable := continuous_const.locallyIntegrable
  gradient := fun _ _ => 0
  gradient_in_sum := fun _ => InLpThreeAddTop.zero
  weak := by intros; simp

def add (G H : WeakSpatialGauge) : WeakSpatialGauge where
  fn := G.fn + H.fn
  locallyIntegrable := G.locallyIntegrable.add H.locallyIntegrable
  gradient := fun a x => G.gradient a x + H.gradient a x
  gradient_in_sum := fun a => (G.gradient_in_sum a).add (H.gradient_in_sum a)
  weak a φ hφ hs := by
    have hG := (G.gradient_in_sum a).locallyIntegrable
      |>.integrable_smul_left_of_hasCompactSupport hφ.continuous hs
    have hH := (H.gradient_in_sum a).locallyIntegrable
      |>.integrable_smul_left_of_hasCompactSupport hφ.continuous hs
    have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single a 1)) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hG' := G.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      hdφ (hs.fderiv_apply ℝ _)
    have hH' := H.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      hdφ (hs.fderiv_apply ℝ _)
    simp only [smul_eq_mul] at hG hH hG' hH'
    simp only [Pi.add_apply, mul_add, integral_add hG hH, integral_add hG' hH',
      G.weak a φ hφ hs, H.weak a φ hφ hs, neg_add]

@[simp] theorem zero_gradientVector (x : Position) : zero.gradientVector x = 0 := by
  ext a
  rfl

theorem add_gradientVector (G H : WeakSpatialGauge) (x : Position) :
    (G.add H).gradientVector x = G.gradientVector x + H.gradientVector x := by
  ext a
  rfl

@[simp] theorem zero_shiftPair (p : Pair) : zero.shiftPair p = p := by
  apply pair_ext_ae
  · rw [zero.densityL1_shiftPair]
  · filter_upwards [zero.currentL1_shiftPair p] with x hx
    simpa only [zero_gradientVector, smul_zero, add_zero] using hx

theorem add_shiftPair (G H : WeakSpatialGauge) (p : Pair) :
    (G.add H).shiftPair p = H.shiftPair (G.shiftPair p) := by
  apply pair_ext_ae
  · rw [densityL1_shiftPair, densityL1_shiftPair, densityL1_shiftPair]
  · filter_upwards [(G.add H).currentL1_shiftPair p,
      H.currentL1_shiftPair (G.shiftPair p), G.currentL1_shiftPair p] with x h₁ h₂ h₃
    rw [G.densityL1_shiftPair] at h₂
    rw [h₁, h₂, h₃, add_gradientVector, smul_add, add_assoc]

end WeakSpatialGauge
end GptLean.TransformationsGauge
