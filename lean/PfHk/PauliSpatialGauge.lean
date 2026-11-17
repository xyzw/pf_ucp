import PfHk.WeakGaugeAlgebra
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Bounded-gradient differentiable gauges belong to the article's weak
gauge class. Their data action agrees with the existing smooth-gauge action. -/

noncomputable section
namespace PfHk.PauliWeakGauge

open MeasureTheory GptLean GptLean.TransformationsGauge GptLean.PhysicalPairSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

theorem spatialGradient_in_sum (g : SpatialGauge) (a : Fin 3) :
    InLpThreeAddTop (g.gradient a) := by
  refine ⟨0, g.gradient a, MemLp.zero, ?_, ?_⟩
  · exact memLp_top_of_bound (g.gradient_measurable a).aestronglyMeasurable
      g.derivativeBound (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs] using g.abs_gradient_le a x)
  · exact ae_of_all _ fun x => (zero_add (g.gradient a x)).symm

def ofSpatial (g : SpatialGauge) : WeakSpatialGauge where
  fn := g.fn
  locallyIntegrable := g.differentiable.continuous.locallyIntegrable
  gradient := g.gradient
  gradient_in_sum := spatialGradient_in_sum g
  weak a φ hφ hs := by
    have hcont : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single a 1)) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hlocal : LocallyIntegrable g.fn volume := g.differentiable.continuous.locallyIntegrable
    have h₁ : Integrable (fun x => fderiv ℝ φ x (EuclideanSpace.single a 1) • g.fn x) volume :=
      hlocal.integrable_smul_left_of_hasCompactSupport hcont (hs.fderiv_apply ℝ _)
    have h₂ : Integrable (fun x => φ x • g.gradient a x) volume :=
      (spatialGradient_in_sum g a).locallyIntegrable.integrable_smul_left_of_hasCompactSupport
        hφ.continuous hs
    have h₃ : Integrable (fun x => φ x • g.fn x) volume :=
      hlocal.integrable_smul_left_of_hasCompactSupport hφ.continuous hs
    exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable h₁ h₂ h₃
      (fun x _ => hφ.differentiable (by simp) x) (fun x _ => g.differentiable x)

theorem ofSpatial_gradient (g : SpatialGauge) (a : Fin 3) (x : Position) :
    (ofSpatial g).gradient a x = g.gradient a x := rfl

theorem ofSpatial_gradientVector (g : SpatialGauge) (x : Position) :
    (ofSpatial g).gradientVector x = g.gradientVector x := rfl

theorem ofSpatial_shiftPair (g : SpatialGauge) (d : Pair) :
    (ofSpatial g).shiftPair d = g.shiftPair d := by
  apply pair_ext_ae
  · rw [WeakSpatialGauge.densityL1_shiftPair, SpatialGauge.densityL1_shiftPair]
  · exact ((ofSpatial g).currentL1_shiftPair d).trans (g.currentL1_shiftPair d).symm

theorem ofSpatial_energyShift (g : SpatialGauge) (d : Pair) :
    (ofSpatial g).energyShift d = g.energyShift d := rfl

end PfHk.PauliWeakGauge
