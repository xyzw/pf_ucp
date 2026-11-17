import PfHk.SphereRestrictionCalculus
import Mathlib.Tactic.Module

/-! Ordinary coordinate algebra for the weak logarithmic-polar chart. -/
noncomputable section
namespace PfHk.PolarCalculus

variable {I H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem fderiv_sum_coordinates (u : Position I → H) (X θ : Position I) :
    (∑ j, θ j • fderiv ℝ u X (EuclideanSpace.single j 1)) = fderiv ℝ u X θ := by
  have he : (∑ j, θ j • EuclideanSpace.single j 1) = θ := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun I ℝ).sum_repr θ
  exact (by rw [map_sum]; simp only [map_smul] :
    (∑ j, θ j • fderiv ℝ u X (EuclideanSpace.single j 1)) =
      fderiv ℝ u X (∑ j, θ j • EuclideanSpace.single j 1)).trans (congrArg (fderiv ℝ u X) he)

theorem scaled_gradient_coordinates (P : StandardPolarCalculus I H)
    (u : Position I → H) (hu : ContDiff ℝ (1 : ℕ∞) u) (a : ℝ) {r : ℝ} (hr : 0 < r)
    (j : I) (θ : UnitSphere I) :
    (a*r) • (fderiv ℝ u (r • θ.val) (EuclideanSpace.single j 1) -
      θ.val j • fderiv ℝ u (r • θ.val) θ.val) =
      a • sphereGradient (radialRestriction u r) j θ := by
  rw [sphereGradient_radial_eq P u hu hr]
  simp only [radialFirst, smul_sub, smul_smul]
  congr 1
  congr 1
  ring

private theorem real_radial_chart_cancellation {V : Type*} [AddCommGroup V] [Module ℝ V]
    (a c r : ℝ) (v R : V) :
    a • ((-c) • v - r • R) + c • (a • v) = (-(a*r)) • R := by
  simp only [smul_sub, smul_smul, mul_neg, neg_smul, smul_neg]
  rw [mul_comm c a]
  abel

theorem radial_chart_cancellation {V : Type*} [AddCommGroup V]
    [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
    (a c r : ℝ) (v R : V) :
    a • ((-c) • v - r • R) + (c : ℂ) • (a • v) = (-(a*r)) • R := by
  have hc : (c : ℂ) • (a • v) = c • (a • v) :=
    IsScalarTower.algebraMap_smul ℂ c (a • v)
  rw [hc]
  exact real_radial_chart_cancellation a c r v R

end PfHk.PolarCalculus
