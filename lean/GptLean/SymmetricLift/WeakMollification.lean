import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Differentiating mollifications of a weakly differentiable field.
The weak derivative premise is the usual integration-by-parts identity
against all smooth compactly supported scalar tests. The reflected,
translated smoothing kernel is such a test, so the smooth derivative of
the mollification is the mollification of the weak derivative. -/

noncomputable section

namespace GptLean.SymmetricLift

open MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Scalar smoothing, written with the smooth kernel on the right so its
classical derivative can be computed directly. -/
def smoothMollify (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (f : EuclideanSpace ℝ (Fin d) → E) : EuclideanSpace ℝ (Fin d) → E :=
  f ⋆[(lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip, volume] κ

theorem smoothMollify_apply (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (f : EuclideanSpace ℝ (Fin d) → E) (x : EuclideanSpace ℝ (Fin d)) :
    smoothMollify κ f x = ∫ y, κ (x - y) • f y := rfl

/-- The distributional directional derivative, stated as actual test
integrals. Local integrability is required separately where it is used. -/
def WeakDirectionalIdentity (f g : EuclideanSpace ℝ (Fin d) → E)
    (v : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, φ x • g x) = -(∫ x, (fderiv ℝ φ x v) • f x)

theorem smoothMollify_contDiff {κ : EuclideanSpace ℝ (Fin d) → ℝ}
    {f : EuclideanSpace ℝ (Fin d) → E}
    (hκ : ContDiff ℝ ∞ κ) (hκs : HasCompactSupport κ)
    (hf : LocallyIntegrable f volume) : ContDiff ℝ ∞ (smoothMollify κ f) := by
  exact hκs.contDiff_convolution_right _ hf hκ

/-- Mollification turns the weak directional identity into the classical
directional derivative, with the weak derivative smoothed by the same kernel. -/
theorem smoothMollify_hasLineDerivAt
    {κ : EuclideanSpace ℝ (Fin d) → ℝ} {f g : EuclideanSpace ℝ (Fin d) → E}
    (hκ : ContDiff ℝ ∞ κ) (hκs : HasCompactSupport κ)
    (hf : LocallyIntegrable f volume) {v : EuclideanSpace ℝ (Fin d)}
    (hweak : WeakDirectionalIdentity f g v) (x : EuclideanSpace ℝ (Fin d)) :
    HasLineDerivAt ℝ (smoothMollify κ f) (smoothMollify κ g x) x v := by
  let φ : EuclideanSpace ℝ (Fin d) → ℝ := fun y => κ (x - y)
  have hφ : ContDiff ℝ ∞ φ := hκ.comp (contDiff_const.sub contDiff_id)
  have hφs : HasCompactSupport φ := hκs.comp_homeomorph (Homeomorph.subLeft x)
  have hφd : ∀ y, fderiv ℝ φ y v = -(fderiv ℝ κ (x - y) v) := by
    intro y
    have h := ((hκ.differentiable (by simp)) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    change HasFDerivAt φ _ y at h
    rw [h.fderiv]
    simp
  have hw := hweak φ hφ hφs
  simp_rw [hφd, neg_smul, integral_neg, neg_neg] at hw
  let L : E →L[ℝ] ℝ →L[ℝ] E := (lsmul ℝ ℝ).flip
  have hκ1 : ContDiff ℝ 1 κ := hκ.of_le (by simp)
  have hd := (hκs.hasFDerivAt_convolution_right L hf hκ1 x).hasLineDerivAt v
  rw [convolution_precompR_apply L hf (hκs.fderiv ℝ)
    (hκ1.continuous_fderiv one_ne_zero) x v] at hd
  have he : (f ⋆[L, volume] (fun y => fderiv ℝ κ y v)) x = smoothMollify κ g x := by
    exact hw.symm
  rw [he] at hd
  exact hd

end GptLean.SymmetricLift
