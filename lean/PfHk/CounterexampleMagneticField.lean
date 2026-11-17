import PfHk.CounterexampleField
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import PfHk.FriedrichsDivergenceBackground
import GptLean.TransformationsGaugePair

/-! The explicit magnetic field of the counterexample is nonzero everywhere.
Distinct parameters therefore have distinct magnetic fields as measurable
classes. The distributional gauge obstruction is derived from commutation
of mixed derivatives of compactly supported smooth tests. -/

noncomputable section
namespace PfHk.CounterexampleMagneticField

open MeasureTheory Filter PfHk.CounterexampleField
open scoped ContDiff

set_option Elab.async false
set_option maxHeartbeats 400000

theorem contDiff_field : ContDiff ℝ ∞ field := by
  have hd : ContDiff ℝ ∞ denominator := contDiff_const.add (contDiff_norm_sq ℝ)
  exact (hd.inv (fun x => (denominator_pos x).ne')).smul rotation.contDiff

theorem contDiff_vectorPotential (t : ℝ) : ContDiff ℝ ∞ (vectorPotential t) :=
  contDiff_field.const_smul t

theorem curl_field (x : Space) :
    curl field x = (2 / (1 + ‖x‖ ^ 2) ^ 2) •
      WithLp.toLp 2 ![x 0 * x 2, x 1 * x 2, 1 + (x 2) ^ 2] := by
  have hd := (denominator_pos x).ne'
  apply PiLp.ext
  intro j
  fin_cases j
  all_goals
    simp [curl, (hasFDerivAt_field x).fderiv, ContinuousLinearMap.smulRight_apply,
      EuclideanSpace.inner_single_right, denominator, rotation, rotationLinear,
      EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ] at hd ⊢
    field_simp
    <;> ring

theorem curl_field_third_pos (x : Space) : 0 < curl field x 2 := by
  rw [curl_field]
  change 0 < 2 / (1 + ‖x‖ ^ 2) ^ 2 * (1 + (x 2) ^ 2)
  positivity

theorem curl_field_ne_zero (x : Space) : curl field x ≠ 0 := by
  intro h
  have hz := congrArg (fun y : Space => y 2) h
  exact (ne_of_gt (curl_field_third_pos x)) hz

theorem curl_vectorPotential (t : ℝ) (x : Space) :
    curl (vectorPotential t) x = t • curl field x := by
  have hd : fderiv ℝ (vectorPotential t) x = t • fderiv ℝ field x :=
    ((differentiable_field x).hasFDerivAt.const_smul t).fderiv
  apply PiLp.ext
  intro j
  fin_cases j <;> simp [curl, hd, mul_sub]

theorem distinct_curls_at {s t : ℝ} (hst : s ≠ t) (x : Space) :
    curl (vectorPotential s) x ≠ curl (vectorPotential t) x := by
  rw [curl_vectorPotential, curl_vectorPotential]
  intro h
  have hz : (s - t) • curl field x = 0 := by rw [sub_smul, h, sub_self]
  exact hst (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (curl_field_ne_zero x)))

theorem distinct_curls_ae {s t : ℝ} (hst : s ≠ t) :
    ∀ᵐ x ∂volume, curl (vectorPotential s) x ≠ curl (vectorPotential t) x :=
  ae_of_all _ (distinct_curls_at hst)

theorem not_ae_eq_curls {s t : ℝ} (hst : s ≠ t) :
    ¬ (curl (vectorPotential s) =ᵐ[volume] curl (vectorPotential t)) := by
  intro h
  obtain ⟨x, hx⟩ := h.exists
  exact distinct_curls_at hst x hx

private def coordinateDerivative (f : Space → ℝ) (j : Fin 3) (x : Space) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single j 1)

private theorem partial_contDiff {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (coordinateDerivative f j) :=
  (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

private theorem integral_partial_mul {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (j : Fin 3) :
    (∫ x, coordinateDerivative f j x * φ x) = -(∫ x, f x * coordinateDerivative φ j x) := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure Space))
    (((partial_contDiff hf j).continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      hs.mul_left)
    ((hf.continuous.mul (partial_contDiff hφ j).continuous).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ (EuclideanSpace.single j 1)).mul_left)
    ((hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hs.mul_left)
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => hφ.differentiable (by simp) x)
  change (∫ x, f x * coordinateDerivative φ j x) = -(∫ x, coordinateDerivative f j x * φ x) at h
  linarith

/-- The classical divergence of the smooth field is also its distributional
divergence. This gives the local regularity used in the HK hypotheses. -/
theorem weakDivergence_vectorPotential (t : ℝ) :
    FriedrichsDivergenceBackground.WeakDivergence
      (fun j x => vectorPotential t x j) (fun _ => 0) := by
  intro φ hφ hs
  have hcoord (j : Fin 3) : ContDiff ℝ ∞ (fun x => vectorPotential t x j) :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp (contDiff_vectorPotential t)
  have hpart (j : Fin 3) (x : Space) :
      coordinateDerivative (fun y => vectorPotential t y j) j x =
        fderiv ℝ (vectorPotential t) x (EuclideanSpace.single j 1) j := by
    exact congrArg (fun L : Space →L[ℝ] ℝ => L (EuclideanSpace.single j 1))
      ((((EuclideanSpace.proj j : Space →L[ℝ] ℝ)).hasFDerivAt.comp x
        ((contDiff_vectorPotential t).differentiable (by simp) x).hasFDerivAt).fderiv)
  have hd (x : Space) : ∑ j : Fin 3, coordinateDerivative (fun y => vectorPotential t y j) j x = 0 := by
    have hdt : fderiv ℝ (vectorPotential t) x = t • fderiv ℝ field x :=
      ((differentiable_field x).hasFDerivAt.const_smul t).fderiv
    simp_rw [hpart, hdt]
    change ∑ j : Fin 3, t * fderiv ℝ field x (EuclideanSpace.single j 1) j = 0
    rw [← Finset.mul_sum]
    change t * divergence field x = 0
    rw [divergence_field, mul_zero]
  have hi (j : Fin 3) : Integrable
      (fun x => coordinateDerivative (fun y => vectorPotential t y j) j x * φ x) volume :=
    (((partial_contDiff (hcoord j) j).continuous).mul hφ.continuous).integrable_of_hasCompactSupport
      hs.mul_left
  have he : (∑ j : Fin 3, ∫ x, vectorPotential t x j * coordinateDerivative φ j x) = 0 := by
    have hh (j : Fin 3) := integral_partial_mul (hcoord j) hφ hs j
    have hj (j : Fin 3) : (∫ x, vectorPotential t x j * coordinateDerivative φ j x) =
        -(∫ x, coordinateDerivative (fun y => vectorPotential t y j) j x * φ x) := by linarith [hh j]
    simp_rw [hj]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum]
    · simp_rw [← Finset.sum_mul, hd, zero_mul]
      simp
    · exact fun j _ => hi j
  change (∫ x, (0 : ℝ) * φ x) =
    -(∑ j : Fin 3, ∫ x, vectorPotential t x j * coordinateDerivative φ j x)
  rw [he]
  simp

/-- A distributional gradient. This allows arbitrary locally integrable
gauge functions, rather than imposing classical second derivatives. -/
def IsDistributionalGradient (A : Space → Space) : Prop :=
  ∃ θ : Space → ℝ, LocallyIntegrable θ volume ∧
    ∀ (j : Fin 3) (φ : Space → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, A x j * φ x) = -(∫ x, θ x * coordinateDerivative φ j x)

theorem IsDistributionalGradient.congr {A A' : Space → Space}
    (h : IsDistributionalGradient A) (he : A =ᵐ[volume] A') :
    IsDistributionalGradient A' := by
  rcases h with ⟨θ, hθ, h⟩
  refine ⟨θ, hθ, fun j φ hφ hs => ?_⟩
  calc
    (∫ x, A' x j * φ x) = ∫ x, A x j * φ x := integral_congr_ae
      (he.mono fun x hx => congrArg (fun v : Space => v j * φ x) hx.symm)
    _ = _ := h j φ hφ hs

/-- Every gauge in the existing physical model is a distributional gauge,
even though its derivative is only required to be bounded and measurable. -/
theorem spatialGauge_isDistributionalGradient (g : GptLean.TransformationsGauge.SpatialGauge) :
    IsDistributionalGradient g.gradientVector := by
  refine ⟨g.fn, g.differentiable.continuous.locallyIntegrable, ?_⟩
  intro j φ hφ hs
  have hφi : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hs
  have hi : Integrable (fun x => fderiv ℝ g.fn x (EuclideanSpace.single j 1) * φ x) volume :=
    hφi.bdd_mul (g.gradient_measurable j).aestronglyMeasurable
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs, GptLean.TransformationsGauge.SpatialGauge.gradient]
          using g.abs_gradient_le j x)
  have hj : Integrable (fun x => g.fn x * coordinateDerivative φ j x) volume :=
    (g.differentiable.continuous.mul (partial_contDiff hφ j).continuous).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ (EuclideanSpace.single j 1)).mul_left
  have hk : Integrable (fun x => g.fn x * φ x) volume :=
    (g.differentiable.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hs.mul_left
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi hj hk
    (fun x _ => g.differentiable x) (fun x _ => hφ.differentiable (by simp) x)
  change (∫ x, g.fn x * coordinateDerivative φ j x) =
    -(∫ x, fderiv ℝ g.fn x (EuclideanSpace.single j 1) * φ x) at he
  change (∫ x, fderiv ℝ g.fn x (EuclideanSpace.single j 1) * φ x) =
    -(∫ x, g.fn x * coordinateDerivative φ j x)
  linarith

private theorem mixed_partials {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (i j : Fin 3) (x : Space) : coordinateDerivative (coordinateDerivative φ i) j x = coordinateDerivative (coordinateDerivative φ j) i x := by
  have hdf := (contDiff_infty_iff_fderiv.mp hφ).2
  unfold coordinateDerivative
  rw [fderiv_clm_apply (hdf.differentiable (by simp) x) (differentiableAt_const _),
    fderiv_clm_apply (hdf.differentiable (by simp) x) (differentiableAt_const _)]
  simpa using hφ.contDiffAt.isSymmSndFDerivAt (by simp)
    (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)

theorem curl_zero_of_distributional_gradient (A : Space → Space)
    (hA : ContDiff ℝ ∞ A) (hg : IsDistributionalGradient A) :
    curl A =ᵐ[volume] 0 := by
  rcases hg with ⟨θ, _, hg⟩
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun x => A x j) :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp hA
  have hp (i j : Fin 3) : coordinateDerivative (fun x => A x i) j =ᵐ[volume]
      coordinateDerivative (fun x => A x j) i := by
    apply ae_eq_of_integral_contDiff_smul_eq
      (partial_contDiff (hc i) j).continuous.locallyIntegrable
      (partial_contDiff (hc j) i).continuous.locallyIntegrable
    intro φ hφ hs
    have hi := integral_partial_mul (hc i) hφ hs j
    have hj := integral_partial_mul (hc j) hφ hs i
    have hgi := hg i (coordinateDerivative φ j) (partial_contDiff hφ j) (hs.fderiv_apply ℝ _)
    have hgj := hg j (coordinateDerivative φ i) (partial_contDiff hφ i) (hs.fderiv_apply ℝ _)
    have he : (∫ x, θ x * coordinateDerivative (coordinateDerivative φ j) i x) =
        (∫ x, θ x * coordinateDerivative (coordinateDerivative φ i) j x) := by
      simp_rw [mixed_partials hφ j i]
    simp only [smul_eq_mul]
    simp_rw [mul_comm (φ _) (coordinateDerivative _ _ _)]
    linarith
  have hp' (i j : Fin 3) : (fun x => fderiv ℝ A x (EuclideanSpace.single j 1) i) =ᵐ[volume]
      (fun x => fderiv ℝ A x (EuclideanSpace.single i 1) j) := by
    have hd (a b : Fin 3) (x : Space) : coordinateDerivative (fun y => A y a) b x =
        fderiv ℝ A x (EuclideanSpace.single b 1) a :=
      congrArg (fun L : Space →L[ℝ] ℝ => L (EuclideanSpace.single b 1))
        ((((EuclideanSpace.proj a : Space →L[ℝ] ℝ)).hasFDerivAt.comp x
          (hA.differentiable (by simp) x).hasFDerivAt).fderiv)
    filter_upwards [hp i j] with x hx
    simpa only [hd] using hx
  filter_upwards [hp' 2 1, hp' 0 2, hp' 1 0] with x h0 h1 h2
  ext j
  fin_cases j <;> simp [curl, h0, h1, h2]

/-- Distinct counterexample vector potentials cannot differ by a
distributional gradient, including all ordinary Sobolev gauge functions. -/
theorem not_distributional_gauge_equivalent {s t : ℝ} (hst : s ≠ t) :
    ¬ IsDistributionalGradient (fun x => vectorPotential t x - vectorPotential s x) := by
  intro hg
  have he : (fun x => vectorPotential t x - vectorPotential s x) = vectorPotential (t - s) := by
    funext x
    simp [vectorPotential, sub_smul]
  rw [he] at hg
  have hz := curl_zero_of_distributional_gradient _ (contDiff_vectorPotential (t - s)) hg
  obtain ⟨x, hx⟩ := hz.exists
  rw [curl_vectorPotential] at hx
  exact hst ((sub_eq_zero.mp ((smul_eq_zero.mp hx).resolve_right (curl_field_ne_zero x))).symm)

theorem not_spatialGauge_equivalent {s t : ℝ} (hst : s ≠ t)
    (g : GptLean.TransformationsGauge.SpatialGauge) :
    ¬ ((fun x => vectorPotential t x - vectorPotential s x) =ᵐ[volume] g.gradientVector) := by
  intro he
  exact not_distributional_gauge_equivalent hst
    ((spatialGauge_isDistributionalGradient g).congr he.symm)

end PfHk.CounterexampleMagneticField
