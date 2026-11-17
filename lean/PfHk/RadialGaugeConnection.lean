import PfHk.RadialGaugeCurvature
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Differentiation of the actual radial Weyl label and identification
of the resulting connection with the curvature integral. -/

noncomputable section
namespace PfHk.RadialGauge

open MeasureTheory Filter Set GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian PfHk.PhysicalFieldRegularity
open scoped ENNReal InnerProductSpace Interval Topology

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section Calculus
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A jointly continuous derivative can be integrated over a fixed compact
interval. The local dominating constant is derived from compactness. -/
theorem continuous_interval_hasDerivAt (f df : ℝ → ℝ → H)
    (hf : Continuous (Function.uncurry f)) (hdf : Continuous (Function.uncurry df))
    (hd : ∀ t s, HasDerivAt (fun t => f t s) (df t s) t) (a b t : ℝ) :
    HasDerivAt (fun t => ∫ s in a..b, f t s) (∫ s in a..b, df t s) t := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall t 1).prod isCompact_uIcc).exists_bound_of_continuousOn
    hdf.continuousOn
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := f) (F' := df) (bound := fun _ => B) (Metric.ball_mem_nhds t zero_lt_one)
    (Eventually.of_forall (fun t => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    ((hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b)
    (hdf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (ae_of_all _ (fun s hs u hu => hB (u, s)
      ⟨Metric.ball_subset_closedBall hu, uIoc_subset_uIcc hs⟩))
    intervalIntegrable_const (ae_of_all _ (fun s _ u _ => hd u s))).2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translating the base point turns line derivatives into derivatives
of the entire affine line. -/
theorem lineCurve_hasDerivAt (f : E → H) (df : E → E → H)
    (hd : ∀ X v, HasLineDerivAt ℝ f (df v X) X v) (X v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (X + s • v)) (df v (X + t • v)) t := by
  have h0 := hd (X + t • v) v
  unfold HasLineDerivAt at h0
  have h1 : HasDerivAt (fun u : ℝ => f ((X + t • v) + u • v))
      (df v (X + t • v)) (t - t) := by simpa only [sub_self] using h0
  have h := h1.comp_sub_const t t
  convert! h using 1
  · funext s
    congr 1
    module

end Calculus

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)

theorem couplingDerivative_real_smul (j : Fin N × Fin 3) (v X : Configuration N) (c : ℝ) :
    couplingDerivative F χ hUV e j (c • v) X = c • couplingDerivative F χ hUV e j v X := by
  change (-e) • directionKernel F χ hUV j.2 (c • particle v j.1) (particle X j.1) = _
  rw [directionKernel_real_smul, smul_comm]
  rfl

theorem couplingCurve_hasDerivAt (j : Fin N × Fin 3) (X v : Configuration N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => couplingKernel F χ e j (X + s • v))
      (couplingDerivative F χ hUV e j v (X + t • v)) t :=
  lineCurve_hasDerivAt _ _ (fun X v => couplingKernel_hasLineDerivAt F χ hUV e j v X) X v t

/-- The derivative of the integrand of `h_(X+tv)` in direction `v`. -/
def labelIntegrandDerivative (X v : Configuration N) (t s : ℝ) : WeightedPhotonKernel :=
  (∑ j : Fin N × Fin 3, v j • couplingKernel F χ e j (s • (X + t • v))) +
    ∑ j : Fin N × Fin 3, (s * (X + t • v) j) •
      couplingDerivative F χ hUV e j v (s • (X + t • v))

theorem labelIntegrand_continuous (X v : Configuration N) :
    Continuous (fun p : ℝ × ℝ => rayIntegrand F χ e (X + p.1 • v) p.2) := by
  unfold rayIntegrand
  apply continuous_finsetSum
  intro j _
  exact ((PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ) j).comp
    (continuous_const.add (continuous_fst.smul continuous_const))).smul
    ((couplingKernel_continuous F χ e j).comp
      (continuous_snd.smul (continuous_const.add (continuous_fst.smul continuous_const))))

theorem labelIntegrandDerivative_continuous (X v : Configuration N) :
    Continuous (Function.uncurry (labelIntegrandDerivative F χ hUV e X v)) := by
  unfold labelIntegrandDerivative Function.uncurry
  apply Continuous.add
  · apply continuous_finsetSum
    intro j _
    exact (continuous_const : Continuous (fun _ : ℝ × ℝ => v j)).smul
      ((couplingKernel_continuous F χ e j).comp
        (continuous_snd.smul (continuous_const.add (continuous_fst.smul continuous_const))))
  · apply continuous_finsetSum
    intro j _
    exact (continuous_snd.mul ((PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ) j).comp
      (continuous_const.add (continuous_fst.smul continuous_const)))).smul
      ((couplingDerivative_continuous F χ hUV e j v).comp
        (continuous_snd.smul (continuous_const.add (continuous_fst.smul continuous_const))))

theorem labelIntegrand_hasDerivAt (X v : Configuration N) (t s : ℝ) :
    HasDerivAt (fun t => rayIntegrand F χ e (X + t • v) s)
      (labelIntegrandDerivative F χ hUV e X v t s) t := by
  have h (j : Fin N × Fin 3) :
      HasDerivAt (fun t => couplingKernel F χ e j (s • (X + t • v)))
        (s • couplingDerivative F χ hUV e j v (s • (X + t • v))) t := by
    convert! couplingCurve_hasDerivAt F χ hUV e j (s • X) (s • v) t using 1
    · funext u
      congr 1
      module
    · rw [couplingDerivative_real_smul]
      congr 2
      module
  have hc (j : Fin N × Fin 3) : HasDerivAt (fun t : ℝ => (X + t • v) j) (v j) t := by
    convert! ((hasDerivAt_id t).mul_const (v j)).const_add (X j) using 1
    simp only [one_mul]
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hc j).smul (h j))
  convert! hh using 1
  simp only [labelIntegrandDerivative, Finset.sum_add_distrib, smul_smul, mul_comm s]
  abel

/-- The spatial derivative of the Bochner radial label is proved. -/
theorem label_hasLineDerivAt (X v : Configuration N) :
    HasLineDerivAt ℝ (label F χ e)
      (∫ s in (0 : ℝ)..1, labelIntegrandDerivative F χ hUV e X v 0 s) X v := by
  exact continuous_interval_hasDerivAt (fun t s => rayIntegrand F χ e (X + t • v) s)
    (labelIntegrandDerivative F χ hUV e X v) (labelIntegrand_continuous F χ e X v)
    (labelIntegrandDerivative_continuous F χ hUV e X v)
    (labelIntegrand_hasDerivAt F χ hUV e X v) 0 1 0



/-- The one-form `Σ v_j g_j(X)`. -/
def contraction (X v : Configuration N) : WeightedPhotonKernel :=
  ∑ j : Fin N × Fin 3, v j • couplingKernel F χ e j X

def radialConnection (X v : Configuration N) : WeightedPhotonKernel :=
  ∫ s in (0 : ℝ)..1, s • curvature F χ hUV e (s • X) X v

def labelDerivative (X v : Configuration N) : WeightedPhotonKernel :=
  ∫ s in (0 : ℝ)..1, labelIntegrandDerivative F χ hUV e X v 0 s

theorem contraction_continuous (v : Configuration N) :
    Continuous (fun X => contraction F χ e X v) := by
  apply continuous_finsetSum
  intro j _
  exact (continuous_const : Continuous (fun _ : Configuration N => v j)).smul
    (couplingKernel_continuous F χ e j)

theorem radial_product_hasDerivAt (X v : Configuration N) (s : ℝ) :
    HasDerivAt (fun s : ℝ => s • contraction F χ e (s • X) v)
      (contraction F χ e (s • X) v + s •
        ∑ j : Fin N × Fin 3, v j • couplingDerivative F χ hUV e j X (s • X)) s := by
  have h (j : Fin N × Fin 3) := (couplingCurve_hasDerivAt F χ hUV e j 0 X s).const_smul (v j)
  simp only [zero_add] at h
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => h j)
  convert! (hasDerivAt_id s).smul hs using 1
  simp only [one_smul, contraction, id_eq, Pi.smul_apply]
  abel

/-- The endpoint identity behind the curvature formula. -/
theorem radial_product_integral (X v : Configuration N) :
    (∫ s in (0 : ℝ)..1, contraction F χ e (s • X) v + s •
      ∑ j : Fin N × Fin 3, v j • couplingDerivative F χ hUV e j X (s • X)) =
      contraction F χ e X v := by
  have hc : Continuous (fun s : ℝ => contraction F χ e (s • X) v + s •
      ∑ j : Fin N × Fin 3, v j • couplingDerivative F χ hUV e j X (s • X)) := by
    apply Continuous.add
    · exact (contraction_continuous F χ e v).comp (continuous_id.smul continuous_const)
    · apply continuous_id.smul
      apply continuous_finsetSum
      intro j _
      exact (continuous_const : Continuous (fun _ : ℝ => v j)).smul
        ((couplingDerivative_continuous F χ hUV e j X).comp (continuous_id.smul continuous_const))
  simpa only [one_smul, zero_smul, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => radial_product_hasDerivAt F χ hUV e X v s) (hc.intervalIntegrable 0 1)

/-- The proved spatial derivative identifies the actual Weyl-gauge
connection, `A(X)[v] - ∂_v h_X`, with its curvature integral. -/
theorem radialConnection_eq (X v : Configuration N) :
    radialConnection F χ hUV e X v = contraction F χ e X v - labelDerivative F χ hUV e X v := by
  apply eq_sub_iff_add_eq.mpr
  unfold radialConnection labelDerivative
  have hi : IntervalIntegrable (fun s => labelIntegrandDerivative F χ hUV e X v 0 s) volume 0 1 :=
    ((labelIntegrandDerivative_continuous F χ hUV e X v).comp
      ((continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).prodMk continuous_id)).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_add
    ((angularIntegrand_continuous F χ hUV e X v).intervalIntegrable 0 1) hi]
  rw [← radial_product_integral F χ hUV e X v]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [labelIntegrandDerivative, zero_smul, add_zero, curvature, contraction,
    smul_sub, Finset.smul_sum, smul_smul]
  module

/-- Radial gauge is an identity for the constructed connection. -/
@[simp] theorem radialConnection_radial (X : Configuration N) :
    radialConnection F χ hUV e X X = 0 := by
  simp [radialConnection]



theorem curvature_real_smul_left (X v w : Configuration N) (c : ℝ) :
    curvature F χ hUV e X (c • v) w = c • curvature F χ hUV e X v w := by
  simp only [curvature, couplingDerivative_real_smul, PiLp.smul_apply,
    smul_eq_mul, smul_sub, Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

/-- The radial angular integral is precisely `r b(rθ)[ζ]`, so its proved
`-r²F` derivative applies to the transformed covariant derivative. -/
theorem angularLabel_eq_radialConnection (θ ζ : Configuration N) (r : ℝ) :
    angularLabel F χ hUV e θ ζ r = r • radialConnection F χ hUV e (r • θ) ζ := by
  unfold angularLabel radialConnection
  have hsub := intervalIntegral.smul_integral_comp_mul_right
    (fun s : ℝ => s • curvature F χ hUV e (s • θ) θ ζ) r (a := 0) (b := 1)
  simp only [zero_mul, one_mul] at hsub
  rw [← hsub]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only [curvature_real_smul_left, smul_smul]

end PfHk.RadialGauge
