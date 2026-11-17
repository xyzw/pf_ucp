import PfHk.CenteredRadialGauge
import PfHk.RadialGaugeCovariance

/-! Full spatial derivative and curvature connection for an arbitrary
center. The identities are proved by differentiation under the Bochner
integral and ordinary one-dimensional FTC. -/

noncomputable section
namespace PfHk.CenteredRadialGauge
open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian PfHk.PhysicalFieldRegularity
open scoped ENNReal InnerProductSpace Interval
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N)

/-- The derivative of the integrand of `h_(X+tv)` in direction `v`. -/
def labelIntegrandDerivative (X v : Configuration N) (t s : ℝ) : WeightedPhotonKernel :=
  (∑ j : Fin N × Fin 3, v j • couplingKernel F χ e O j (s • (X + t • v))) +
    ∑ j : Fin N × Fin 3, (s * (X + t • v) j) •
      couplingDerivative F χ hUV e O j v (s • (X + t • v))

theorem labelIntegrand_continuous (X v : Configuration N) :
    Continuous (fun p : ℝ × ℝ => rayIntegrand F χ e O (X + p.1 • v) p.2) := by
  unfold rayIntegrand
  apply continuous_finsetSum
  intro j _
  exact ((PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ) j).comp
    (continuous_const.add (continuous_fst.smul continuous_const))).smul
    ((couplingKernel_continuous F χ e O j).comp
      (continuous_snd.smul (continuous_const.add (continuous_fst.smul continuous_const))))

theorem labelIntegrandDerivative_continuous (X v : Configuration N) :
    Continuous (Function.uncurry (labelIntegrandDerivative F χ hUV e O X v)) := by
  unfold labelIntegrandDerivative Function.uncurry
  apply Continuous.add
  · apply continuous_finsetSum
    intro j _
    exact (continuous_const : Continuous (fun _ : ℝ × ℝ => v j)).smul
      ((couplingKernel_continuous F χ e O j).comp
        (continuous_snd.smul (continuous_const.add (continuous_fst.smul continuous_const))))
  · apply continuous_finsetSum
    intro j _
    exact (continuous_snd.mul ((PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ) j).comp
      (continuous_const.add (continuous_fst.smul continuous_const)))).smul
      ((couplingDerivative_continuous F χ hUV e O j v).comp
        (continuous_snd.smul (continuous_const.add (continuous_fst.smul continuous_const))))

theorem labelIntegrand_hasDerivAt (X v : Configuration N) (t s : ℝ) :
    HasDerivAt (fun t => rayIntegrand F χ e O (X + t • v) s)
      (labelIntegrandDerivative F χ hUV e O X v t s) t := by
  have h (j : Fin N × Fin 3) :
      HasDerivAt (fun t => couplingKernel F χ e O j (s • (X + t • v)))
        (s • couplingDerivative F χ hUV e O j v (s • (X + t • v))) t := by
    convert! couplingCurve_hasDerivAt F χ hUV e O j (s • X) (s • v) t using 1
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
    HasLineDerivAt ℝ (label F χ e O)
      (∫ s in (0 : ℝ)..1, labelIntegrandDerivative F χ hUV e O X v 0 s) X v := by
  exact RadialGauge.continuous_interval_hasDerivAt (fun t s => rayIntegrand F χ e O (X + t • v) s)
    (labelIntegrandDerivative F χ hUV e O X v) (labelIntegrand_continuous F χ e O X v)
    (labelIntegrandDerivative_continuous F χ hUV e O X v)
    (labelIntegrand_hasDerivAt F χ hUV e O X v) 0 1 0



/-- The one-form `Σ v_j g_j(X)`. -/
def contraction (X v : Configuration N) : WeightedPhotonKernel :=
  ∑ j : Fin N × Fin 3, v j • couplingKernel F χ e O j X

def radialConnection (X v : Configuration N) : WeightedPhotonKernel :=
  ∫ s in (0 : ℝ)..1, s • curvature F χ hUV e O (s • X) X v

def labelDerivative (X v : Configuration N) : WeightedPhotonKernel :=
  ∫ s in (0 : ℝ)..1, labelIntegrandDerivative F χ hUV e O X v 0 s

theorem contraction_continuous (v : Configuration N) :
    Continuous (fun X => contraction F χ e O X v) := by
  apply continuous_finsetSum
  intro j _
  exact (continuous_const : Continuous (fun _ : Configuration N => v j)).smul
    (couplingKernel_continuous F χ e O j)

theorem radial_product_hasDerivAt (X v : Configuration N) (s : ℝ) :
    HasDerivAt (fun s : ℝ => s • contraction F χ e O (s • X) v)
      (contraction F χ e O (s • X) v + s •
        ∑ j : Fin N × Fin 3, v j • couplingDerivative F χ hUV e O j X (s • X)) s := by
  have h (j : Fin N × Fin 3) := (couplingCurve_hasDerivAt F χ hUV e O j 0 X s).const_smul (v j)
  simp only [zero_add] at h
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => h j)
  convert! (hasDerivAt_id s).smul hs using 1
  simp only [one_smul, contraction, id_eq, Pi.smul_apply]
  abel

/-- The endpoint identity behind the curvature formula. -/
theorem radial_product_integral (X v : Configuration N) :
    (∫ s in (0 : ℝ)..1, contraction F χ e O (s • X) v + s •
      ∑ j : Fin N × Fin 3, v j • couplingDerivative F χ hUV e O j X (s • X)) =
      contraction F χ e O X v := by
  have hc : Continuous (fun s : ℝ => contraction F χ e O (s • X) v + s •
      ∑ j : Fin N × Fin 3, v j • couplingDerivative F χ hUV e O j X (s • X)) := by
    apply Continuous.add
    · exact (contraction_continuous F χ e O v).comp (continuous_id.smul continuous_const)
    · apply continuous_id.smul
      apply continuous_finsetSum
      intro j _
      exact (continuous_const : Continuous (fun _ : ℝ => v j)).smul
        ((couplingDerivative_continuous F χ hUV e O j X).comp (continuous_id.smul continuous_const))
  simpa only [one_smul, zero_smul, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => radial_product_hasDerivAt F χ hUV e O X v s) (hc.intervalIntegrable 0 1)

/-- The proved spatial derivative identifies the actual Weyl-gauge
connection, `A(X)[v] - ∂_v h_X`, with its curvature integral. -/
theorem radialConnection_eq (X v : Configuration N) :
    radialConnection F χ hUV e O X v = contraction F χ e O X v - labelDerivative F χ hUV e O X v := by
  apply eq_sub_iff_add_eq.mpr
  unfold radialConnection labelDerivative
  have hi : IntervalIntegrable (fun s => labelIntegrandDerivative F χ hUV e O X v 0 s) volume 0 1 :=
    ((labelIntegrandDerivative_continuous F χ hUV e O X v).comp
      ((continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).prodMk continuous_id)).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_add
    ((angularIntegrand_continuous F χ hUV e O X v).intervalIntegrable 0 1) hi]
  rw [← radial_product_integral F χ hUV e O X v]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [labelIntegrandDerivative, zero_smul, add_zero, curvature_eq, contraction,
    smul_sub, Finset.smul_sum, smul_smul]
  module

/-- Radial gauge is an identity for the constructed connection. -/
@[simp] theorem radialConnection_radial (X : Configuration N) :
    radialConnection F χ hUV e O X X = 0 := by
  simp [radialConnection]



/-- The radial angular integral is precisely `r b(rθ)[ζ]`, so its proved
`-r²F` derivative applies to the transformed covariant derivative. -/
theorem angularLabel_eq_radialConnection (θ ζ : Configuration N) (r : ℝ) :
    angularLabel F χ hUV e O θ ζ r = r • radialConnection F χ hUV e O (r • θ) ζ := by
  unfold angularLabel radialConnection
  have hsub := intervalIntegral.smul_integral_comp_mul_right
    (fun s : ℝ => s • curvature F χ hUV e O (s • θ) θ ζ) r (a := 0) (b := 1)
  simp only [zero_mul, one_mul] at hsub
  rw [← hsub]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only [curvature_real_smul_left, smul_smul]

theorem radialConnection_add (X v w : Configuration N) :
    radialConnection F χ hUV e O X (v + w) =
      radialConnection F χ hUV e O X v + radialConnection F χ hUV e O X w := by
  unfold radialConnection
  simp_rw [curvature_add_right, smul_add]
  exact intervalIntegral.integral_add
    ((angularIntegrand_continuous F χ hUV e O X v).intervalIntegrable 0 1)
    ((angularIntegrand_continuous F χ hUV e O X w).intervalIntegrable 0 1)

theorem radialConnection_real_smul (X v : Configuration N) (c : ℝ) :
    radialConnection F χ hUV e O X (c • v) = c • radialConnection F χ hUV e O X v := by
  unfold radialConnection
  simp_rw [curvature_real_smul_right, smul_comm _ c]
  exact intervalIntegral.integral_smul c _

/-- The actual connection is a continuous real-linear differential form. -/
def connectionMap (X : Configuration N) : Configuration N →L[ℝ] WeightedPhotonKernel :=
  LinearMap.toContinuousLinearMap
    { toFun := radialConnection F χ hUV e O X
      map_add' := radialConnection_add F χ hUV e O X
      map_smul' := fun c v => radialConnection_real_smul F χ hUV e O X v c }

@[simp] theorem connectionMap_apply (X v : Configuration N) :
    connectionMap F χ hUV e O X v = radialConnection F χ hUV e O X v := rfl

/-- Cartesian component contraction gives zero in radial gauge. -/
theorem radialConnection_components (X : Configuration N) :
    (∑ j : Fin N × Fin 3, X j • radialConnection F χ hUV e O X (EuclideanSpace.single j 1)) = 0 := by
  have hX : (∑ j : Fin N × Fin 3, X j • EuclideanSpace.single j 1) = X := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin N × Fin 3) ℝ).sum_repr X
  have h := congrArg (connectionMap F χ hUV e O X) hX
  simpa only [map_sum, map_smul, connectionMap_apply, radialConnection_radial] using h



/-- The angular connection is tangent in the actual ambient Cartesian
components used for the sphere gradient. -/
theorem angularLabel_components (θ : Configuration N) (r : ℝ) :
    (∑ j : Fin N × Fin 3, θ j • angularLabel F χ hUV e O θ (EuclideanSpace.single j 1) r) = 0 := by
  have hθ : (∑ j : Fin N × Fin 3, θ j • EuclideanSpace.single j 1) = θ := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin N × Fin 3) ℝ).sum_repr θ
  simp_rw [angularLabel_eq_radialConnection, smul_comm _ r]
  rw [← Finset.smul_sum]
  change r • (∑ j : Fin N × Fin 3, θ j • connectionMap F χ hUV e O (r • θ) (EuclideanSpace.single j 1)) = 0
  simp_rw [← map_smul]
  rw [← map_sum, hθ, ← map_smul]
  exact radialConnection_radial F χ hUV e O (r • θ)

theorem contraction_fixed (X v : Configuration N) :
    F.conjugation (contraction F χ e O X v).val.1 = (contraction F χ e O X v).val.1 :=
  RadialGauge.sum_fixed F _ (fun j => real_smul_fixed F _ _ (couplingKernel_fixed F χ e O j X))

theorem labelIntegrandDerivative_fixed (X v : Configuration N) (t s : ℝ) :
    F.conjugation (labelIntegrandDerivative F χ hUV e O X v t s).val.1 =
      (labelIntegrandDerivative F χ hUV e O X v t s).val.1 := by
  apply add_fixed F
  · exact RadialGauge.sum_fixed F _ (fun j => real_smul_fixed F _ _ (couplingKernel_fixed F χ e O j _))
  · exact RadialGauge.sum_fixed F _ (fun j => real_smul_fixed F _ _ (couplingDerivative_fixed F χ hUV e O j v _))

theorem labelDerivative_fixed (X v : Configuration N) :
    F.conjugation (labelDerivative F χ hUV e O X v).val.1 =
      (labelDerivative F χ hUV e O X v).val.1 := by
  apply integral_fixed F
  · exact ((labelIntegrandDerivative_continuous F χ hUV e O X v).comp
      ((continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).prodMk continuous_id)).intervalIntegrable 0 1
  · exact labelIntegrandDerivative_fixed F χ hUV e O X v 0

theorem radialConnection_fixed (X v : Configuration N) :
    F.conjugation (radialConnection F χ hUV e O X v).val.1 =
      (radialConnection F χ hUV e O X v).val.1 := by
  rw [radialConnection_eq]
  change F.realStructure.realCLM (_ - _) = _ - _
  rw [map_sub]
  exact congrArg₂ (fun a b : Lp ℂ 2 photonMeasure => a - b)
    (contraction_fixed F χ e O X v) (labelDerivative_fixed F χ hUV e O X v)

end PfHk.CenteredRadialGauge
