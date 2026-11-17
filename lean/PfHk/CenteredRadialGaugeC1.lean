import PfHk.CenteredRadialGaugeConnection
import PfHk.C1FromLines

/-! Actual continuous Fréchet differentiability of the physical kernels
and radial label, derived from the proved Fourier line derivatives and
their jointly continuous bounded linear differential. -/

noncomputable section
namespace PfHk.CenteredRadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian PfHk.PhysicalFieldRegularity
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 250000
attribute [local irreducible] couplingKernel couplingDerivative contraction radialConnection
  labelDerivative label connectionMap

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N)

theorem couplingDerivative_add (j : Fin N × Fin 3) (v w X : Configuration N) :
    couplingDerivative F χ hUV e O j (v + w) X =
      couplingDerivative F χ hUV e O j v X + couplingDerivative F χ hUV e O j w X := by
  unfold couplingDerivative
  exact RadialGauge.couplingDerivative_add F χ hUV e j v w (O + X)

def couplingDifferential (j : Fin N × Fin 3) (X : Configuration N) :
    Configuration N →L[ℝ] WeightedPhotonKernel :=
  LinearMap.toContinuousLinearMap
    { toFun v := couplingDerivative F χ hUV e O j v X
      map_add' v w := couplingDerivative_add F χ hUV e O j v w X
      map_smul' c v := couplingDerivative_real_smul F χ hUV e O j X v c }

theorem couplingDifferential_continuous (j : Fin N × Fin 3) :
    Continuous (couplingDifferential F χ hUV e O j) := by
  apply continuous_clm_apply.mpr
  intro v
  exact couplingDerivative_continuous F χ hUV e O j v

include hUV in
theorem couplingKernel_contDiff (j : Fin N × Fin 3) :
    ContDiff ℝ (1 : ℕ∞) (couplingKernel F χ e O j) := by
  apply C1FromLines.contDiff_one (L := couplingDifferential F χ hUV e O j)
  · intro X v
    change HasDerivAt (fun s => couplingKernel F χ e O j (X + s • v))
      (couplingDerivative F χ hUV e O j v X) 0
    simpa only [zero_smul, add_zero] using
      couplingCurve_hasDerivAt F χ hUV e O j X v 0
  · exact couplingDifferential_continuous F χ hUV e O j

def contractionMap (X : Configuration N) : Configuration N →L[ℝ] WeightedPhotonKernel :=
  LinearMap.toContinuousLinearMap
    { toFun v := contraction F χ e O X v
      map_add' v w := by
        simp only [contraction, PiLp.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' c v := by
        simp only [contraction, PiLp.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul,
          RingHom.id_apply] }

theorem contractionMap_apply (X v : Configuration N) :
    contractionMap F χ e O X v = contraction F χ e O X v := rfl

theorem contractionMap_continuous : Continuous (contractionMap F χ e O) := by
  apply continuous_clm_apply.mpr
  intro v
  exact contraction_continuous F χ e O v

theorem radialConnection_continuous (v : Configuration N) :
    Continuous (fun X => radialConnection F χ hUV e O X v) := by
  have he : (fun X => radialConnection F χ hUV e O X v) =
      fun X => angularLabel F χ hUV e O X v 1 := by
    funext X
    simpa only [one_smul] using (angularLabel_eq_radialConnection F χ hUV e O X v 1).symm
  rw [he]
  exact angularLabel_continuous_theta F χ hUV e O v 1

theorem connectionMap_continuous : Continuous (connectionMap F χ hUV e O) := by
  apply continuous_clm_apply.mpr
  intro v
  convert! radialConnection_continuous F χ hUV e O v using 1
  exact funext fun X => connectionMap_apply F χ hUV e O X v

def labelDifferential (X : Configuration N) : Configuration N →L[ℝ] WeightedPhotonKernel :=
  contractionMap F χ e O X - connectionMap F χ hUV e O X

theorem labelDifferential_apply (X v : Configuration N) :
    labelDifferential F χ hUV e O X v = labelDerivative F χ hUV e O X v := by
  simp only [labelDifferential, sub_apply, contractionMap_apply, connectionMap_apply]
  rw [radialConnection_eq]
  abel

theorem labelDifferential_continuous : Continuous (labelDifferential F χ hUV e O) := by
  apply continuous_clm_apply.mpr
  intro v
  convert! (contraction_continuous F χ e O v).sub
    (radialConnection_continuous F χ hUV e O v) using 1
  funext X
  simp only [labelDifferential, sub_apply, contractionMap_apply, connectionMap_apply, Pi.sub_apply]

theorem label_hasFDerivAt (X : Configuration N) :
    HasFDerivAt (label F χ e O) (labelDifferential F χ hUV e O X) X := by
  apply C1FromLines.hasFDerivAt
  · intro Y v
    rw [labelDifferential_apply]
    simpa only [labelDerivative] using label_hasLineDerivAt F χ hUV e O Y v
  · exact (labelDifferential_continuous F χ hUV e O).continuousAt

include hUV in
theorem label_contDiff : ContDiff ℝ (1 : ℕ∞) (label F χ e O) :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨labelDifferential F χ hUV e O, labelDifferential_continuous F χ hUV e O,
      label_hasFDerivAt F χ hUV e O⟩

end PfHk.CenteredRadialGauge
