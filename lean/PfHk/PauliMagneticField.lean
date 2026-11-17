import PfHk.RadialGaugeCurvature

/-! The physical quantized magnetic field on the full radiation graph.
Its kernels are the actual coordinate curl of the polarization kernels.
Only the first ultraviolet moment is used. -/

noncomputable section
namespace PfHk.PauliMagneticField

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel Gaussian PfHk.PhysicalFieldRegularity

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

private theorem sum_scaled_add {S : Type*} [Fintype S] (a : ℝ) (f g : S → ℝ) :
    (∑ s, a * (f s + g s)) = a * ((∑ s, f s) + ∑ s, g s) := by
  rw [← Finset.mul_sum, Finset.sum_add_distrib]

def next (i : Fin 3) : Fin 3 := i + 1
def last (i : Fin 3) : Fin 3 := i + 2

variable (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)

/-- Coordinate curl of the actual weighted one-photon coupling. -/
def kernel (i : Fin 3) (x : FieldSpace) : WeightedPhotonKernel :=
  directionKernel F χ hUV (last i) (EuclideanSpace.single (next i) 1) x -
    directionKernel F χ hUV (next i) (EuclideanSpace.single (last i) 1) x

theorem kernel_eq_curl (i : Fin 3) (x : FieldSpace) :
    kernel F χ hUV i x =
      lineDeriv ℝ (physicalKernel F χ (last i)) x (EuclideanSpace.single (next i) 1) -
        lineDeriv ℝ (physicalKernel F χ (next i)) x (EuclideanSpace.single (last i) 1) := by
  rw [(physicalKernel_hasLineDerivAt F χ hUV (last i)
    (EuclideanSpace.single (next i) 1) x).lineDeriv,
    (physicalKernel_hasLineDerivAt F χ hUV (next i)
      (EuclideanSpace.single (last i) 1) x).lineDeriv]
  rfl

theorem kernel_continuous (i : Fin 3) : Continuous (kernel F χ hUV i) :=
  (directionKernel_continuous F χ hUV (last i) (EuclideanSpace.single (next i) 1)).sub
    (directionKernel_continuous F χ hUV (next i) (EuclideanSpace.single (last i) 1))

/-- A uniform bound from the already constructed ultraviolet moment. -/
theorem kernel_norm_le (i : Fin 3) (x : FieldSpace) :
    ‖kernel F χ hUV i x‖ ≤ 2 * RadialGauge.momentBound F χ hUV := by
  have ha := directionKernel_uniform_bound F χ hUV (last i)
    (EuclideanSpace.single (next i) 1) x
  have hb := directionKernel_uniform_bound F χ hUV (next i)
    (EuclideanSpace.single (last i) 1) x
  simp only [PiLp.norm_single, norm_one, one_mul] at ha hb
  exact (norm_sub_le _ _).trans ((add_le_add ha hb).trans_eq (by
    dsimp [RadialGauge.momentBound]
    ring))

attribute [local irreducible] RadialGauge.momentBound radiationGraphDerivative radiationGraphInclusion

variable (C : CanonicalSectorCCR photonMeasure)

/-- Each magnetic component is a Segal field on the actual Fock space. -/
def field (i : Fin 3) (x : FieldSpace) : RadiationGraphSpace →L[ℂ] PhotonFock :=
  kernelField C (kernel F χ hUV i x)

theorem field_sq_le (i : Fin 3) (x : FieldSpace) (q : RadiationGraphSpace) :
    ‖field F χ hUV C i x q‖ ^ 2 ≤
      20 * (RadialGauge.momentBound F χ hUV) ^ 2 *
        (‖radiationGraphDerivative q‖ ^ 2 + ‖radiationGraphInclusion q‖ ^ 2) := by
  have hk := pow_le_pow_left₀ (norm_nonneg _) (kernel_norm_le F χ hUV i x) 2
  have hf := RadialGauge.fieldEvaluation_sq_le C (kernel F χ hUV i x) q
  change ‖field F χ hUV C i x q‖ ^ 2 ≤ _ at hf
  calc
    _ ≤ 5 * ‖kernel F χ hUV i x‖ ^ 2 *
        (‖radiationGraphDerivative q‖ ^ 2 + ‖radiationGraphInclusion q‖ ^ 2) := hf
    _ ≤ 5 * (2 * RadialGauge.momentBound F χ hUV) ^ 2 *
        (‖radiationGraphDerivative q‖ ^ 2 + ‖radiationGraphInclusion q‖ ^ 2) := by
      gcongr
    _ = _ := by ring

theorem sum_field_sq_le (x : FieldSpace) (q : RadiationGraphSpace) :
    (∑ i : Fin 3, ‖field F χ hUV C i x q‖ ^ 2) ≤
      60 * (RadialGauge.momentBound F χ hUV) ^ 2 *
        (‖radiationGraphDerivative q‖ ^ 2 + ‖radiationGraphInclusion q‖ ^ 2) := by
  calc
    _ ≤ ∑ _i : Fin 3, 20 * (RadialGauge.momentBound F χ hUV) ^ 2 *
        (‖radiationGraphDerivative q‖ ^ 2 + ‖radiationGraphInclusion q‖ ^ 2) :=
      Finset.sum_le_sum (fun i _ => field_sq_le F χ hUV C i x q)
    _ = _ := by simp; ring

/-- The magnetic-field estimate survives finite spin amplification with
the same constant and the sum of the physical component energies. -/
theorem finite_sum_field_sq_le {S : Type*} [Fintype S]
    (x : FieldSpace) (q : S → RadiationGraphSpace) :
    (∑ s : S, ∑ i : Fin 3, ‖field F χ hUV C i x (q s)‖ ^ 2) ≤
      60 * (RadialGauge.momentBound F χ hUV) ^ 2 *
        ((∑ s : S, ‖radiationGraphDerivative (q s)‖ ^ 2) +
          ∑ s : S, ‖radiationGraphInclusion (q s)‖ ^ 2) := by
  calc
    _ ≤ ∑ s : S, 60 * (RadialGauge.momentBound F χ hUV) ^ 2 *
        (‖radiationGraphDerivative (q s)‖ ^ 2 + ‖radiationGraphInclusion (q s)‖ ^ 2) :=
      Finset.sum_le_sum (fun s _ => sum_field_sq_le F χ hUV C x (q s))
    _ = _ := sum_scaled_add _ _ _

end PfHk.PauliMagneticField
