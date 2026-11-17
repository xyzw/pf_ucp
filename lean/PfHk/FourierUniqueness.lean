import GptLean.PhysicalSmearedKernel
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Uniqueness of the actual unnormalized Fourier coefficient used in the
Pauli--Fierz field kernels. The proof reduces real L¹ functions to the
uniqueness theorem for finite positive measures already proved in mathlib.
-/

noncomputable section

namespace PfHk.FourierUniqueness

open MeasureTheory Filter GptLean Gaussian PhysicalGroundState
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 400000

private theorem finite_density (w : FieldSpace → ℝ) (hw : Integrable w volume)
    (hpos : ∀ x, 0 ≤ w x) :
    IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (w x))) :=
  isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hw.aestronglyMeasurable
      (ae_of_all _ hpos)).mpr hw)

private theorem charFun_density (w : FieldSpace → ℝ) (hw : Integrable w volume)
    (hpos : ∀ x, 0 ≤ w x) (t : FieldSpace) :
    charFun (volume.withDensity (fun x => ENNReal.ofReal (w x))) t =
      PhysicalGroundState.fourierCoeff w (-t) := by
  rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul₀
    hw.aemeasurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  unfold PhysicalGroundState.fourierCoeff
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    simp [ENNReal.toReal_ofReal (hpos x), fieldPhase, inner_neg_left,
      real_inner_comm, Complex.real_smul, mul_comm]

private theorem positive_sub_negative (r : ℝ) : max r 0 - max (-r) 0 = r := by
  rcases le_total r 0 with h | h
  · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
  · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]

/-- L¹ injectivity of the physical Fourier coefficient, with no normalization
factor and with the sign convention of `pf_ucp.tex`. -/
theorem ae_eq_zero_of_fourierCoeff_zero (w : FieldSpace → ℝ)
    (hw : Integrable w volume) (hzero : ∀ k, PhysicalGroundState.fourierCoeff w k = 0) :
    w =ᵐ[volume] 0 := by
  let wpos : FieldSpace → ℝ := fun x => max (w x) 0
  let wneg : FieldSpace → ℝ := fun x => max (-w x) 0
  have hpos : Integrable wpos volume := hw.pos_part
  have hneg : Integrable wneg volume := hw.neg_part
  have hpos0 (x : FieldSpace) : 0 ≤ wpos x := le_max_right _ _
  have hneg0 (x : FieldSpace) : 0 ≤ wneg x := le_max_right _ _
  let μpos := volume.withDensity (fun x => ENNReal.ofReal (wpos x))
  let μneg := volume.withDensity (fun x => ENNReal.ofReal (wneg x))
  have : IsFiniteMeasure μpos := finite_density wpos hpos hpos0
  have : IsFiniteMeasure μneg := finite_density wneg hneg hneg0
  have heq : μpos = μneg := by
    apply Measure.ext_of_charFun
    funext t
    apply sub_eq_zero.mp
    change charFun (volume.withDensity (fun x => ENNReal.ofReal (wpos x))) t -
      charFun (volume.withDensity (fun x => ENNReal.ofReal (wneg x))) t = 0
    rw [charFun_density wpos hpos hpos0, charFun_density wneg hneg hneg0]
    calc
      PhysicalGroundState.fourierCoeff wpos (-t) - PhysicalGroundState.fourierCoeff wneg (-t) = PhysicalGroundState.fourierCoeff w (-t) := by
        unfold PhysicalGroundState.fourierCoeff
        rw [← integral_sub (integrable_phase_mul wpos hpos (-t))
          (integrable_phase_mul wneg hneg (-t))]
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          dsimp only
          rw [← mul_sub, ← Complex.ofReal_sub]
          congr 2
          exact positive_sub_negative (w x)
      _ = 0 := hzero _
  have heq_ae := (withDensity_eq_iff_of_sigmaFinite
    hpos.aemeasurable.ennreal_ofReal hneg.aemeasurable.ennreal_ofReal).mp heq
  filter_upwards [heq_ae] with x hx
  have hr := congrArg ENNReal.toReal hx
  simp only [ENNReal.toReal_ofReal (hpos0 x), ENNReal.toReal_ofReal (hneg0 x)] at hr
  have hs : wpos x - wneg x = w x := positive_sub_negative (w x)
  change w x = 0
  linarith

/-- Almost-everywhere vanishing in momentum space suffices because the
Fourier coefficient of an L¹ function is continuous. -/
theorem ae_eq_zero_of_fourierCoeff_ae_zero (w : FieldSpace → ℝ)
    (hw : Integrable w volume) (hzero : PhysicalGroundState.fourierCoeff w =ᵐ[volume] 0) :
    w =ᵐ[volume] 0 := by
  have h := Measure.eq_of_ae_eq hzero (continuous_fourierCoeff w hw) continuous_zero
  apply ae_eq_zero_of_fourierCoeff_zero w hw
  intro k
  exact congrFun h k

/-- Componentwise Fourier uniqueness for the three-dimensional ambiguity
field in `prop-cutoff-kernel`. -/
theorem vector_ae_eq_zero_of_fourierCoeff_ae_zero (b : FieldSpace → FieldSpace)
    (hb : ∀ a : Fin 3, Integrable (fun x => b x a) volume)
    (hzero : ∀ᵐ k ∂volume, ∀ a : Fin 3,
      PhysicalGroundState.fourierCoeff (fun x => b x a) k = 0) :
    b =ᵐ[volume] 0 := by
  have hcomponents : ∀ a : Fin 3, (fun x => b x a) =ᵐ[volume] 0 := by
    intro a
    exact ae_eq_zero_of_fourierCoeff_ae_zero _ (hb a)
      (hzero.mono fun k hk => hk a)
  filter_upwards [ae_all_iff.mpr hcomponents] with x hx
  ext a
  exact hx a

end PfHk.FourierUniqueness
