import GptLean.RepresentabilityCoherent
import GptLean.Transformations
import GptLean.CoherentSobolevLimits

/-! The complex coherent phase and its horizontal and Berry derivatives. -/

noncomputable section

namespace GptLean.Representability

open MeasureTheory PhysicalFock
open scoped InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

/-- The imaginary part of the complex inner product as a real bilinear map. -/
def berryBilinear : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (LinearMap.mk₂ ℝ (fun f h : Lp ℂ 2 μ => (⟪f, h⟫_ℂ).im)
    (fun f g h => by simp only [inner_add_left, Complex.add_im])
    (fun r f h => by
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, smul_eq_mul]
      exact (congrArg (fun z : ℂ => (z * ⟪f, h⟫_ℂ).im) (Complex.conj_ofReal r)).trans
        (Complex.im_ofReal_mul r ⟪f, h⟫_ℂ))
    (fun f g h => by simp only [inner_add_right, Complex.add_im])
    (fun r f h => by
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, smul_eq_mul]
      exact Complex.im_ofReal_mul r ⟪f, h⟫_ℂ)) 1
    (fun f h => by
      simp only [one_mul, Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans (norm_inner_le_norm f h))

omit [SigmaFinite μ] in
@[simp] theorem berryBilinear_apply (f h : Lp ℂ 2 μ) :
    berryBilinear μ f h = (⟪f, h⟫_ℂ).im := rfl

def vacuumCreationIsometry : Lp ℂ 2 μ →ₗᵢ[ℝ] Fock μ where
  toLinearMap := (creationDirection μ 0 (vacuumSector μ)).toLinearMap
  norm_map' h := creationWord_single_norm μ h

@[simp] theorem vacuumCreationIsometry_apply (h : Lp ℂ 2 μ) :
    vacuumCreationIsometry μ h = creationWord μ [h] := rfl

namespace ConcreteWeylLaw

variable (W : ConcreteWeylLaw μ)

def phaseCoherent (S : ℝ) (f : Lp ℂ 2 μ) : Fock μ :=
  Complex.exp (Complex.I * (S : ℂ)) • W.coherent μ f

theorem phaseCoherent_norm (S : ℝ) (f : Lp ℂ 2 μ) : ‖W.phaseCoherent μ S f‖ = 1 := by
  rw [phaseCoherent, norm_smul, Complex.norm_exp_I_mul_ofReal, W.coherent_norm, mul_one]

theorem phaseCoherent_continuous :
    Continuous (fun p : ℝ × Lp ℂ 2 μ => W.phaseCoherent μ p.1 p.2) :=
  (Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst))).smul
      ((W.coherent_continuous μ).comp continuous_snd)

def phaseHorizontal (S : ℝ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ →ₗᵢ[ℝ] Fock μ where
  toLinearMap :=
    ((((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Fock μ →L[ℝ] Fock μ)) (Complex.exp (Complex.I * (S : ℂ)))).comp
      (((W.weyl f).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).comp
        (vacuumCreationIsometry μ).toContinuousLinearMap)).toLinearMap
  norm_map' h := by
    change ‖Complex.exp (Complex.I * (S : ℂ)) • W.weyl f (creationWord μ [h])‖ = ‖h‖
    rw [norm_smul, Complex.norm_exp_I_mul_ofReal, one_mul, (W.weyl f).norm_map,
      creationWord_single_norm]

@[simp] theorem phaseHorizontal_apply (S : ℝ) (f h : Lp ℂ 2 μ) :
    W.phaseHorizontal μ S f h =
      Complex.exp (Complex.I * (S : ℂ)) • W.weyl f (creationWord μ [h]) := rfl

theorem phaseHorizontal_continuous :
    Continuous (fun p : (ℝ × Lp ℂ 2 μ) × Lp ℂ 2 μ => W.phaseHorizontal μ p.1.1 p.1.2 p.2) := by
  change Continuous (fun p : (ℝ × Lp ℂ 2 μ) × Lp ℂ 2 μ =>
    Complex.exp (Complex.I * (p.1.1 : ℂ)) • W.weyl p.1.2 (vacuumCreationIsometry μ p.2))
  exact (Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_fst.comp continuous_fst)))).smul
      (W.continuous.comp ((continuous_snd.comp continuous_fst).prodMk
        ((vacuumCreationIsometry μ).continuous.comp continuous_snd)))

def phaseCoherentDerivative (S : ℝ) (f : Lp ℂ 2 μ) (dS : ℝ) (h : Lp ℂ 2 μ) : Fock μ :=
  Complex.exp (Complex.I * (S : ℂ)) •
    (W.coherentDerivative μ f h + (Complex.I * (dS : ℂ)) • W.coherent μ f)

theorem phaseCoherentDerivative_split (S : ℝ) (f : Lp ℂ 2 μ) (dS : ℝ) (h : Lp ℂ 2 μ) :
    W.phaseCoherentDerivative μ S f dS h = W.phaseHorizontal μ S f h +
      (dS + (⟪f, h⟫_ℂ).im) • (Complex.I • W.phaseCoherent μ S f) := by
  rw [phaseCoherentDerivative, coherentDerivative_apply, map_add, map_smul,
    phaseHorizontal_apply, phaseCoherent, coherent]
  simp only [smul_add, smul_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  module

theorem phaseCoherentDerivative_connection (S : ℝ) (f : Lp ℂ 2 μ) (dS : ℝ) (h : Lp ℂ 2 μ) :
    ⟪W.phaseCoherent μ S f, W.phaseCoherentDerivative μ S f dS h⟫_ℂ =
      Complex.I * ((dS + (⟪f, h⟫_ℂ).im : ℝ) : ℂ) := by
  rw [phaseCoherent, phaseCoherentDerivative, inner_smul_left, inner_smul_right, ← mul_assoc,
    Complex.conj_mul', Complex.norm_exp_I_mul_ofReal]
  simp only [one_pow, Complex.ofReal_one, one_mul]
  exact Transformations.coherent_phase_connection _ _ _ _ (W.coherent_norm μ f)
    (W.coherent_connection μ f h)

theorem phaseCoherentDerivative_metric (S : ℝ) (f : Lp ℂ 2 μ) (dS : ℝ) (h : Lp ℂ 2 μ) :
    ‖W.phaseCoherentDerivative μ S f dS h‖ ^ 2 =
      ‖h‖ ^ 2 + (dS + (⟪f, h⟫_ℂ).im) ^ 2 := by
  rw [phaseCoherentDerivative, norm_smul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact Transformations.coherent_phase_metric _ _ _ _ _ (W.coherent_norm μ f)
    (W.coherent_connection μ f h) (W.coherent_metric μ f h)

theorem phaseCoherent_hasDerivAt {S : ℝ → ℝ} {f : ℝ → Lp ℂ 2 μ}
    {dS t : ℝ} {df : Lp ℂ 2 μ} (hS : HasDerivAt S dS t) (hf : HasDerivAt f df t) :
    HasDerivAt (fun s => W.phaseCoherent μ (S s) (f s))
      (W.phaseCoherentDerivative μ (S t) (f t) dS df) t := by
  have he := (hS.ofReal_comp.const_mul Complex.I).cexp
  have hc := (W.coherent_hasFDerivAt μ (f t)).comp_hasDerivAt t hf
  apply (he.smul hc).congr_deriv
  change Complex.exp (Complex.I * (S t : ℂ)) • W.coherentDerivative μ (f t) df +
    (Complex.exp (Complex.I * (S t : ℂ)) * (Complex.I * (dS : ℂ))) • W.coherent μ (f t) =
      Complex.exp (Complex.I * (S t : ℂ)) •
        (W.coherentDerivative μ (f t) df + (Complex.I * (dS : ℂ)) • W.coherent μ (f t))
  rw [smul_add, smul_smul]

end ConcreteWeylLaw

end GptLean.Representability
