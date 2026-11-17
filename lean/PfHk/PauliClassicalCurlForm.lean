import PfHk.CoordinateMultiplierConvergence
import PfHk.ScalarSqrtLp

/-! The classical magnetic coefficient acts as an integrable sesquilinear
form. Only its square-root amplitude is multiplied into an H1 vector.
In particular, this file does not require the magnetic coefficient times
the vector itself to belong to L2. -/

noncomputable section
namespace PfHk.PauliClassicalCurlForm

open MeasureTheory Filter GptLean.ElectronicH1Space
  GptLean.PhysicalSourceCoordinates PfHk.CoordinateSobolev
open scoped ENNReal Topology InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 50000

section Scalar

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

theorem amplitude_memLp {p : ℝ} (_hp : 0 < p) {b : X → ℝ}
    (hb : MemLp b (ENNReal.ofReal p) ν) :
    MemLp (ScalarSqrtLp.amplitude b) (ENNReal.ofReal (2 * p)) ν := by
  have h := hb.norm_rpow_div (1 / 2)
  have he : ENNReal.ofReal p / (1 / 2) = ENNReal.ofReal (2 * p) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [div_eq_mul_inv, mul_comm]
  rw [he] at h
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h
  change MemLp (fun x => Real.sqrt |b x|) (ENNReal.ofReal (2 * p)) ν
  simpa only [Real.norm_eq_abs, ← Real.sqrt_eq_rpow] using h

theorem amplitude_norm_sq {p : ℝ} (hp : 0 < p) (b : X → ℝ) :
    (eLpNorm (ScalarSqrtLp.amplitude b) (ENNReal.ofReal (2 * p)) ν).toReal ^ 2 =
      (eLpNorm b (ENNReal.ofReal p) ν).toReal := by
  have h := eLpNorm_norm_rpow (p := ENNReal.ofReal (2 * p)) (μ := ν) b
    (by norm_num : (0 : ℝ) < 1 / 2)
  have he : ENNReal.ofReal (2 * p) * ENNReal.ofReal (1 / 2 : ℝ) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * p)]
    congr 1
    ring
  rw [he] at h
  have ht := congrArg ENNReal.toReal h
  simp only [← ENNReal.toReal_rpow, Real.norm_eq_abs, ← Real.sqrt_eq_rpow] at ht
  exact (congrArg (fun r : ℝ => r ^ 2) ht).trans (Real.sq_sqrt ENNReal.toReal_nonneg)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [InnerProductSpace ℂ H] in
/-- Cauchy--Schwarz for products of pointwise norms, in the exact L2 norm. -/
theorem integral_norm_mul_le (u v : Lp H 2 ν) :
    (∫ x, ‖u x‖ * ‖v x‖ ∂ν) ≤ ‖u‖ * ‖v‖ := by
  let r : Lp H 2 ν → Lp ℝ 2 ν := fun z => (Lp.memLp z).norm.toLp (fun x => ‖z x‖)
  have hr (z : Lp H 2 ν) : (r z : X → ℝ) =ᵐ[ν] fun x => ‖z x‖ :=
    (Lp.memLp z).norm.coeFn_toLp
  have hn (z : Lp H 2 ν) : ‖r z‖ = ‖z‖ := by
    dsimp only [r]
    rw [Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]
  have he : inner ℝ (r u) (r v) = ∫ x, ‖u x‖ * ‖v x‖ ∂ν := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hr u, hr v] with x hu hv
    simp only [hu, hv, Real.inner_apply]
  rw [← he, ← hn u, ← hn v]
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (r u) (r v))

def weightedInner (b : X → ℝ) (u v : Lp H 2 ν) (x : X) : ℂ :=
  (b x : ℂ) * inner ℂ (u x) (v x)

theorem weightedInner_bound (b : X → ℝ) (u v : Lp H 2 ν) (x : X) :
    ‖weightedInner b u v x‖ ≤
      ‖ScalarSqrtLp.amplitude b x • u x‖ * ‖ScalarSqrtLp.amplitude b x • v x‖ := by
  have hs := ScalarSqrtLp.amplitude_sq b x
  rw [weightedInner, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |b x| * (‖u x‖ * ‖v x‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (abs_nonneg _)
    _ = |ScalarSqrtLp.amplitude b x| ^ 2 * (‖u x‖ * ‖v x‖) := by
      rw [sq_abs, hs]
    _ = _ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs]
      ring

theorem weightedInner_integrable_bound (b : X → ℝ)
    (hb : AEStronglyMeasurable b ν) (u v au av : Lp H 2 ν)
    (hu : au =ᵐ[ν] fun x => ScalarSqrtLp.amplitude b x • u x)
    (hv : av =ᵐ[ν] fun x => ScalarSqrtLp.amplitude b x • v x) :
    Integrable (weightedInner b u v) ν ∧
      ‖∫ x, weightedInner b u v x ∂ν‖ ≤ ‖au‖ * ‖av‖ := by
  have hm : AEStronglyMeasurable (weightedInner b u v) ν :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hb).mul
      ((Lp.aestronglyMeasurable u).inner (Lp.aestronglyMeasurable v))
  have hi : Integrable (fun x => ‖au x‖ * ‖av x‖) ν :=
    (Lp.memLp au).norm.integrable_mul (Lp.memLp av).norm
  have hbound : ∀ᵐ x ∂ν, ‖weightedInner b u v x‖ ≤ ‖au x‖ * ‖av x‖ := by
    filter_upwards [hu, hv] with x hx hy
    rw [hx, hy]
    exact weightedInner_bound b u v x
  have hf : Integrable (weightedInner b u v) ν := hi.mono' hm hbound
  exact ⟨hf, (norm_integral_le_integral_norm _).trans
    ((integral_mono_ae hf.norm hi hbound).trans (integral_norm_mul_le au av))⟩

end Scalar

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

def pairing (n : Fin N) (b : Position → ℝ) (u v : L2 H (Fin N × Fin 3)) : ℂ :=
  ∫ x, weightedInner (coordinateCoefficient n b) u v x

/-- A raw Lp magnetic coefficient defines a form on coordinate Sobolev
vectors of order 3/(2p), strictly below one when p is above two. -/
theorem coordinate_bound (S : Data H N) {p : ℝ} (hp : 2 < p)
    (n : Fin N) (b : Position → ℝ) (hb : MemLp b (ENNReal.ofReal p) volume)
    (u v uB vB : L2 H (Fin N × Fin 3))
    (huB : BesselPair n (3 / (2 * p)) u uB)
    (hvB : BesselPair n (3 / (2 * p)) v vB) :
    Integrable (weightedInner (coordinateCoefficient n b) u v) volume ∧
      ‖pairing n b u v‖ ≤ S.constant (2 * p) ^ 2 *
        (eLpNorm b (ENNReal.ofReal p) volume).toReal * ‖uB‖ * ‖vB‖ := by
  have hp0 : 0 < p := by linarith
  have hp2 : 2 < 2 * p := by linarith
  have hs := amplitude_memLp hp0 hb
  obtain ⟨hu, hnu⟩ := coordinate_multiplier S hp2 n (ScalarSqrtLp.amplitude b) hs u uB huB
  obtain ⟨hv, hnv⟩ := coordinate_multiplier S hp2 n (ScalarSqrtLp.amplitude b) hs v vB hvB
  have hform := weightedInner_integrable_bound (coordinateCoefficient n b)
    (coordinateCoefficient_measurable n hb.aestronglyMeasurable) u v
    (hu.toLp _) (hv.toLp _) hu.coeFn_toLp hv.coeFn_toLp
  refine ⟨hform.1, hform.2.trans ?_⟩
  have hmul := mul_le_mul hnu hnv (norm_nonneg _) ((norm_nonneg _).trans hnu)
  apply hmul.trans_eq
  have hsq := amplitude_norm_sq (ν := volume) hp0 b
  calc
    _ = S.constant (2 * p) ^ 2 *
        (eLpNorm (ScalarSqrtLp.amplitude b) (ENNReal.ofReal (2 * p)) volume).toReal ^ 2 *
          ‖uB‖ * ‖vB‖ := by ring
    _ = _ := congrArg (fun t : ℝ => S.constant (2 * p) ^ 2 * t * ‖uB‖ * ‖vB‖) hsq

theorem pairing_tendsto_zero (S : Data H N) {p : ℝ} (hp : 2 < p)
    (n : Fin N) (b : ℕ → Position → ℝ)
    (hb : ∀ k, MemLp (b k) (ENNReal.ofReal p) volume)
    (hb0 : Tendsto (fun k => (eLpNorm (b k) (ENNReal.ofReal p) volume).toReal)
      atTop (𝓝 0))
    (u v uB vB : L2 H (Fin N × Fin 3))
    (huB : BesselPair n (3 / (2 * p)) u uB)
    (hvB : BesselPair n (3 / (2 * p)) v vB) :
    Tendsto (fun k => pairing n (b k) u v) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto (fun k => S.constant (2 * p) ^ 2 *
      (eLpNorm (b k) (ENNReal.ofReal p) volume).toReal * ‖uB‖ * ‖vB‖)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_const_nhds.mul hb0).mul tendsto_const_nhds).mul tendsto_const_nhds
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k =>
    (coordinate_bound S hp n (b k) (hb k) u v uB vB huB hvB).2) ht

end PfHk.PauliClassicalCurlForm
