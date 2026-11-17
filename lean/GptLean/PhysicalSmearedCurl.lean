import GptLean.PhysicalSmearedKernel

/-!
The curl of test fields and the magnetic kernels.

The curl of a test field is again a test field, with Fourier coefficients
`(∇×u)^ = i k × û`. Applying this twice gives
`(∇×∇×v)^ = |k|² v̂ - k (k · v̂)`. The polarization vectors are orthogonal to `k`,
so the longitudinal part drops out of the smeared kernel: `g_{∇×∇×v} = ω² g_v`.
The smeared magnetic field is `∫ w · B = ∫ (∇×w) · A`, the Segal field of
`g_{∇×w}`. For `w = ∇×v` its kernel is `(ω f, √ω f)` with `f = ω g_v`.
-/

noncomputable section

namespace GptLean.PhysicalGroundState

open MeasureTheory Filter PhysicalFock PhysicalPairSpace Gaussian PhysicalPolarization
open scoped ENNReal InnerProductSpace ContDiff

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

namespace TestField

variable (u : TestField)

/-- The partial derivative `∂_j u^a`. -/
def pderiv (a j : Fin 3) (x : FieldSpace) : ℝ :=
  fderiv ℝ (u.comp a) x (EuclideanSpace.single j 1)

theorem pderiv_contDiff (a j : Fin 3) : ContDiff ℝ ∞ (u.pderiv a j) :=
  (contDiff_infty_iff_fderiv.mp (u.comp_contDiff a)).2.clm_apply contDiff_const

theorem pderiv_eq_zero (a j : Fin 3) {x : FieldSpace} (hx : x ∉ tsupport u.fn) :
    u.pderiv a j x = 0 := by
  have hx' : x ∉ tsupport (u.comp a) := fun h =>
    hx (tsupport_comp_subset (g := fun v : Vector => v a) (by simp) u.fn h)
  unfold pderiv
  rw [fderiv_of_notMem_tsupport ℝ hx', zero_apply]

theorem pderiv_integrable (a j : Fin 3) : Integrable (u.pderiv a j) volume :=
  (u.pderiv_contDiff a j).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.intro u.compact fun _ hx => u.pderiv_eq_zero a j hx)

theorem fourierCoeff_partial' (a j : Fin 3) (k : FieldSpace) :
    fourierCoeff (u.pderiv a j) k = ((k j : ℂ) * Complex.I) * fourierCoeff (u.comp a) k :=
  fourierCoeff_partial (u.comp a) (u.comp_contDiff_one a) (u.comp_compact a) j k

/-- The components of the curl. -/
def curlComp : Fin 3 → FieldSpace → ℝ :=
  ![fun x => u.pderiv 2 1 x - u.pderiv 1 2 x, fun x => u.pderiv 0 2 x - u.pderiv 2 0 x,
    fun x => u.pderiv 1 0 x - u.pderiv 0 1 x]

theorem curlComp_contDiff (a : Fin 3) : ContDiff ℝ ∞ (u.curlComp a) := by
  match a with
  | 0 => exact (u.pderiv_contDiff 2 1).sub (u.pderiv_contDiff 1 2)
  | 1 => exact (u.pderiv_contDiff 0 2).sub (u.pderiv_contDiff 2 0)
  | 2 => exact (u.pderiv_contDiff 1 0).sub (u.pderiv_contDiff 0 1)

theorem curlComp_eq_zero (a : Fin 3) {x : FieldSpace} (hx : x ∉ tsupport u.fn) :
    u.curlComp a x = 0 := by
  match a with
  | 0 =>
    change u.pderiv 2 1 x - u.pderiv 1 2 x = 0
    rw [u.pderiv_eq_zero 2 1 hx, u.pderiv_eq_zero 1 2 hx, sub_zero]
  | 1 =>
    change u.pderiv 0 2 x - u.pderiv 2 0 x = 0
    rw [u.pderiv_eq_zero 0 2 hx, u.pderiv_eq_zero 2 0 hx, sub_zero]
  | 2 =>
    change u.pderiv 1 0 x - u.pderiv 0 1 x = 0
    rw [u.pderiv_eq_zero 1 0 hx, u.pderiv_eq_zero 0 1 hx, sub_zero]

/-- The curl `∇ × u` of a test field. -/
def curl : TestField where
  fn x := WithLp.toLp 2 (fun a => u.curlComp a x)
  smooth := contDiff_piLp' 2 fun a => u.curlComp_contDiff a
  compact := HasCompactSupport.intro u.compact fun x hx => by
    apply PiLp.ext
    intro a
    exact u.curlComp_eq_zero a hx

theorem curl_comp (a : Fin 3) : u.curl.comp a = u.curlComp a := rfl

end TestField

theorem fourierCoeff_sub (w w' : FieldSpace → ℝ) (hw : Integrable w volume)
    (hw' : Integrable w' volume) (k : FieldSpace) :
    fourierCoeff (fun x => w x - w' x) k = fourierCoeff w k - fourierCoeff w' k := by
  unfold fourierCoeff
  rw [← integral_sub (integrable_phase_mul w hw k) (integrable_phase_mul w' hw' k)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Complex.ofReal_sub, mul_sub]

/-- **`(∇×u)^ = i k × û`.** -/
theorem fourierCoeff_curl (u : TestField) (k : FieldSpace) :
    fourierCoeff (u.curl.comp 0) k = Complex.I *
        ((k 1 : ℂ) * fourierCoeff (u.comp 2) k - (k 2 : ℂ) * fourierCoeff (u.comp 1) k) ∧
      fourierCoeff (u.curl.comp 1) k = Complex.I *
        ((k 2 : ℂ) * fourierCoeff (u.comp 0) k - (k 0 : ℂ) * fourierCoeff (u.comp 2) k) ∧
      fourierCoeff (u.curl.comp 2) k = Complex.I *
        ((k 0 : ℂ) * fourierCoeff (u.comp 1) k - (k 1 : ℂ) * fourierCoeff (u.comp 0) k) := by
  refine ⟨?_, ?_, ?_⟩
  · refine (fourierCoeff_sub _ _ (u.pderiv_integrable 2 1) (u.pderiv_integrable 1 2) k).trans ?_
    rw [u.fourierCoeff_partial' 2 1 k, u.fourierCoeff_partial' 1 2 k]
    ring
  · refine (fourierCoeff_sub _ _ (u.pderiv_integrable 0 2) (u.pderiv_integrable 2 0) k).trans ?_
    rw [u.fourierCoeff_partial' 0 2 k, u.fourierCoeff_partial' 2 0 k]
    ring
  · refine (fourierCoeff_sub _ _ (u.pderiv_integrable 1 0) (u.pderiv_integrable 0 1) k).trans ?_
    rw [u.fourierCoeff_partial' 1 0 k, u.fourierCoeff_partial' 0 1 k]
    ring

/-- **`(∇×∇×v)^ = |k|² v̂ - k (k · v̂)`.** -/
theorem fourierCoeff_curlCurl (v : TestField) (k : FieldSpace) (a : Fin 3) :
    fourierCoeff (v.curl.curl.comp a) k =
      ((‖k‖ ^ 2 : ℝ) : ℂ) * fourierCoeff (v.comp a) k -
        (k a : ℂ) * ∑ b, (k b : ℂ) * fourierCoeff (v.comp b) k := by
  obtain ⟨h0, h1, h2⟩ := fourierCoeff_curl v.curl k
  obtain ⟨g0, g1, g2⟩ := fourierCoeff_curl v k
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_three]
  push_cast
  match a with
  | 0 =>
    rw [h0, g2, g1]
    linear_combination ((k 1 : ℂ) * (k 0 : ℂ) * fourierCoeff (v.comp 1) k -
      (k 1 : ℂ) ^ 2 * fourierCoeff (v.comp 0) k - (k 2 : ℂ) ^ 2 * fourierCoeff (v.comp 0) k +
      (k 2 : ℂ) * (k 0 : ℂ) * fourierCoeff (v.comp 2) k) * Complex.I_sq
  | 1 =>
    rw [h1, g0, g2]
    linear_combination ((k 2 : ℂ) * (k 1 : ℂ) * fourierCoeff (v.comp 2) k -
      (k 2 : ℂ) ^ 2 * fourierCoeff (v.comp 1) k - (k 0 : ℂ) ^ 2 * fourierCoeff (v.comp 1) k +
      (k 0 : ℂ) * (k 1 : ℂ) * fourierCoeff (v.comp 0) k) * Complex.I_sq
  | 2 =>
    rw [h2, g1, g0]
    linear_combination ((k 0 : ℂ) * (k 2 : ℂ) * fourierCoeff (v.comp 0) k -
      (k 0 : ℂ) ^ 2 * fourierCoeff (v.comp 2) k - (k 1 : ℂ) ^ 2 * fourierCoeff (v.comp 2) k +
      (k 1 : ℂ) * (k 2 : ℂ) * fourierCoeff (v.comp 1) k) * Complex.I_sq

variable (F : Frame) (χ : ArticleCutoff)

/-- The polarization vectors are orthogonal to the momentum. -/
theorem epsilon_transverse (k : FieldSpace) (l : Fin 2) :
    ∑ a, F.epsilon k l a * k a = 0 := by
  have hinner : inner ℝ (F.epsilon k l) k = 0 := by
    by_cases hk : k = 0
    · rw [hk, inner_zero_right]
    · have hk' : k = ‖k‖ • F.basis k 2 := by
        rw [F.radial k hk, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hk), one_smul]
      have hne : l.castSucc ≠ (2 : Fin 3) := by
        fin_cases l <;> decide
      have h0 : inner ℝ (F.basis k l.castSucc) (F.basis k 2) = 0 :=
        (F.basis k).orthonormal.2 hne
      exact (congrArg (fun z : FieldSpace => inner ℝ (F.basis k l.castSucc) z) hk').trans
        ((inner_smul_right _ _ _).trans (by rw [h0, mul_zero]))
  rw [← hinner, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun a _ => by simp [mul_comm]

theorem base_transverse (p : PhotonMode) : ∑ a, base F χ a p * ((p.1 a : ℝ) : ℂ) = 0 := by
  have h := epsilon_transverse F p.1 p.2
  have hc : ((∑ a, F.epsilon p.1 p.2 a * p.1 a : ℝ) : ℂ) = 0 := by rw [h, Complex.ofReal_zero]
  simp only [base]
  calc
    _ = ((∑ a, F.epsilon p.1 p.2 a * p.1 a : ℝ) : ℂ) * χ.value (-p.1) / (Real.sqrt 2 : ℂ) := by
      push_cast
      rw [Finset.sum_mul, Finset.sum_div]
      exact Finset.sum_congr rfl fun a _ => by ring
    _ = 0 := by rw [hc, zero_mul, zero_div]

/-- **`g_{∇×∇×v} = ω² g_v`.** -/
theorem smearedFun_curlCurl (v : TestField) (p : PhotonMode) :
    smearedFun F χ v.curl.curl p = ((‖p.1‖ ^ 2 : ℝ) : ℂ) * smearedFun F χ v p := by
  unfold smearedFun
  simp only [fourierCoeff_curlCurl, Fin.sum_univ_three]
  have ht := base_transverse F χ p
  rw [Fin.sum_univ_three] at ht
  linear_combination (-(((p.1 0 : ℝ) : ℂ) * fourierCoeff (v.comp 0) p.1 +
    ((p.1 1 : ℝ) : ℂ) * fourierCoeff (v.comp 1) p.1 +
    ((p.1 2 : ℝ) : ℂ) * fourierCoeff (v.comp 2) p.1)) * ht

/-- The smeared magnetic field kernel: `∫ w · B = ∫ (∇×w) · A = Φ(g_{∇×w})`. -/
def magneticKernel (w : TestField) : WeightedPhotonKernel := smearedKernel F χ w.curl

/-- The Ampère direction `f = ω g_v` as a photon `L²` function. -/
def omegaSmearedL2 (v : TestField) : Lp ℂ 2 photonMeasure := (omegaSmeared_memLp F χ v).toLp _

private theorem sqrt_weight (t : ℝ) (ht : 0 < t) (g : ℂ) :
    ((Real.sqrt t : ℝ) : ℂ)⁻¹ * (((t ^ 2 : ℝ) : ℂ) * g) =
      ((Real.sqrt t : ℝ) : ℂ) * (((t : ℝ) : ℂ) * g) := by
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hne : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr ht)
  rw [inv_mul_eq_iff_eq_mul₀ hne]
  have ht2 : ((t ^ 2 : ℝ) : ℂ) = ((Real.sqrt t : ℝ) : ℂ) * ((Real.sqrt t : ℝ) : ℂ) * ((t : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← sq, hs, sq]
  rw [ht2]
  ring

/-- The magnetic kernel of `∇×v` is the weighted kernel `(ω f, √ω f)` of `f = ω g_v`. -/
theorem magneticKernel_curl_snd (v : TestField) :
    ∀ᵐ p ∂photonMeasure, (magneticKernel F χ v.curl).val.2 p =
      ((Real.sqrt ‖p.1‖ : ℝ) : ℂ) * omegaSmearedL2 F χ v p := by
  filter_upwards [(weightedSmeared_memLp F χ v.curl.curl).coeFn_toLp,
    (omegaSmeared_memLp F χ v).coeFn_toLp, PhysicalOnePhotonFourier.momentum_nonzero]
    with p h₁ h₂ h₀
  refine h₁.trans ((congrArg (fun z : ℂ => ((Real.sqrt ‖p.1‖ : ℝ) : ℂ)⁻¹ * z)
    (smearedFun_curlCurl F χ v p)).trans ((sqrt_weight ‖p.1‖ (norm_pos_iff.mpr h₀)
      (smearedFun F χ v p)).trans ?_))
  exact congrArg (fun z : ℂ => ((Real.sqrt ‖p.1‖ : ℝ) : ℂ) * z) h₂.symm

end GptLean.PhysicalGroundState
