import GptLean.TransformationsDilation
import GptLean.TransformationsFockScaling
import GptLean.ElectronicH1Map
import GptLean.PhysicalPFReference

/-!
Dilations on the actual common Pauli--Fierz reference domain,
`prop-dilation-covariance`.

For `λ > 0` the map `V_λ = S_λ ⊗ Γ(Υ_λ†)` acts by
`(V_λ Ψ)(x) = λ^{d/2} Γ(Υ_λ†) Ψ(λ x)`. It is a unitary of the wave space and
maps the reference domain bijectively onto itself; here the reference domain
does not depend on the cutoff, and its Coulomb coordinate is preserved
because the Coulomb potential is homogeneous of degree `-1`. Ordinary
derivatives scale by `λ`, the radiation and Coulomb square roots by `√λ`.
If the field kernels of the two cutoffs are related by
`κ_Λ(x) = λ Υ_λ† κ_{Λ/λ}(λ x)`, the covariant derivatives obey
`D^{Λ} (V_λ u) = λ V_λ D^{Λ/λ} u`, and the energy obeys `energy-scaling`:

`E_Λ (V_λ u) = λ² K_{Λ/λ}(u) + λ R(u) + λ C(u)`.
-/

noncomputable section

namespace GptLean.TransformationsDilation

open MeasureTheory PhysicalFock PhysicalPFReference TransformationsFock
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

local instance radiationNormedSpace : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace

variable {I : Type} [Fintype I] [DecidableEq I] {r : ℝ} (hr : 0 < r)
  (W : PhotonFock ≃ₗᵢ[ℂ] PhotonFock)

/-- `(V v)(x) = r^{d/2} W (v (r x))` on the wave space. -/
def waveDilation (v : WaveSpace I) : WaveSpace I :=
  dilation hr ((W.toLinearIsometry.toContinuousLinearMap).compLpL 2 volume v)

theorem waveDilation_ae (v : WaveSpace I) :
    waveDilation hr W v =ᵐ[volume] fun x => (factor I r : ℂ) • W (v (r • x)) := by
  unfold waveDilation
  filter_upwards [dilation_ae hr ((W.toLinearIsometry.toContinuousLinearMap).compLpL 2 volume v),
    (Measure.quasiMeasurePreserving_smul volume hr.ne').ae
      ((W.toLinearIsometry.toContinuousLinearMap).coeFn_compLpL v)] with x h₁ h₂
  exact h₁.trans (congrArg (fun y => (factor I r : ℂ) • y) h₂)

theorem waveDilation_add (v w : WaveSpace I) :
    waveDilation hr W (v + w) = waveDilation hr W v + waveDilation hr W w :=
  (congrArg (dilation hr) (map_add ((W.toLinearIsometry.toContinuousLinearMap).compLpL 2 volume)
    v w)).trans (map_add (dilation hr) _ _)

theorem waveDilation_sub (v w : WaveSpace I) :
    waveDilation hr W (v - w) = waveDilation hr W v - waveDilation hr W w :=
  (congrArg (dilation hr) (map_sub ((W.toLinearIsometry.toContinuousLinearMap).compLpL 2 volume)
    v w)).trans (map_sub (dilation hr) _ _)

theorem waveDilation_smul (a : ℂ) (v : WaveSpace I) :
    waveDilation hr W (a • v) = a • waveDilation hr W v :=
  (congrArg (dilation hr) (map_smul ((W.toLinearIsometry.toContinuousLinearMap).compLpL 2 volume)
    a v)).trans (map_smul (dilation hr) a _)

theorem norm_waveDilation (v : WaveSpace I) : ‖waveDilation hr W v‖ = ‖v‖ := by
  refine ((dilation hr).norm_map _).trans ?_
  have h : eLpNorm ((W.toLinearIsometry.toContinuousLinearMap).compLpL 2 volume v) 2 volume =
      eLpNorm v 2 volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards [(W.toLinearIsometry.toContinuousLinearMap).coeFn_compLpL v] with x hx
    exact (congrArg norm hx).trans (W.norm_map (v x))
  exact congrArg ENNReal.toReal h

/-- The inverse dilation inverts `waveDilation`. -/
theorem waveDilation_inv (v : WaveSpace I) :
    waveDilation (inv_pos.mpr hr) W.symm (waveDilation hr W v) = v := by
  apply Lp.ext
  have hs := (Measure.quasiMeasurePreserving_smul volume (inv_pos.mpr hr).ne').ae_eq_comp
    (waveDilation_ae hr W v)
  filter_upwards [waveDilation_ae (inv_pos.mpr hr) W.symm (waveDilation hr W v), hs] with x h₁ h₂
  simp only [Function.comp_apply] at h₂
  refine h₁.trans ?_
  rw [h₂, map_smul, smul_smul, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, ← Complex.ofReal_mul,
    factor_inv_mul hr, Complex.ofReal_one, one_smul]
  exact W.symm_apply_apply (v x)

theorem waveDilation_inv_left (v : WaveSpace I) :
    waveDilation hr W (waveDilation (inv_pos.mpr hr) W.symm v) = v := by
  apply Lp.ext
  have hs := (Measure.quasiMeasurePreserving_smul volume hr.ne').ae_eq_comp
    (waveDilation_ae (inv_pos.mpr hr) W.symm v)
  filter_upwards [waveDilation_ae hr W (waveDilation (inv_pos.mpr hr) W.symm v), hs] with x h₁ h₂
  simp only [Function.comp_apply] at h₂
  refine h₁.trans ?_
  rw [h₂, map_smul, smul_smul, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, ← Complex.ofReal_mul]
  have hf : factor I r * factor I r⁻¹ = 1 := by rw [mul_comm]; exact factor_inv_mul hr
  rw [hf, Complex.ofReal_one, one_smul]
  exact W.apply_symm_apply (v x)

/-- The electronic graph map. -/
def electronicDilation (w : ElectronicGraph I) : ElectronicGraph I :=
  dilationH1 hr (ElectronicH1Map.map (W.toLinearIsometry.toContinuousLinearMap) w)

theorem value_electronicDilation (w : ElectronicGraph I) :
    ElectronicH1Complex.value (electronicDilation hr W w) =
      waveDilation hr W (ElectronicH1Complex.value w) := rfl

theorem derivative_electronicDilation (i : I) (w : ElectronicGraph I) :
    ElectronicH1Complex.derivative i (electronicDilation hr W w) =
      r • waveDilation hr W (ElectronicH1Complex.derivative i w) := rfl

variable (Wr : RadiationGraphSpace ≃L[ℂ] RadiationGraphSpace) (a : ℂ)
  (hincl : ∀ q, radiationGraphInclusion (Wr q) = W (radiationGraphInclusion q))
  (hderiv : ∀ q, radiationGraphDerivative (Wr q) = a • W (radiationGraphDerivative q))

/-- The radiation-graph map. -/
def radiationDilation' (q : RadiationGraph I) : RadiationGraph I :=
  dilationLinear hr ((Wr : RadiationGraphSpace →L[ℂ] RadiationGraphSpace).compLpL 2 volume q)

theorem radiationDilation'_ae (q : RadiationGraph I) :
    radiationDilation' hr Wr q =ᵐ[volume] fun x => (factor I r : ℂ) • Wr (q (r • x)) := by
  unfold radiationDilation'
  filter_upwards [dilationLinear_ae hr
      ((Wr : RadiationGraphSpace →L[ℂ] RadiationGraphSpace).compLpL 2 volume q),
    (Measure.quasiMeasurePreserving_smul volume hr.ne').ae
      ((Wr : RadiationGraphSpace →L[ℂ] RadiationGraphSpace).coeFn_compLpL q)] with x h₁ h₂
  exact h₁.trans (congrArg (fun y => (factor I r : ℂ) • y) h₂)

include hincl in
theorem inclusion_radiationDilation' (q : RadiationGraph I) :
    spatialRadiationInclusion volume (radiationDilation' hr Wr q) =
      waveDilation hr W (spatialRadiationInclusion volume q) := by
  apply Lp.ext
  have hs := (Measure.quasiMeasurePreserving_smul volume hr.ne').ae
    (radiationGraphInclusion.coeFn_compLpL q)
  filter_upwards [radiationGraphInclusion.coeFn_compLpL (radiationDilation' hr Wr q),
    radiationDilation'_ae hr Wr q, waveDilation_ae hr W (spatialRadiationInclusion volume q), hs]
    with x h₁ h₂ h₃ h₄
  refine h₁.trans ((congrArg radiationGraphInclusion h₂).trans (Eq.trans ?_ h₃.symm))
  exact (map_smul radiationGraphInclusion _ _).trans (congrArg (fun y => (factor I r : ℂ) • y)
    ((hincl _).trans (congrArg W h₄.symm)))

include hderiv in
theorem derivative_radiationDilation' (q : RadiationGraph I) :
    spatialRadiationDerivative volume (radiationDilation' hr Wr q) =
      a • waveDilation hr W (spatialRadiationDerivative volume q) := by
  apply Lp.ext
  have hs := (Measure.quasiMeasurePreserving_smul volume hr.ne').ae
    (radiationGraphDerivative.coeFn_compLpL q)
  filter_upwards [radiationGraphDerivative.coeFn_compLpL (radiationDilation' hr Wr q),
    radiationDilation'_ae hr Wr q, waveDilation_ae hr W (spatialRadiationDerivative volume q), hs,
    Lp.coeFn_smul a (waveDilation hr W (spatialRadiationDerivative volume q))]
    with x h₁ h₂ h₃ h₄ h₅
  refine h₁.trans ((congrArg radiationGraphDerivative h₂).trans (Eq.trans ?_ h₅.symm))
  refine (map_smul radiationGraphDerivative _ _).trans ((congrArg (fun y => (factor I r : ℂ) • y)
    ((hderiv _).trans (congrArg (fun y => a • W y) h₄.symm))).trans
      ((smul_comm _ a _).trans ?_))
  exact congrArg (fun y => a • y) h₃.symm

variable (V : Position I → ℝ) (hV : ∀ x, V (r • x) = r⁻¹ * V x)

private theorem scalar_algebra {E : Type*} [AddCommGroup E] [Module ℂ E] (w : E) (a b c t : ℂ)
    (h : a * b = t) {z : E} (hz : z = b • w) : a • (c • z) = t • (c • w) := by
  rw [hz, smul_comm c b, smul_smul, h]

include hV in
theorem potentialDilation_mem (p : PotentialGraph I V) :
    ((waveDilation hr W p.val.1, (Real.sqrt r : ℂ) • waveDilation hr W p.val.2) :
        WaveSpace I × WaveSpace I) ∈
      PhysicalMultiplicationGraph.graph volume (H := PhotonFock)
        (fun x => (Real.sqrt (V x) : ℂ)) := by
  have hp : ∀ᵐ x ∂volume, p.val.2 x = (Real.sqrt (V x) : ℂ) • p.val.1 x := p.property
  change ∀ᵐ x ∂volume, ((Real.sqrt r : ℂ) • waveDilation hr W p.val.2) x =
    (Real.sqrt (V x) : ℂ) • waveDilation hr W p.val.1 x
  filter_upwards [(Measure.quasiMeasurePreserving_smul volume hr.ne').ae hp,
    waveDilation_ae hr W p.val.1, waveDilation_ae hr W p.val.2,
    Lp.coeFn_smul (Real.sqrt r : ℂ) (waveDilation hr W p.val.2)] with x hx h₁ h₂ h₃
  have hsq : Real.sqrt r * Real.sqrt (V (r • x)) = Real.sqrt (V x) := by
    rw [hV x, Real.sqrt_mul (inv_nonneg.mpr hr.le), Real.sqrt_inv, ← mul_assoc,
      mul_inv_cancel₀ (Real.sqrt_pos.mpr hr).ne', one_mul]
  have hc : ((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt (V (r • x)) : ℝ) : ℂ) =
      ((Real.sqrt (V x) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hsq]
  refine h₃.trans ((congrArg (fun y => (Real.sqrt r : ℂ) • y) (h₂.trans
    (congrArg (fun y => (factor I r : ℂ) • W y) hx))).trans (Eq.trans ?_
      (congrArg (fun y => (Real.sqrt (V x) : ℂ) • y) h₁.symm)))
  exact scalar_algebra (W (p.val.1 (r • x))) _ _ _ _ hc (map_smul W _ _)

/-- The Coulomb-graph map. -/
def potentialDilation (p : PotentialGraph I V) : PotentialGraph I V :=
  ⟨(waveDilation hr W p.val.1, (Real.sqrt r : ℂ) • waveDilation hr W p.val.2),
    potentialDilation_mem hr W V hV p⟩

/-- The dilation `V_λ` on the common reference domain. -/
def dilate (u : Reference I V) : Reference I V :=
  ⟨(electronicDilation hr W (electronic I V u), radiationDilation' hr Wr (radiationSource I V u),
      potentialDilation hr W V hV (potentialSource I V u)), by
    change (ElectronicH1Complex.value (electronicDilation hr W (electronic I V u)) -
        spatialRadiationInclusion volume (radiationDilation' hr Wr (radiationSource I V u)),
      ElectronicH1Complex.value (electronicDilation hr W (electronic I V u)) -
        waveDilation hr W (potentialSource I V u).val.1) = (0, 0)
    apply Prod.ext
    · exact sub_eq_zero.mpr ((congrArg (waveDilation hr W) (radiation_matches I V u).symm).trans
        (inclusion_radiationDilation' hr W Wr hincl (radiationSource I V u)).symm)
    · exact sub_eq_zero.mpr (congrArg (waveDilation hr W) (potential_matches I V u).symm)⟩

theorem inclusion_dilate (u : Reference I V) :
    inclusion I V (dilate hr W Wr hincl V hV u) = waveDilation hr W (inclusion I V u) := rfl

theorem ordinary_dilate (i : I) (u : Reference I V) :
    ordinary I V i (dilate hr W Wr hincl V hV u) = r • waveDilation hr W (ordinary I V i u) := rfl

include hderiv in
theorem radiation_dilate (u : Reference I V) :
    radiation I V (dilate hr W Wr hincl V hV u) = a • waveDilation hr W (radiation I V u) :=
  derivative_radiationDilation' hr W Wr a hderiv (radiationSource I V u)

theorem potential_dilate (u : Reference I V) :
    potential I V (dilate hr W Wr hincl V hV u) =
      (Real.sqrt r : ℂ) • waveDilation hr W (potential I V u) := rfl

variable (C : CanonicalSectorCCR photonMeasure)
  (κ κ' : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume) (hκ' : ∀ i, AEStronglyMeasurable (κ' i) volume)
  (M M' : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (hbound' : ∀ i, ∀ᵐ x ∂volume, ‖κ' i x‖ ≤ M')
  (hkern : ∀ i x q, kernelField C (κ i x) (Wr q) = r • W (kernelField C (κ' i (r • x)) q))

include hkern in
/-- Scaled kernels make the dilation scale the field by `λ`. -/
theorem field_dilate (i : I) (u : Reference I V) :
    field I V C κ hκ M hbound i (dilate hr W Wr hincl V hV u) =
      r • waveDilation hr W (field I V C κ' hκ' M' hbound' i u) := by
  apply Lp.ext
  have hs := (Measure.quasiMeasurePreserving_smul volume hr.ne').ae
    (spatialField_ae volume C (κ' i) (hκ' i) M' (hbound' i) (radiationSource I V u))
  filter_upwards [spatialField_ae volume C (κ i) (hκ i) M (hbound i)
      (radiationDilation' hr Wr (radiationSource I V u)),
    radiationDilation'_ae hr Wr (radiationSource I V u),
    Lp.coeFn_smul r (waveDilation hr W (field I V C κ' hκ' M' hbound' i u)),
    waveDilation_ae hr W (field I V C κ' hκ' M' hbound' i u), hs] with x h₁ h₂ h₃ h₄ h₅
  change spatialField volume C (κ i) (hκ i) M (hbound i)
      (radiationDilation' hr Wr (radiationSource I V u)) x = _
  refine h₁.trans ((congrArg (kernelField C (κ i x)) h₂).trans ?_)
  refine (map_smul (kernelField C (κ i x)) _ _).trans ((congrArg (fun y => (factor I r : ℂ) • y)
    (hkern i x _)).trans ((smul_comm _ r _).trans (Eq.trans ?_ h₃.symm)))
  exact congrArg (fun y => r • y) ((congrArg (fun y => (factor I r : ℂ) • W y) h₅.symm).trans
    h₄.symm)

private theorem real_norm_mul_sq (t X : ℝ) : (‖t‖ * X) ^ 2 = t ^ 2 * X ^ 2 := by
  rw [Real.norm_eq_abs, mul_pow, sq_abs]

private theorem sqrt_norm_mul_sq {t : ℝ} (ht : 0 < t) (X : ℝ) :
    (‖(Real.sqrt t : ℂ)‖ * X) ^ 2 = t * X ^ 2 := by
  rw [mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt ht.le]

private theorem energy_algebra {ι : Type*} [Fintype ι] (r : ℝ) (f : ι → ℝ) (A B : ℝ) :
    (1 / 2 : ℝ) * (∑ i, r ^ 2 * f i) + A + B = r ^ 2 * ((1 / 2 : ℝ) * ∑ i, f i) + A + B := by
  rw [← Finset.mul_sum]
  ring

private theorem covariant_algebra {E : Type*} [AddCommGroup E] [Module ℂ E] (L : E → E)
    (hsub : ∀ a b, L (a - b) = L a - L b) (hsmul : ∀ (c : ℂ) a, L (c • a) = c • L a)
    (d f : E) (e r : ℝ) :
    (-Complex.I) • (r • L d) - (e : ℂ) • (r • L f) = r • L ((-Complex.I) • d - (e : ℂ) • f) := by
  rw [hsub, hsmul, hsmul, smul_sub, smul_comm r, smul_comm r]

include hkern in
/-- The covariant-derivative law `D^{Λ} (V_λ u) = λ V_λ D^{Λ/λ} u`. -/
theorem covariant_dilate (e : ℝ) (i : I) (u : Reference I V) :
    covariant I V C κ hκ M hbound e i (dilate hr W Wr hincl V hV u) =
      r • waveDilation hr W (covariant I V C κ' hκ' M' hbound' e i u) :=
  (covariant_apply I V C κ hκ M hbound e i (dilate hr W Wr hincl V hV u)).trans
    ((congrArg₂ (fun p q : WaveSpace I => (-Complex.I) • p - (e : ℂ) • q)
      (ordinary_dilate hr W Wr hincl V hV i u)
      (field_dilate hr W Wr hincl V hV C κ κ' hκ hκ' M M' hbound hbound' hkern i u)).trans
      ((covariant_algebra (waveDilation hr W) (waveDilation_sub hr W) (waveDilation_smul hr W)
        (ordinary I V i u) (field I V C κ' hκ' M' hbound' i u) e r).trans
        (congrArg (fun z => r • waveDilation hr W z)
          (covariant_apply I V C κ' hκ' M' hbound' e i u).symm)))

include hkern hderiv in
/-- **The dilation identity `energy-scaling`** on the reference domain:
the kinetic energy scales by `λ²`, the radiation energy by `‖a‖²` and the
Coulomb energy by `λ`. For the physical photon dilation `‖a‖² = λ`. -/
theorem energy_dilate (e : ℝ) (u : Reference I V) :
    energy I V C κ hκ M hbound e (dilate hr W Wr hincl V hV u) =
      r ^ 2 * kineticEnergy I V C κ' hκ' M' hbound' e u + ‖a‖ ^ 2 * ‖radiation I V u‖ ^ 2 +
        r * ‖potential I V u‖ ^ 2 := by
  have hk (i : I) : ‖covariant I V C κ hκ M hbound e i (dilate hr W Wr hincl V hV u)‖ ^ 2 =
      r ^ 2 * ‖covariant I V C κ' hκ' M' hbound' e i u‖ ^ 2 := by
    refine (congrArg (· ^ 2) ((congrArg norm (covariant_dilate hr W Wr hincl V hV C κ κ' hκ hκ'
      M M' hbound hbound' hkern e i u)).trans ((norm_smul _ _).trans
        (congrArg (fun t => ‖r‖ * t) (norm_waveDilation hr W _))))).trans (real_norm_mul_sq r _)
  have hr' : ‖radiation I V (dilate hr W Wr hincl V hV u)‖ ^ 2 =
      ‖a‖ ^ 2 * ‖radiation I V u‖ ^ 2 := by
    refine (congrArg (· ^ 2) ((congrArg norm (radiation_dilate hr W Wr a hincl hderiv V hV u)).trans
      ((norm_smul _ _).trans (congrArg (fun t => ‖a‖ * t) (norm_waveDilation hr W _))))).trans
      (mul_pow _ _ _)
  have hp : ‖potential I V (dilate hr W Wr hincl V hV u)‖ ^ 2 = r * ‖potential I V u‖ ^ 2 := by
    refine (congrArg (· ^ 2) ((norm_smul _ _).trans
      (congrArg (fun t => ‖(Real.sqrt r : ℂ)‖ * t) (norm_waveDilation hr W _)))).trans
      (sqrt_norm_mul_sq hr _)
  unfold energy kineticEnergy
  refine (congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) (Finset.sum_congr rfl fun i _ => hk i)) hr') hp).trans
    (energy_algebra r _ _ _)

end GptLean.TransformationsDilation
