import PfHk.PhysicalLocalEnergyRough
import GptLean.PhysicalSourceCurrentBounds
import GptLean.PhysicalFockFieldSymmetry
import PfHk.NormWeakH1Finite

/-! The diamagnetic step for the actual Fock-valued weak derivative.
The field expectation is real by the proved symmetry of the Segal field.
The rough external magnetic multiplier is real as well. -/

noncomputable section

namespace PfHk.PhysicalLocalEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply
  kernelField radiationGraphInclusion radiationGraphDerivative externalCovariant roughMultiply

section Fiber

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]

theorem normGradient_le_covariant (f d field : H) (e A : ℝ)
    (hfield : (⟪f, field⟫_ℂ).im = 0) :
    ((⟪f, d⟫_ℂ).re / ‖f‖) ^ 2 ≤
      ‖(-Complex.I) • d - (e : ℂ) • field + A • f‖ ^ 2 := by
  have ha : (⟪f, (e : ℂ) • field - A • f⟫_ℂ).im = 0 := by
    have hself : (⟪f, f⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) f
    rw [inner_sub_right, inner_smul_right, inner_smul_right_eq_smul]
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.smul_im, hfield, hself,
      mul_zero, zero_mul, zero_add, sub_zero, smul_zero]
  have h := PhysicalSourceCurrentBounds.inner_joint f d
    ((e : ℂ) • field - A • f) 1 ha
  have hid : (-Complex.I) • d - (1 : ℂ) • ((e : ℂ) • field - A • f) =
      (-Complex.I) • d - (e : ℂ) • field + A • f := by
    simp only [one_smul]
    abel
  simp only [Complex.ofReal_one] at h
  rw [hid] at h
  by_cases hf : ‖f‖ = 0
  · simp [hf]
  · rw [div_pow, div_le_iff₀ (sq_pos_of_ne_zero hf)]
    nlinarith [sq_nonneg (⟪f, (-Complex.I) • d - (e : ℂ) • field + A • f⟫_ℂ).re]

end Fiber

variable {I : Type} [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

theorem field_expectation_real (u : Reference I V) (i : I) :
    ∀ᵐ x ∂volume,
      (⟪inclusion I V u x, field I V C κ hκ M hbound i u x⟫_ℂ).im = 0 := by
  have hi : (inclusion I V u : Position I → PhotonFock) =ᵐ[volume]
      fun x => radiationGraphInclusion (radiationSource I V u x) :=
    (Filter.EventuallyEq.of_eq (congrArg (fun f : WaveSpace I => ⇑f)
      (radiation_matches I V u).symm)).trans
        (radiationGraphInclusion.coeFn_compLpL (radiationSource I V u))
  have hf : (field I V C κ hκ M hbound i u : Position I → PhotonFock) =ᵐ[volume]
      fun x => kernelField C (κ i x) (radiationSource I V u x) := by
    simpa only [PhysicalPFReference.field, ContinuousLinearMap.comp_apply] using
      spatialField_ae volume C (κ i) (hκ i) M (hbound i) (radiationSource I V u)
  filter_upwards [hi, hf] with x hx hfx
  let q := radiationSource I V u x
  have hz : (⟪radiationGraphInclusion q, kernelField C (κ i x) q⟫_ℂ).im = 0 :=
    Complex.conj_eq_iff_im.mp
      ((inner_conj_symm (kernelField C (κ i x) q) (radiationGraphInclusion q)).trans
        (kernelField_symmetric C (κ i x) q q))
  exact (congrArg Complex.im (congrArg₂ (fun v w : PhotonFock => ⟪v, w⟫_ℂ) hx hfx)).trans hz

def normGradient (u : Reference I V) (i : I) (x : Position I) : ℝ :=
  (⟪inclusion I V u x, ordinary I V i u x⟫_ℂ).re / ‖inclusion I V u x‖

theorem normGradient_memLp (u : Reference I V) (i : I) :
    MemLp (normGradient V u i) 2 volume := by
  have hf := Lp.aestronglyMeasurable (inclusion I V u)
  have hd := Lp.aestronglyMeasurable (ordinary I V i u)
  have hre : AEMeasurable (fun x => (⟪inclusion I V u x, ordinary I V i u x⟫_ℂ).re)
      volume := Complex.continuous_re.measurable.comp_aemeasurable
        (hf.inner (𝕜 := ℂ) hd).aemeasurable
  exact ((Lp.memLp (ordinary I V i u)).norm).mono'
    (hre.div hf.norm.aemeasurable).aestronglyMeasurable
    (ae_of_all _ fun x => PhysicalSourceCurrentBounds.norm_re_inner_div_norm_le _ _)

variable (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

theorem externalCovariant_ae (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) (i : I) :
    externalCovariant V C κ hκ M hbound e A positive negative u hu i =ᵐ[volume]
      fun x => (-Complex.I) • ordinary I V i u x -
        (e : ℂ) • field I V C κ hκ M hbound i u x + A i x • inclusion I V u x := by
  have he : externalCovariant V C κ hκ M hbound e A positive negative u hu i =
      (-Complex.I) • ordinary I V i u - (e : ℂ) • field I V C κ hκ M hbound i u +
      roughMultiply (A i) (inclusion I V u) (hu.vector i) := by
    unfold externalCovariant
    exact congrArg (fun z : WaveSpace I => z +
      roughMultiply (A i) (inclusion I V u) (hu.vector i))
      (covariant_apply I V C κ hκ M hbound e i u)
  apply (Filter.EventuallyEq.of_eq (congrArg (fun z : WaveSpace I => ⇑z) he)).trans
  filter_upwards [Lp.coeFn_add
      ((-Complex.I) • ordinary I V i u - (e : ℂ) • field I V C κ hκ M hbound i u)
      (roughMultiply (A i) (inclusion I V u) (hu.vector i)),
    Lp.coeFn_sub ((-Complex.I) • ordinary I V i u)
      ((e : ℂ) • field I V C κ hκ M hbound i u),
    Lp.coeFn_smul (-Complex.I) (ordinary I V i u),
    Lp.coeFn_smul (e : ℂ) (field I V C κ hκ M hbound i u),
    roughMultiply_ae (A i) (inclusion I V u) (hu.vector i)] with x h₁ h₂ h₃ h₄ h₅
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at h₁ h₂ h₃ h₄
  exact h₁.trans (congrArg₂ (· + ·) (h₂.trans (congrArg₂ (· - ·) h₃ h₄)) h₅)

/-- Pointwise diamagnetism, including unbounded real external vector
potentials whose products with the form vector lie in L2. -/
theorem diamagnetic_ae (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) :
    ∀ᵐ x ∂volume, (∑ i, normGradient V u i x ^ 2) ≤
      ∑ i, ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i x‖ ^ 2 := by
  have hf : ∀ᵐ x ∂volume, ∀ i,
      (⟪inclusion I V u x, field I V C κ hκ M hbound i u x⟫_ℂ).im = 0 :=
    ae_all_iff.mpr (field_expectation_real V C κ hκ M hbound u)
  have hp : ∀ᵐ x ∂volume, ∀ i,
      externalCovariant V C κ hκ M hbound e A positive negative u hu i x =
        (-Complex.I) • ordinary I V i u x -
          (e : ℂ) • field I V C κ hκ M hbound i u x + A i x • inclusion I V u x :=
    ae_all_iff.mpr (externalCovariant_ae V C κ hκ M hbound e A positive negative u hu)
  filter_upwards [hf, hp] with x hfx hpx
  apply Finset.sum_le_sum
  intro i _
  rw [hpx i]
  exact normGradient_le_covariant _ _ _ e (A i x) (hfx i)

theorem l2_norm_sq (u : WaveSpace I) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  have h := Repair.toL2_norm_sq (Lp.memLp u)
  simpa only [Lp.toLp_coeFn] using h

def normGradientEnergy (u : Reference I V) : ℝ :=
  ∑ i, ∫ x, normGradient V u i x ^ 2

theorem normGradientEnergy_nonneg (u : Reference I V) :
    0 ≤ normGradientEnergy V u :=
  Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _

theorem diamagnetic_integrated (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) :
    normGradientEnergy V u ≤
      ∑ i, ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i‖ ^ 2 := by
  have hi (i : I) : Integrable (fun x => normGradient V u i x ^ 2) volume :=
    (normGradient_memLp V u i).integrable_sq
  have hj (i : I) : Integrable
      (fun x => ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i x‖ ^ 2)
      volume := (Lp.memLp (externalCovariant V C κ hκ M hbound e A positive negative u hu i)).norm.integrable_sq
  simp only [normGradientEnergy, l2_norm_sq]
  rw [← integral_finsetSum _ (fun i _ => hi i),
    ← integral_finsetSum _ (fun i _ => hj i)]
  exact integral_mono_ae (integrable_finsetSum _ (fun i _ => hi i))
    (integrable_finsetSum _ (fun i _ => hj i))
    (diamagnetic_ae V C κ hκ M hbound e A positive negative u hu)

section WeakNorm

variable {J : Type} [Fintype J] [DecidableEq J] (W : Position J → ℝ)

/-- The norm has the displayed genuine weak gradient. Division at zero
sets the gradient to zero, exactly as in the norm chain theorem. -/
theorem normGradient_weak (u : Reference J W) :
    SymmetricLift.HasWeakH1Local (fun x => ‖inclusion J W u x‖)
      (normGradient W u) := by
  let := InnerProductSpace.rclikeToReal ℂ PhotonFock
  have hw : SymmetricLift.HasWeakH1Local (inclusion J W u : Position J → PhotonFock)
      (fun i => (ordinary J W i u : Position J → PhotonFock)) := by
    simpa only [inclusion, ordinary, ContinuousLinearMap.comp_apply] using
      ElectronicH1Complex.weak (electronic J W u)
  have h := NormWeakH1Finite.norm_weakH1Local (Lp.memLp (inclusion J W u))
    (fun i => Lp.memLp (ordinary J W i u)) hw
  exact h

end WeakNorm

end PfHk.PhysicalLocalEnergy
