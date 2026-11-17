import PfHk.PhysicalLocalEnergyRoughCutoff

noncomputable section
namespace PfHk.PhysicalLocalEnergy
open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false
attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply roughMultiply
  DifferentiableMultiplier.multiplier DifferentiableMultiplier.derivativeMultiplier
  externalCovariant externalForm externalEnergy
variable {I : Type} [Fintype I] [DecidableEq I]

private theorem half_sum_algebra (k z r p vplus vminus : ℝ) :
    (1 / 2 : ℝ) * (k + z) + r + p + vplus - vminus =
      ((1 / 2 : ℝ) * k + r + p + vplus - vminus) + (1 / 2 : ℝ) * z := by ring

private theorem real_mul_inner_self {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (E : ℝ) (u : H) :
    ((E : ℂ) * ⟪u, u⟫_ℂ).re = E * ‖u‖ ^ 2 := by
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, re_inner_self]

private theorem form_real_sum (k : I → ℂ) (r p vplus vminus : ℂ) :
    ((1 / 2 : ℂ) * (∑ i, k i) + r + p + vplus - vminus).re =
      (1 / 2 : ℝ) * (∑ i, (k i).re) + r.re + p.re + vplus.re - vminus.re := by
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.one_re, Complex.one_im, Complex.re_sum,
    zero_div, zero_mul, sub_zero]

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

/-- Full rough-field IMS. Both external scalar signs and the external
magnetic derivative are present in the constructed physical form. -/
theorem external_ims (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) (a : DifferentiableMultiplier I) :
    externalEnergy V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a u) (hu.localize V a) =
    (externalForm V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a (PhysicalPFScalarMultiplier.multiply V a u))
      u ((hu.localize V a).localize V a) hu).re +
      (1 / 2 : ℝ) * ∑ i, ‖a.derivativeMultiplier i (inclusion I V u)‖ ^ 2 := by
  have hk := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun i _ => externalCovariant_singleCutoff V C κ hκ M hbound e A positive negative u hu a i)
  have hr := radiation_singleCutoff V a u
  have hp := potential_singleCutoff V a u
  have hpos := roughMultiply_singleCutoff V a positive u hu.positive
    (hu.localize V a).positive ((hu.localize V a).localize V a).positive
  have hneg := roughMultiply_singleCutoff V a negative u hu.negative
    (hu.localize V a).negative ((hu.localize V a).localize V a).negative
  let u₁ := PhysicalPFScalarMultiplier.multiply V a u
  let u₂ := PhysicalPFScalarMultiplier.multiply V a u₁
  let kin : I → ℂ := fun i => ⟪externalCovariant V C κ hκ M hbound e A positive negative
      u₂ ((hu.localize V a).localize V a) i,
    externalCovariant V C κ hκ M hbound e A positive negative u hu i⟫_ℂ
  let z := ∑ i, ‖a.derivativeMultiplier i (inclusion I V u)‖ ^ 2
  let rad := ⟪radiation I V u₂, radiation I V u⟫_ℂ
  let pot := ⟪potential I V u₂, potential I V u⟫_ℂ
  let pos := ⟪roughMultiply positive (inclusion I V u₂) ((hu.localize V a).localize V a).positive,
    roughMultiply positive (inclusion I V u) hu.positive⟫_ℂ
  let neg := ⟪roughMultiply negative (inclusion I V u₂) ((hu.localize V a).localize V a).negative,
    roughMultiply negative (inclusion I V u) hu.negative⟫_ℂ
  have hk' : (∑ i, ‖externalCovariant V C κ hκ M hbound e A positive negative
      u₁ (hu.localize V a) i‖ ^ 2) = (∑ i, (kin i).re) + z :=
    hk.trans Finset.sum_add_distrib
  have he : externalEnergy V C κ hκ M hbound e A positive negative u₁ (hu.localize V a) =
      (1 / 2 : ℝ) * ((∑ i, (kin i).re) + z) + rad.re + pot.re + pos.re - neg.re := by
    unfold externalEnergy
    exact congrArg₂ (· - ·) (congrArg₂ (· + ·)
      (congrArg₂ (· + ·) (congrArg₂ (· + ·)
        (congrArg (fun q : ℝ => (1 / 2 : ℝ) * q) hk') hr) hp) hpos) hneg
  have hf : (externalForm V C κ hκ M hbound e A positive negative
      u₂ u ((hu.localize V a).localize V a) hu).re =
      (1 / 2 : ℝ) * (∑ i, (kin i).re) + rad.re + pot.re + pos.re - neg.re := by
    unfold externalForm
    exact form_real_sum kin rad pot pos neg
  exact he.trans ((half_sum_algebra _ z rad.re pot.re pos.re neg.re).trans
    (congrArg (fun q : ℝ => q + (1 / 2 : ℝ) * z) hf.symm))

theorem external_eigenstate_ims {E : ℝ} {u : Reference I V}
    {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (a : DifferentiableMultiplier I) :
    externalEnergy V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a u) (hu.localize V a) =
      E * ‖a.multiplier (inclusion I V u)‖ ^ 2 +
      (1 / 2 : ℝ) * ∑ i, ‖a.derivativeMultiplier i (inclusion I V u)‖ ^ 2 := by
  let ψ := inclusion I V u
  let u₁ := PhysicalPFScalarMultiplier.multiply V a u
  let u₂ := PhysicalPFScalarMultiplier.multiply V a u₁
  let L : WaveSpace I →L[ℂ] WaveSpace I := a.multiplier
  have hv₁ : inclusion I V u₁ = L ψ := PhysicalPFScalarMultiplier.value_multiply V a u
  have hv₂ : inclusion I V u₂ = L (L ψ) :=
    (PhysicalPFScalarMultiplier.value_multiply V a u₁).trans (congrArg L hv₁)
  have hs : ⟪inclusion I V u₂, ψ⟫_ℂ = ⟪L ψ, L ψ⟫_ℂ :=
    (congrArg (fun z : WaveSpace I => ⟪z, ψ⟫_ℂ) hv₂).trans
      (a.multiplier_symmetric (H := PhotonFock) (L ψ) ψ).symm
  have hform := heigen u₂ ((hu.localize V a).localize V a)
  have hre :
      (externalForm V C κ hκ M hbound e A positive negative u₂ u
        ((hu.localize V a).localize V a) hu).re = E * ‖L ψ‖ ^ 2 :=
    (congrArg Complex.re hform).trans
      ((congrArg (fun z : ℂ => ((E : ℂ) * z).re) hs).trans
        (real_mul_inner_self E (L ψ)))
  exact (external_ims V C κ hκ M hbound e A positive negative u hu a).trans
    (congrArg (fun q : ℝ => q + (1 / 2 : ℝ) *
      ∑ i, ‖a.derivativeMultiplier i (inclusion I V u)‖ ^ 2) hre)

end PfHk.PhysicalLocalEnergy
