import GptLean.PhysicalPFScalarMultiplier
import Mathlib.Tactic.Module

/-! Single-cutoff IMS on the actual Pauli–Fierz common form domain.
The test vector is the twice-localized physical graph vector, so no
operator-domain or antisymmetry preservation is required of the cutoff. -/

noncomputable section

namespace PfHk.PhysicalLocalEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply


section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Hilbert-space identity behind a single real cutoff. -/
theorem re_inner_self (u : H) : (⟪u, u⟫_ℂ).re = ‖u‖ ^ 2 :=
  (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm

theorem singleCutoff_identity (A : H →L[ℂ] H)
    (hA : ∀ u v, ⟪u, A v⟫_ℂ = ⟪A u, v⟫_ℂ) (d b : H) :
    ‖A d + b‖ ^ 2 = (⟪A (A d + b + b), d⟫_ℂ).re + ‖b‖ ^ 2 := by
  rw [← hA, inner_add_left, inner_add_left]
  rw [norm_add_sq (𝕜 := ℂ)]
  have hc : (⟪b, A d⟫_ℂ).re = (⟪A d, b⟫_ℂ).re := by
    simpa only [Complex.conj_re] using congrArg Complex.re (inner_conj_symm (A d) b)
  simp only [Complex.add_re, re_inner_self]
  change ‖A d‖ ^ 2 + 2 * (⟪A d, b⟫_ℂ).re + ‖b‖ ^ 2 =
    ‖A d‖ ^ 2 + (⟪b, A d⟫_ℂ).re + (⟪b, A d⟫_ℂ).re + ‖b‖ ^ 2
  rw [hc]
  ring

theorem singleCutoff_of_product (A : H →L[ℂ] H)
    (hA : ∀ u v, ⟪u, A v⟫_ℂ = ⟪A u, v⟫_ℂ) (d d₁ d₂ b : H)
    (h₁ : d₁ = A d + b) (h₂ : d₂ = A (d₁ + b)) :
    ‖d₁‖ ^ 2 = (⟪d₂, d⟫_ℂ).re + ‖b‖ ^ 2 := by
  rw [h₂, h₁]
  exact singleCutoff_identity A hA d b

theorem norm_negI_smul (b : H) : ‖(-Complex.I) • b‖ = ‖b‖ := by
  simp only [norm_smul, norm_neg, Complex.norm_I, one_mul]

end Hilbert


variable {I : Type} [Fintype I] [DecidableEq I]

/-- Real multiplication and multiplication by its real derivative commute. -/
theorem multiplier_derivative_commute (a : DifferentiableMultiplier I)
    (i : I) (u : WaveSpace I) :
    a.derivativeMultiplier i (a.multiplier u) =
      a.multiplier (a.derivativeMultiplier i u) := by
  apply Lp.ext
  filter_upwards [
    PhotonLocalization.realL2Multiplier_apply (a.gradient i)
      (a.gradient_measurable i).aestronglyMeasurable a.derivativeBound
      (ae_of_all _ (a.derivative_bounded i)) (a.multiplier u),
    PhotonLocalization.realL2Multiplier_apply a.weight
      a.differentiable.continuous.aestronglyMeasurable a.bound
      (ae_of_all _ a.bounded) u,
    PhotonLocalization.realL2Multiplier_apply a.weight
      a.differentiable.continuous.aestronglyMeasurable a.bound
      (ae_of_all _ a.bounded) (a.derivativeMultiplier i u),
    PhotonLocalization.realL2Multiplier_apply (a.gradient i)
      (a.gradient_measurable i).aestronglyMeasurable a.derivativeBound
      (ae_of_all _ (a.derivative_bounded i)) u] with x h₁ h₂ h₃ h₄
  change a.derivativeMultiplier i (a.multiplier u) x =
    a.multiplier (a.derivativeMultiplier i u) x
  calc
    _ = a.gradient i x • a.multiplier u x := h₁
    _ = a.gradient i x • (a.weight x • u x) := congrArg (fun z : PhotonFock => a.gradient i x • z) h₂
    _ = a.weight x • (a.gradient i x • u x) := smul_comm _ _ _
    _ = a.weight x • a.derivativeMultiplier i u x :=
      congrArg (fun z : PhotonFock => a.weight x • z) h₄.symm
    _ = _ := h₃.symm

attribute [local irreducible] DifferentiableMultiplier.multiplier
  DifferentiableMultiplier.derivativeMultiplier

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)


/-- The sesquilinear positive PF form on its constructed common graph. -/
def form (u v : Reference I V) : ℂ :=
  (1 / 2 : ℂ) * ∑ i, ⟪covariant I V C κ hκ M hbound e i u,
    covariant I V C κ hκ M hbound e i v⟫_ℂ +
  ⟪radiation I V u, radiation I V v⟫_ℂ +
  ⟪potential I V u, potential I V v⟫_ℂ

theorem form_diagonal (u : Reference I V) :
    (form V C κ hκ M hbound e u u).re = energy I V C κ hκ M hbound e u := by
  simp only [form, energy, kineticEnergy, Complex.add_re, Complex.mul_re,
    Complex.div_re, Complex.div_im, Complex.one_re, Complex.one_im,
    Complex.re_sum, Complex.im_sum,
    re_inner_self (H := WaveSpace I), inner_self_im]
  norm_num

theorem covariant_singleCutoff (a : DifferentiableMultiplier I)
    (u : Reference I V) (i : I) :
    ‖covariant I V C κ hκ M hbound e i
      (PhysicalPFScalarMultiplier.multiply V a u)‖ ^ 2 =
    (⟪covariant I V C κ hκ M hbound e i
      (PhysicalPFScalarMultiplier.multiply V a
        (PhysicalPFScalarMultiplier.multiply V a u)),
      covariant I V C κ hκ M hbound e i u⟫_ℂ).re +
      ‖a.derivativeMultiplier i (inclusion I V u)‖ ^ 2 := by
  have h₁ := PhysicalPFScalarMultiplier.covariant_multiply V a C κ hκ M hbound e u i
  have h₂ := PhysicalPFScalarMultiplier.covariant_multiply V a C κ hκ M hbound e
    (PhysicalPFScalarMultiplier.multiply V a u) i
  have hv := PhysicalPFScalarMultiplier.value_multiply V a u
  have hc := multiplier_derivative_commute a i (inclusion I V u)
  let L : WaveSpace I →L[ℂ] WaveSpace I := a.multiplier
  let B : WaveSpace I →L[ℂ] WaveSpace I := a.derivativeMultiplier i
  let d₁ := covariant I V C κ hκ M hbound e i (PhysicalPFScalarMultiplier.multiply V a u)
  let b := (-Complex.I) • B (inclusion I V u)
  have hprod : covariant I V C κ hκ M hbound e i
      (PhysicalPFScalarMultiplier.multiply V a (PhysicalPFScalarMultiplier.multiply V a u)) =
      L (d₁ + b) :=
    h₂.trans ((congrArg (fun z : WaveSpace I => L d₁ + (-Complex.I) • B z) hv).trans
      ((congrArg (fun z : WaveSpace I => L d₁ + (-Complex.I) • z) hc).trans
        ((congrArg (fun z : WaveSpace I => L d₁ + z)
          (L.map_smul (-Complex.I) (B (inclusion I V u))).symm).trans
            (L.map_add d₁ b).symm)))
  have h := singleCutoff_of_product (H := WaveSpace I) L
    (a.multiplier_symmetric (H := PhotonFock))
    (covariant I V C κ hκ M hbound e i u) d₁ _ b h₁ hprod
  exact h.trans (congrArg (fun r : ℝ =>
    (⟪covariant I V C κ hκ M hbound e i
      (PhysicalPFScalarMultiplier.multiply V a (PhysicalPFScalarMultiplier.multiply V a u)),
      covariant I V C κ hκ M hbound e i u⟫_ℂ).re + r ^ 2)
    (norm_negI_smul (B (inclusion I V u))))


end PfHk.PhysicalLocalEnergy
