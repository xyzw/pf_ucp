import PfHk.PhysicalCutoffCommutatorCore
import PfHk.PhysicalCutoffCommutatorAlgebraLp

/-! The exact scalar-cutoff product identity for the full physical weak form. -/

noncomputable section
namespace PfHk.PhysicalCutoffCommutator

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier PfHk.PhysicalLocalEnergy
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply

local instance photonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

variable {I : Type} [Fintype I] [DecidableEq I]

attribute [local irreducible] roughMultiply externalCovariant
  DifferentiableMultiplier.multiplier DifferentiableMultiplier.derivativeMultiplier

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

private theorem kinetic_pair (a : TwiceDifferentiableMultiplier I) (u v : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    (hv : ExternalDomain V A positive negative v) (i : I) :
    ⟪externalCovariant V C κ hκ M hbound e A positive negative v hv i,
      externalCovariant V C κ hκ M hbound e A positive negative
        (PhysicalPFScalarMultiplier.multiply V a.scalar u) (hu.localize V a.scalar) i⟫_ℂ =
    ⟪externalCovariant V C κ hκ M hbound e A positive negative
        (PhysicalPFScalarMultiplier.multiply V a.scalar v) (hv.localize V a.scalar) i,
      externalCovariant V C κ hκ M hbound e A positive negative u hu i⟫_ℂ +
      2 * ⟪inclusion I V v, singleCutoffError (H := PhotonFock) a i (inclusion I V u)
        (externalCovariant V C κ hκ M hbound e A positive negative u hu i)⟫_ℂ := by
  exact scalar_cutoff_kinetic (H := PhotonFock) a i
    (inclusion I V u) (inclusion I V v)
    (externalCovariant V C κ hκ M hbound e A positive negative u hu i)
    (externalCovariant V C κ hκ M hbound e A positive negative v hv i)
    _ _ _ _
    (externalCovariant_localize V C κ hκ M hbound e A positive negative u hu a.scalar i)
    (externalCovariant_localize V C κ hκ M hbound e A positive negative v hv a.scalar i)
    (externalCovariant_localize V C κ hκ M hbound e A positive negative u hu (a.derivative i) i)
    (PhysicalPFScalarMultiplier.value_multiply V (a.derivative i) u)
    (externalCovariant_symmetric V C κ hκ M hbound e A positive negative v
      (PhysicalPFScalarMultiplier.multiply V (a.derivative i) u) hv (hu.localize V (a.derivative i)) i)

/-- Form version of the exact cutoff commutator, including the external
magnetic field and both signs of the scalar potential. -/
theorem form_commutator (a : TwiceDifferentiableMultiplier I) (u v : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    (hv : ExternalDomain V A positive negative v) :
    externalForm V C κ hκ M hbound e A positive negative v
      (PhysicalPFScalarMultiplier.multiply V a.scalar u) hv (hu.localize V a.scalar) =
    externalForm V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a.scalar v) u (hv.localize V a.scalar) hu +
      ⟪inclusion I V v, commutator V C κ hκ M hbound e A positive negative a u hu⟫_ℂ := by
  unfold externalForm
  have hr := scalar_multiplier_pair (H := PhotonFock) a.scalar _ _ _ _
    (PhysicalPFScalarMultiplier.radiation_multiply V a.scalar v)
    (PhysicalPFScalarMultiplier.radiation_multiply V a.scalar u)
  have hp := scalar_multiplier_pair (H := PhotonFock) a.scalar _ _ _ _
    (PhysicalPFScalarMultiplier.potential_multiply V a.scalar v)
    (PhysicalPFScalarMultiplier.potential_multiply V a.scalar u)
  have hpos := scalar_multiplier_pair (H := PhotonFock) a.scalar _ _ _ _
    (roughMultiply_reference_localize V a.scalar positive v hv.positive (hv.localize V a.scalar).positive)
    (roughMultiply_reference_localize V a.scalar positive u hu.positive (hu.localize V a.scalar).positive)
  have hneg := scalar_multiplier_pair (H := PhotonFock) a.scalar _ _ _ _
    (roughMultiply_reference_localize V a.scalar negative v hv.negative (hv.localize V a.scalar).negative)
    (roughMultiply_reference_localize V a.scalar negative u hu.negative (hu.localize V a.scalar).negative)
  have hk := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun i _ => kinetic_pair V C κ hκ M hbound e A positive negative a u v hu hv i)
  have hform := congrArg₂ (fun z w : ℂ => z - w)
    (congrArg₂ (fun z w : ℂ => z + w)
      (congrArg₂ (fun z w : ℂ => z + w)
        (congrArg₂ (fun z w : ℂ => z + w)
          (congrArg (fun z : ℂ => (1 / 2 : ℂ) * z) hk) hr) hp) hpos) hneg
  have hcomm := inner_scalarCommutator (H := PhotonFock) a (inclusion I V v) (inclusion I V u)
    (externalCovariant V C κ hκ M hbound e A positive negative u hu)
  change ⟪inclusion I V v, commutator V C κ hκ M hbound e A positive negative a u hu⟫_ℂ = _ at hcomm
  have hhalf := half_sum_form
    (fun i => ⟪externalCovariant V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a.scalar v) (hv.localize V a.scalar) i,
        externalCovariant V C κ hκ M hbound e A positive negative u hu i⟫_ℂ)
    (fun i => ⟪inclusion I V v, singleCutoffError (H := PhotonFock) a i (inclusion I V u)
      (externalCovariant V C κ hκ M hbound e A positive negative u hu i)⟫_ℂ)
    ⟪radiation I V (PhysicalPFScalarMultiplier.multiply V a.scalar v), radiation I V u⟫_ℂ
    ⟪potential I V (PhysicalPFScalarMultiplier.multiply V a.scalar v), potential I V u⟫_ℂ
    ⟪roughMultiply positive (inclusion I V (PhysicalPFScalarMultiplier.multiply V a.scalar v))
      (hv.localize V a.scalar).positive, roughMultiply positive (inclusion I V u) hu.positive⟫_ℂ
    ⟪roughMultiply negative (inclusion I V (PhysicalPFScalarMultiplier.multiply V a.scalar v))
      (hv.localize V a.scalar).negative, roughMultiply negative (inclusion I V u) hu.negative⟫_ℂ
    ⟪inclusion I V v, commutator V C κ hκ M hbound e A positive negative a u hu⟫_ℂ hcomm
  exact hform.trans hhalf

end PfHk.PhysicalCutoffCommutator
