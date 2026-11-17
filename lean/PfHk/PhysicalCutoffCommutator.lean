import PfHk.PhysicalCutoffCommutatorForm
import PfHk.L2ScalarNorm

/-! Local operator graphs defined by the actual PF weak form. Scalar cutoff localization computes the graph image explicitly. -/

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

local instance graphPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
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

/-- Membership in the operator graph realized by the full PF weak form. -/
def IsOperatorPair (u : Reference I V) (hu : ExternalDomain V A positive negative u)
    (f : WaveSpace I) : Prop :=
  ∀ v : Reference I V, ∀ hv : ExternalDomain V A positive negative v,
    externalForm V C κ hκ M hbound e A positive negative v u hv hu =
      ⟪inclusion I V v, f⟫_ℂ

/-- Scalar cutoff localization preserves the form-realized operator domain
and computes its output. -/
theorem operatorPair_localize (a : TwiceDifferentiableMultiplier I)
    {u : Reference I V} {hu : ExternalDomain V A positive negative u} {f : WaveSpace I}
    (hf : IsOperatorPair V C κ hκ M hbound e A positive negative u hu f) :
    IsOperatorPair V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a.scalar u) (hu.localize V a.scalar)
      (a.scalar.multiplier (H := PhotonFock) f + commutator V C κ hκ M hbound e A positive negative a u hu) := by
  intro v hv
  have htest := hf (PhysicalPFScalarMultiplier.multiply V a.scalar v) (hv.localize V a.scalar)
  have hpair : ⟪inclusion I V (PhysicalPFScalarMultiplier.multiply V a.scalar v), f⟫_ℂ =
      ⟪inclusion I V v, a.scalar.multiplier (H := PhotonFock) f⟫_ℂ :=
    (congrArg (fun z : WaveSpace I => ⟪z, f⟫_ℂ)
      (PhysicalPFScalarMultiplier.value_multiply V a.scalar v)).trans
      (a.scalar.multiplier_symmetric (H := PhotonFock) (inclusion I V v) f).symm
  exact (form_commutator V C κ hκ M hbound e A positive negative a u v hu hv).trans
    ((congrArg (fun z : ℂ => z +
      ⟪inclusion I V v, commutator V C κ hκ M hbound e A positive negative a u hu⟫_ℂ)
      (htest.trans hpair)).trans (inner_add_right _ _ _).symm)

/-- In particular a weak eigenstate has the explicit localized operator
image `E ηψ + [H,η]ψ`. -/
theorem eigenstate_operatorPair_localize (a : TwiceDifferentiableMultiplier I)
    {u : Reference I V} {hu : ExternalDomain V A positive negative u} {E : ℝ}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu) :
    IsOperatorPair V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a.scalar u) (hu.localize V a.scalar)
      ((E : ℂ) • a.scalar.multiplier (H := PhotonFock) (inclusion I V u) +
        commutator V C κ hκ M hbound e A positive negative a u hu) := by
  have hop : IsOperatorPair V C κ hκ M hbound e A positive negative u hu
      ((E : ℂ) • inclusion I V u) := by
    intro v hv
    exact (heigen v hv).trans (inner_smul_right _ _ _).symm
  simpa only [map_smul] using operatorPair_localize V C κ hκ M hbound e A positive negative a hop

/-- The weak equation on a region, tested only against form vectors supported
there. The state itself need not belong to the global operator domain. -/
def IsLocalOperatorPair (s : Set (Position I)) (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) (f : WaveSpace I) : Prop :=
  ∀ v : Reference I V, ∀ hv : ExternalDomain V A positive negative v,
    (∀ᵐ x ∂volume, x ∉ s → inclusion I V v x = 0) →
      externalForm V C κ hκ M hbound e A positive negative v u hv hu =
        ⟪inclusion I V v, f⟫_ℂ

theorem localized_supported (a : DifferentiableMultiplier I)
    {s : Set (Position I)} (hsupp : ∀ x, x ∉ s → a.weight x = 0)
    (v : Reference I V) :
    ∀ᵐ x ∂volume, x ∉ s →
      inclusion I V (PhysicalPFScalarMultiplier.multiply V a v) x = 0 := by
  filter_upwards [scalar_multiplier_supported (H := PhotonFock) a (inclusion I V v) hsupp] with x hx
  intro hxs
  have hv := congrArg (fun z : WaveSpace I => z x) (PhysicalPFScalarMultiplier.value_multiply V a v)
  exact hv.trans (hx hxs)

/-- A cutoff supported inside the weak-equation region belongs to the global
form-realized operator graph, with the explicit commutator output. -/
theorem local_operatorPair_localize (a : TwiceDifferentiableMultiplier I)
    {s : Set (Position I)} (hsupp : ∀ x, x ∉ s → a.scalar.weight x = 0)
    {u : Reference I V} {hu : ExternalDomain V A positive negative u} {f : WaveSpace I}
    (hf : IsLocalOperatorPair V C κ hκ M hbound e A positive negative s u hu f) :
    IsOperatorPair V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a.scalar u) (hu.localize V a.scalar)
      (a.scalar.multiplier (H := PhotonFock) f + commutator V C κ hκ M hbound e A positive negative a u hu) := by
  intro v hv
  have htest := hf (PhysicalPFScalarMultiplier.multiply V a.scalar v) (hv.localize V a.scalar)
    (localized_supported V a.scalar hsupp v)
  have hpair : ⟪inclusion I V (PhysicalPFScalarMultiplier.multiply V a.scalar v), f⟫_ℂ =
      ⟪inclusion I V v, a.scalar.multiplier (H := PhotonFock) f⟫_ℂ :=
    (congrArg (fun z : WaveSpace I => ⟪z, f⟫_ℂ)
      (PhysicalPFScalarMultiplier.value_multiply V a.scalar v)).trans
      (a.scalar.multiplier_symmetric (H := PhotonFock) (inclusion I V v) f).symm
  exact (form_commutator V C κ hκ M hbound e A positive negative a u v hu hv).trans
    ((congrArg (fun z : ℂ => z +
      ⟪inclusion I V v, commutator V C κ hκ M hbound e A positive negative a u hu⟫_ℂ)
      (htest.trans hpair)).trans (inner_add_right _ _ _).symm)


end PfHk.PhysicalCutoffCommutator
