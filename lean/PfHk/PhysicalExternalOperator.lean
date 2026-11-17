import PfHk.ExternalOperatorAlgebra
import PfHk.ExternalScalarApproximation
import PfHk.PhysicalComparisonDomain

/-! The external magnetic operator expression on the actual PF form domain.
The divergence identity is obtained by passing to the limit in smooth scalar
product rules. The approximation assumptions concern ordinary scalar
multiplication in L², and contain no operator or Carleman identity. -/

noncomputable section
namespace PfHk.PhysicalExternalOperator

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier PfHk.PhysicalLocalEnergy
open PfHk.PhysicalCutoffCommutator
open scoped InnerProductSpace Topology

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
set_option Elab.async false

local instance externalPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  PfHk.PhysicalOperatorDomain.comparisonPhotonDirectInner

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply roughMultiply HasMultiplier
  PhysicalPFReference.referenceSubspace
  DifferentiableMultiplier.multiplier DifferentiableMultiplier.derivativeMultiplier

variable {I : Type} [Fintype I] [DecidableEq I]

theorem multiplier_symmetric_wave (a : DifferentiableMultiplier I) (u v : WaveSpace I) :
    ⟪u, a.multiplier v⟫_ℂ = ⟪a.multiplier u, v⟫_ℂ :=
  a.multiplier_symmetric (H := PhotonFock) (I := I) u v

def sourceSum (f g : WaveSpace I) : WaveSpace I := f + g

attribute [local irreducible] sourceSum

omit [DecidableEq I] in
theorem sourceSum_inner (v f g : WaveSpace I) :
    ⟪v, sourceSum f g⟫_ℂ = ⟪v, f⟫_ℂ + ⟪v, g⟫_ℂ := by
  unfold sourceSum
  exact inner_add_right v f g

theorem roughMultiply_square_pair (a : Position I → ℝ) (u v : WaveSpace I)
    (hu : HasMultiplier a u) (hv : HasMultiplier a v)
    (hs : HasMultiplier (fun x => a x ^ 2) u) :
    ⟪roughMultiply a v hv, roughMultiply a u hu⟫_ℂ =
      ⟪v, roughMultiply (fun x => a x ^ 2) u hs⟫_ℂ := by
  exact ExternalScalarApproximation.square_pair (H := PhotonFock) a u v
    (roughMultiply a u hu) (roughMultiply a v hv) (roughMultiply (fun x => a x ^ 2) u hs)
    (roughMultiply_ae a u hu) (roughMultiply_ae a v hv)
    (roughMultiply_ae (fun x => a x ^ 2) u hs)

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i : I, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i : I, ∀ᵐ x : Position I ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

set_option maxHeartbeats 60000 in
theorem smooth_covariant_divergence_pair (a : I → DifferentiableMultiplier I)
    (u v : Reference I V) :
    (∑ i, ⟪covariant I V C κ hκ M hbound e i v,
      (a i).multiplier (inclusion I V u)⟫_ℂ) =
    (∑ i, ⟪(a i).multiplier (inclusion I V v),
      covariant I V C κ hκ M hbound e i u⟫_ℂ) -
      Complex.I * ⟪inclusion I V v,
        ∑ i, (a i).derivativeMultiplier i (inclusion I V u)⟫_ℂ := by
  have hi (i : I) : ⟪covariant I V C κ hκ M hbound e i v,
        (a i).multiplier (inclusion I V u)⟫_ℂ =
      ⟪(a i).multiplier (inclusion I V v),
        covariant I V C κ hκ M hbound e i u⟫_ℂ -
      Complex.I * ⟪inclusion I V v,
        (a i).derivativeMultiplier i (inclusion I V u)⟫_ℂ := by
    exact ExternalScalarApproximation.covariant_pair (H := WaveSpace I)
      (inclusion I V v) (covariant I V C κ hκ M hbound e i u)
      (covariant I V C κ hκ M hbound e i v)
      ((a i).multiplier (inclusion I V u)) ((a i).multiplier (inclusion I V v))
      ((a i).multiplier (covariant I V C κ hκ M hbound e i u))
      (covariant I V C κ hκ M hbound e i (PhysicalPFScalarMultiplier.multiply V (a i) u))
      ((a i).derivativeMultiplier i (inclusion I V u))
      ((covariant_symmetric I V C κ hκ M hbound e i v
        (PhysicalPFScalarMultiplier.multiply V (a i) u)).trans
          (congrArg (fun z : WaveSpace I => ⟪covariant I V C κ hκ M hbound e i v, z⟫_ℂ)
            (PhysicalPFScalarMultiplier.value_multiply V (a i) u)))
      (PhysicalPFScalarMultiplier.covariant_multiply V (a i) C κ hκ M hbound e u i)
      (multiplier_symmetric_wave (a i)
        (inclusion I V v) (covariant I V C κ hκ M hbound e i u))
  exact ExternalScalarApproximation.sum_covariant_pair (H := WaveSpace I) (I := I)
    (inclusion I V v) (fun i => covariant I V C κ hκ M hbound e i u)
    (fun i => covariant I V C κ hκ M hbound e i v)
    (fun i => (a i).multiplier (H := PhotonFock) (inclusion I V u))
    (fun i => (a i).multiplier (H := PhotonFock) (inclusion I V v))
    (fun i => (a i).derivativeMultiplier (H := PhotonFock) i (inclusion I V u)) hi

/-- Smooth coefficient approximation in the scalar multiplication topologies
needed for the divergence product rule. Only the values of the vectors enter
these assumptions, never their PF derivatives. -/
abbrev DivergenceApproximation (_A : I → Position I → ℝ) (_divA : Position I → ℝ)
    (u v : Reference I V) (au av : I → WaveSpace I) (divu : WaveSpace I) :=
  ExternalScalarApproximation.Data (H := PhotonFock) (I := I)
    (inclusion I V u) (inclusion I V v) au av divu

theorem covariant_divergence_pair (A : I → Position I → ℝ) (divA : Position I → ℝ)
    (u v : Reference I V) (au av : I → WaveSpace I) (divu : WaveSpace I)
    (h : DivergenceApproximation V A divA u v au av divu) :
    (∑ i, ⟪covariant I V C κ hκ M hbound e i v, au i⟫_ℂ) =
      (∑ i, ⟪av i, covariant I V C κ hκ M hbound e i u⟫_ℂ) -
      Complex.I * ⟪inclusion I V v, divu⟫_ℂ := by
  exact ExternalOperatorAlgebra.divergence_pair_limit (H := WaveSpace I) (I := I)
    (inclusion I V v) divu
    (fun i => covariant I V C κ hκ M hbound e i u)
    (fun i => covariant I V C κ hκ M hbound e i v) au av
    (fun n i => (h.coefficient n i).multiplier (inclusion I V u))
    (fun n i => (h.coefficient n i).multiplier (inclusion I V v))
    (fun n => ∑ i, (h.coefficient n i).derivativeMultiplier i (inclusion I V u))
    h.value_u h.value_v h.divergence_u
    (fun n => smooth_covariant_divergence_pair V C κ hκ M hbound e (h.coefficient n) u v)

variable (A : I → Position I → ℝ) (positive negative divA : Position I → ℝ)

/-- Membership of each term of the actual first-order operator expression in L². -/
structure OperatorMultipliers (u : Reference I V) : Prop where
  domain : ExternalDomain V A positive negative u
  vectorFirst : ∀ i, HasMultiplier (A i) (covariant I V C κ hκ M hbound e i u)
  vectorSquare : ∀ i, HasMultiplier (fun x => A i x ^ 2) (inclusion I V u)
  divergence : HasMultiplier divA (inclusion I V u)
  positiveSquare : HasMultiplier (fun x => positive x ^ 2) (inclusion I V u)
  negativeSquare : HasMultiplier (fun x => negative x ^ 2) (inclusion I V u)

def perturbation (u : Reference I V)
    (hu : OperatorMultipliers V C κ hκ M hbound e A positive negative divA u) : WaveSpace I :=
  (∑ i, roughMultiply (A i) (covariant I V C κ hκ M hbound e i u) (hu.vectorFirst i)) +
  (1 / 2 : ℂ) • (∑ i, roughMultiply (fun x => A i x ^ 2) (inclusion I V u)
    (hu.vectorSquare i)) +
  (-Complex.I / 2) • roughMultiply divA (inclusion I V u) hu.divergence +
  roughMultiply (fun x => positive x ^ 2) (inclusion I V u) hu.positiveSquare -
  roughMultiply (fun x => negative x ^ 2) (inclusion I V u) hu.negativeSquare

attribute [local irreducible] perturbation

theorem externalForm_expansion (u v : Reference I V)
    (hu : OperatorMultipliers V C κ hκ M hbound e A positive negative divA u)
    (hv : ExternalDomain V A positive negative v)
    (happrox : DivergenceApproximation V A divA u v
      (fun i => roughMultiply (A i) (inclusion I V u) (hu.domain.vector i))
      (fun i => roughMultiply (A i) (inclusion I V v) (hv.vector i))
      (roughMultiply divA (inclusion I V u) hu.divergence)) :
    externalForm V C κ hκ M hbound e A positive negative v u hv hu.domain =
      PhysicalLocalEnergy.form V C κ hκ M hbound e v u +
        ⟪inclusion I V v, perturbation V C κ hκ M hbound e A positive negative divA u hu⟫_ℂ := by
  have hc := covariant_divergence_pair V C κ hκ M hbound e A divA u v _ _ _ happrox
  have h := ExternalOperatorAlgebra.magnetic_form_expansion (H := WaveSpace I) (I := I)
    (inclusion I V v)
    (roughMultiply divA (inclusion I V u) hu.divergence)
    (roughMultiply (fun x => positive x ^ 2) (inclusion I V u) hu.positiveSquare)
    (roughMultiply (fun x => negative x ^ 2) (inclusion I V u) hu.negativeSquare)
    (fun i => covariant I V C κ hκ M hbound e i u)
    (fun i => covariant I V C κ hκ M hbound e i v)
    (fun i => roughMultiply (A i) (inclusion I V u) (hu.domain.vector i))
    (fun i => roughMultiply (A i) (inclusion I V v) (hv.vector i))
    (fun i => roughMultiply (A i) (covariant I V C κ hκ M hbound e i u) (hu.vectorFirst i))
    (fun i => roughMultiply (fun x => A i x ^ 2) (inclusion I V u) (hu.vectorSquare i))
    (⟪radiation I V v, radiation I V u⟫_ℂ + ⟪potential I V v, potential I V u⟫_ℂ)
    _ _ hc
    (fun i => (roughMultiply_symmetric (A i) (inclusion I V v)
      (covariant I V C κ hκ M hbound e i u) (hv.vector i) (hu.vectorFirst i)).symm)
    (fun i => roughMultiply_square_pair (A i) (inclusion I V u) (inclusion I V v)
      (hu.domain.vector i) (hv.vector i) (hu.vectorSquare i))
    (roughMultiply_square_pair positive (inclusion I V u) (inclusion I V v)
      hu.domain.positive hv.positive hu.positiveSquare)
    (roughMultiply_square_pair negative (inclusion I V u) (inclusion I V v)
      hu.domain.negative hv.negative hu.negativeSquare)
  simpa only [externalForm, externalCovariant, PhysicalLocalEnergy.form,
    perturbation, add_assoc] using h

attribute [local irreducible] IsOperatorPair

theorem operatorPair_add_perturbation (u : Reference I V) (f : WaveSpace I)
    (hu : OperatorMultipliers V C κ hκ M hbound e A positive negative divA u)
    (hfree : ∀ v, PhysicalLocalEnergy.form V C κ hκ M hbound e v u =
      ⟪inclusion I V v, f⟫_ℂ)
    (happrox : ∀ v (hv : ExternalDomain V A positive negative v),
      DivergenceApproximation V A divA u v
        (fun i => roughMultiply (A i) (inclusion I V u) (hu.domain.vector i))
        (fun i => roughMultiply (A i) (inclusion I V v) (hv.vector i))
        (roughMultiply divA (inclusion I V u) hu.divergence)) :
    IsOperatorPair V C κ hκ M hbound e A positive negative u hu.domain
      (sourceSum f (perturbation V C κ hκ M hbound e A positive negative divA u hu)) := by
  unfold IsOperatorPair
  intro v hv
  let r := perturbation V C κ hκ M hbound e A positive negative divA u hu
  exact (externalForm_expansion V C κ hκ M hbound e A positive negative divA u v hu hv
    (happrox v hv)).trans
      ((congrArg (fun z : ℂ => z + ⟪inclusion I V v, r⟫_ℂ) (hfree v)).trans
        (sourceSum_inner (inclusion I V v) f r).symm)

end PfHk.PhysicalExternalOperator
