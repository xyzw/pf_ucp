import PfHk.PhysicalExternalDomain
import PfHk.ScalarMultiplicationLinear
import Mathlib.LinearAlgebra.BilinearMap

/-! The actual external form is a Hermitian sesquilinear form on the
common reference domain once its multiplier memberships are derived.
This supplies the linear form object used by finite permutation reduction
and by the variational eigenvalue argument. -/

noncomputable section
namespace PfHk.PhysicalExternalFormLinear

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PhysicalLocalEnergy
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

local instance externalFormPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

attribute [local irreducible] inclusion covariant radiation potential roughMultiply
  PhysicalPFReference.referenceSubspace

variable {I : Type} [Fintype I] [DecidableEq I]
  (V : Position I → ℝ)

local instance externalFormWaveDirectInner : InnerProductSpace ℂ (WaveSpace I) :=
  { (inferInstance : InnerProductSpace ℂ (WaveSpace I)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (WaveSpace I)) }

def roughLinear (f : Position I → ℝ)
    (hf : ∀ u : Reference I V, HasMultiplier f (inclusion I V u)) :
    Reference I V →ₗ[ℂ] WaveSpace I :=
  ScalarMultiplicationLinear.multiplierOfValues (H := PhotonFock) (Q := Reference I V)
    volume (fun x => (f x : ℂ)) (inclusion I V).toLinearMap
    (fun u => roughMultiply f (inclusion I V u) (hf u)) (fun u => by
      filter_upwards [roughMultiply_ae f (inclusion I V u) (hf u)] with x hx
      exact hx.trans (Complex.coe_smul (f x) (inclusion I V u x)).symm)

theorem roughLinear_apply (f : Position I → ℝ)
    (hf : ∀ u : Reference I V, HasMultiplier f (inclusion I V u)) (u : Reference I V)
    (h : HasMultiplier f (inclusion I V u)) :
    roughLinear V f hf u = roughMultiply f (inclusion I V u) h := rfl

section Algebra

variable {Q H : Type*} [AddCommGroup Q] [Module ℂ Q]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def innerForm (L : Q →ₗ[ℂ] H) : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ :=
  ((innerₛₗ ℂ).compl₂ L).comp L

@[simp] theorem innerForm_apply (L : Q →ₗ[ℂ] H) (u v : Q) :
    innerForm L u v = ⟪L u, L v⟫_ℂ := rfl

end Algebra

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)
  (D : ∀ u : Reference I V, ExternalDomain V A positive negative u)

def covariantLinear (i : I) : Reference I V →ₗ[ℂ] WaveSpace I :=
  (covariant I V C κ hκ M hbound e i).toLinearMap +
    roughLinear V (A i) (fun u => (D u).vector i)

theorem covariantLinear_apply (i : I) (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) :
    covariantLinear V C κ hκ M hbound e A positive negative D i u =
      externalCovariant V C κ hκ M hbound e A positive negative u hu i := by
  exact congrArg (covariant I V C κ hκ M hbound e i u + ·)
    (roughLinear_apply V (A i) (fun w => (D w).vector i) u (hu.vector i))

def form : Reference I V →ₗ⋆[ℂ] Reference I V →ₗ[ℂ] ℂ :=
  (1 / 2 : ℂ) • ∑ i, innerForm (Q := Reference I V) (H := WaveSpace I) (covariantLinear V C κ hκ M hbound e A positive negative D i) +
    innerForm (Q := Reference I V) (H := WaveSpace I) (radiation I V).toLinearMap + innerForm (Q := Reference I V) (H := WaveSpace I) (potential I V).toLinearMap +
    innerForm (Q := Reference I V) (H := WaveSpace I) (roughLinear V positive (fun u => (D u).positive)) -
    innerForm (Q := Reference I V) (H := WaveSpace I) (roughLinear V negative (fun u => (D u).negative))

set_option maxHeartbeats 200000 in
theorem form_apply (u v : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    (hv : ExternalDomain V A positive negative v) :
    form V C κ hκ M hbound e A positive negative D u v =
      externalForm V C κ hκ M hbound e A positive negative u v hu hv := by
  have hc (i : I) := congrArg₂ (fun a b : WaveSpace I => ⟪a, b⟫_ℂ)
    (covariantLinear_apply V C κ hκ M hbound e A positive negative D i u hu)
    (covariantLinear_apply V C κ hκ M hbound e A positive negative D i v hv)
  have hp := congrArg₂ (fun a b : WaveSpace I => ⟪a, b⟫_ℂ)
    (roughLinear_apply V positive (fun w => (D w).positive) u hu.positive)
    (roughLinear_apply V positive (fun w => (D w).positive) v hv.positive)
  have hn := congrArg₂ (fun a b : WaveSpace I => ⟪a, b⟫_ℂ)
    (roughLinear_apply V negative (fun w => (D w).negative) u hu.negative)
    (roughLinear_apply V negative (fun w => (D w).negative) v hv.negative)
  simp only [form, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, innerForm_apply, smul_eq_mul, hc, hp, hn,
    externalForm, ContinuousLinearMap.coe_coe]

attribute [local irreducible] form

set_option maxHeartbeats 200000 in
theorem form_hermitian (u v : Reference I V) :
    star (form V C κ hκ M hbound e A positive negative D u v) =
      form V C κ hκ M hbound e A positive negative D v u := by
  exact (congrArg (star : ℂ → ℂ)
    (form_apply V C κ hκ M hbound e A positive negative D u v (D u) (D v))).trans
      ((PhysicalExternalOperator.externalForm_conj V C κ hκ M hbound e A positive negative
        u v (D u) (D v)).trans
          (form_apply V C κ hκ M hbound e A positive negative D v u (D v) (D u)).symm)

end PfHk.PhysicalExternalFormLinear
