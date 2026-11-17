import PfHk.PhysicalCutoffCommutator

/-! The same form-realized graph with zero external perturbations. This
exposes the free form for polar calculations without defining another operator. -/

noncomputable section
namespace PfHk.PhysicalCutoffCommutator

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalLocalEnergy
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential roughMultiply

variable {I : Type} [Fintype I] [DecidableEq I]

theorem zeroExternalDomain (V : Position I → ℝ) (u : Reference I V) :
    ExternalDomain V (fun _ _ => 0) (fun _ => 0) (fun _ => 0) u := by
  have hzero : HasMultiplier (fun _ => 0) (inclusion I V u) := by
    simpa only [HasMultiplier, zero_smul] using
      (MemLp.zero' : MemLp (fun _ : Position I => (0 : PhotonFock)) 2 volume)
  exact ⟨fun _ => hzero, hzero, hzero⟩

theorem roughMultiply_zero (u : WaveSpace I) (hu : HasMultiplier (fun _ => 0) u) :
    roughMultiply (fun _ => 0) u hu = 0 := by
  apply Lp.ext
  have h : roughMultiply (fun _ => 0) u hu =ᵐ[volume] (fun _ => (0 : PhotonFock)) := by
    simpa only [zero_smul] using roughMultiply_ae (fun _ => 0) u hu
  exact h.trans (Lp.coeFn_zero PhotonFock 2 (volume : Measure (Position I))).symm

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

theorem externalForm_zero (u v : Reference I V)
    (hu : ExternalDomain V (fun _ _ => 0) (fun _ => 0) (fun _ => 0) u)
    (hv : ExternalDomain V (fun _ _ => 0) (fun _ => 0) (fun _ => 0) v) :
    externalForm V C κ hκ M hbound e (fun _ _ => 0) (fun _ => 0) (fun _ => 0) u v hu hv =
      PhysicalLocalEnergy.form V C κ hκ M hbound e u v := by
  simp only [externalForm, externalCovariant, roughMultiply_zero, add_zero,
    inner_zero_left, sub_zero, PhysicalLocalEnergy.form]

/-- At `V = 0` this is the free PF graph used in the cylinder transport.
All tests are actual reference vectors, and no zero-domain witnesses remain
in the right side of the equivalence. -/
theorem isOperatorPair_zero_iff (u : Reference I V) (f : WaveSpace I) :
    IsOperatorPair V C κ hκ M hbound e (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
      u (zeroExternalDomain V u) f ↔
      ∀ v : Reference I V,
        PhysicalLocalEnergy.form V C κ hκ M hbound e v u = ⟪inclusion I V v, f⟫_ℂ := by
  constructor
  · intro h v
    exact (externalForm_zero V C κ hκ M hbound e v u (zeroExternalDomain V v)
      (zeroExternalDomain V u)).symm.trans (h v (zeroExternalDomain V v))
  · intro h v hv
    exact (externalForm_zero V C κ hκ M hbound e v u hv (zeroExternalDomain V u)).trans (h v)

end PfHk.PhysicalCutoffCommutator
