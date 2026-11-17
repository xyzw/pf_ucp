import PfHk.PauliOrbitalForm
import PfHk.PauliLocalEnergy
import PfHk.PhysicalCutoffLocality

/-! A scalar cutoff constant near a spinor's support can be removed
from the first argument of its orbital form. -/

noncomputable section
namespace PfHk.PauliOrbitalCutoffLocality

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift GptLean.ElectronicH1Multiplier
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PhysicalLocalEnergy
  PfHk.PhysicalCutoffCommutator PfHk.PhysicalCutoffLocality
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion radiation roughMultiply
  externalCovariant externalForm PhysicalPFScalarMultiplier.multiply
  DifferentiableMultiplier.multiplier DifferentiableMultiplier.derivativeMultiplier

variable {N : ℕ}
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : (Fin N × Fin 3) → Configuration N → ℝ)
  (positive negative : Configuration N → ℝ)

theorem form_localize_left (a : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (z u : Ref N) (hz : Domain A positive negative z) (hu : Domain A positive negative u)
    (hfix : ∀ s, a.scalar.multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) =
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
    (hfirst : ∀ i s, (a.derivative i).multiplier
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) = 0)
    (hsecond : ∀ i s, (a.derivative i).derivativeMultiplier i
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) = 0) :
    PauliOrbitalForm.form C κ hκ M hbound e A positive negative
      (PauliLocalEnergy.localize a.scalar z) u (PauliLocalEnergy.domain_localize hz a.scalar) hu =
    PauliOrbitalForm.form C κ hκ M hbound e A positive negative z u hz hu := by
  apply Finset.sum_congr rfl
  intro s _
  have hzero := commutator_zero (fun _ => 0) C κ hκ M hbound e A positive negative
    a (u s) (hu s) (fun i => hfirst i s) (fun i => hsecond i s)
  have hproduct := form_commutator (fun _ => 0) C κ hκ M hbound e A positive negative
    a (u s) (z s) (hu s) (hz s)
  have hfixed :
      (⟨PhysicalPFScalarMultiplier.multiply (fun _ => 0) a.scalar (u s),
        (hu s).localize (fun _ => 0) a.scalar⟩ :
        {w : Reference (Fin N × Fin 3) (fun _ => 0) //
          ExternalDomain (fun _ => 0) A positive negative w}) = ⟨u s, hu s⟩ :=
    Subtype.ext (reference_multiply_eq_of_value (fun _ => 0) a.scalar (u s) (u s) (hfix s))
  have hleft := congrArg (fun w : {w : Reference (Fin N × Fin 3) (fun _ => 0) //
      ExternalDomain (fun _ => 0) A positive negative w} =>
    externalForm (fun _ => 0) C κ hκ M hbound e A positive negative
      (z s) w.val (hz s) w.property) hfixed
  have herr : inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (PhysicalCutoffCommutator.commutator (fun _ => 0) C κ hκ M hbound e
        A positive negative a (u s) (hu s)) = 0 :=
    (congrArg (fun w : WaveSpace (Fin N × Fin 3) =>
      inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) w) hzero).trans
      (inner_zero_right _)
  exact ((hleft.symm.trans hproduct).trans
    ((congrArg (fun r : ℂ =>
      externalForm (fun _ => 0) C κ hκ M hbound e A positive negative
        (PhysicalPFScalarMultiplier.multiply (fun _ => 0) a.scalar (z s)) (u s)
        ((hz s).localize (fun _ => 0) a.scalar) (hu s) + r) herr).trans (add_zero _))).symm

end PfHk.PauliOrbitalCutoffLocality

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
