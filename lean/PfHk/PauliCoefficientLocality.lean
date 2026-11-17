import PfHk.PauliOrbitalForm
import PfHk.PhysicalCoefficientLocality

/-! The actual Pauli form depends only on the external coefficients on
the supports of its two arguments. -/

noncomputable section
namespace PfHk.PauliCoefficientLocality

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift PfHk.PauliSpin PfHk.PauliGroundState
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCoefficientLocality
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion radiation roughMultiply
  externalCovariant rawCovariant rawContraction

variable {N : ℕ}
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A A' : (Fin N × Fin 3) → Configuration N → ℝ)
  (positive negative positive' negative' : Configuration N → ℝ)

theorem contraction_congr (u : Ref N)
    (hu : Domain A positive negative u) (hu' : Domain A' positive' negative' u)
    (hU : ∀ s, Agreement A A' positive negative positive' negative'
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))) (n : Fin N) :
    rawContraction C κ hκ M hbound e A positive negative u hu n =
      rawContraction C κ hκ M hbound e A' positive' negative' u hu' n := by
  have he : (fun k => rawCovariant C κ hκ M hbound e A positive negative u hu (n, k)) =
      (fun k => rawCovariant C κ hκ M hbound e A' positive' negative' u hu' (n, k)) := by
    funext k s
    unfold rawCovariant
    exact covariant_congr (fun _ => 0) A A' positive negative positive' negative'
      C κ hκ M hbound e (u s) (hu s) (hu' s) (hU s) (n, k)
  unfold rawContraction
  exact congrArg (PauliCurrentAlgebra.contraction n) he

theorem common_congr (z u : Ref N)
    (hz : Domain A positive negative z) (hu : Domain A positive negative u)
    (hz' : Domain A' positive' negative' z) (hu' : Domain A' positive' negative' u)
    (hZ : ∀ s, Agreement A A' positive negative positive' negative'
      (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)))
    (hU : ∀ s, Agreement A A' positive negative positive' negative'
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))) :
    PauliOrbitalForm.common A positive negative z u hz hu =
      PauliOrbitalForm.common A' positive' negative' z u hz' hu' := by
  have hp := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun s _ => congrArg₂ (fun x y : WaveSpace (Fin N × Fin 3) => inner ℂ x y)
      (roughMultiply_congr _ _ _ (hz s).positive (hz' s).positive (hZ s).positive)
      (roughMultiply_congr _ _ _ (hu s).positive (hu' s).positive (hU s).positive))
  have hn := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun s _ => congrArg₂ (fun x y : WaveSpace (Fin N × Fin 3) => inner ℂ x y)
      (roughMultiply_congr _ _ _ (hz s).negative (hz' s).negative (hZ s).negative)
      (roughMultiply_congr _ _ _ (hu s).negative (hu' s).negative (hU s).negative))
  exact congrArg₂ (fun p m : ℂ =>
    (∑ s, inner ℂ (radiation (Fin N × Fin 3) (fun _ => 0) (z s))
      (radiation (Fin N × Fin 3) (fun _ => 0) (u s))) + p - m) hp hn

theorem form_congr (z u : Ref N)
    (hz : Domain A positive negative z) (hu : Domain A positive negative u)
    (hz' : Domain A' positive' negative' z) (hu' : Domain A' positive' negative' u)
    (hZ : ∀ s, Agreement A A' positive negative positive' negative'
      (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)))
    (hU : ∀ s, Agreement A A' positive negative positive' negative'
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))) :
    rawForm C κ hκ M hbound e A positive negative z u hz hu =
      rawForm C κ hκ M hbound e A' positive' negative' z u hz' hu' := by
  have hk : (∑ n, ∑ s,
      inner ℂ (rawContraction C κ hκ M hbound e A positive negative z hz n s)
        (rawContraction C κ hκ M hbound e A positive negative u hu n s)) =
      ∑ n, ∑ s,
      inner ℂ (rawContraction C κ hκ M hbound e A' positive' negative' z hz' n s)
        (rawContraction C κ hκ M hbound e A' positive' negative' u hu' n s) := by
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro s _
    exact congrArg₂ (fun x y : WaveSpace (Fin N × Fin 3) => inner ℂ x y)
      (congrFun (contraction_congr C κ hκ M hbound e A A'
        positive negative positive' negative' z hz hz' hZ n) s)
      (congrFun (contraction_congr C κ hκ M hbound e A A'
        positive negative positive' negative' u hu hu' hU n) s)
  exact (PauliOrbitalForm.rawForm_eq C κ hκ M hbound e A positive negative z u hz hu).trans
    ((congrArg₂ (fun k c : ℂ => (1 / 2 : ℂ) * k + c) hk
      (common_congr A A' positive negative positive' negative' z u hz hu hz' hu' hZ hU)).trans
      (PauliOrbitalForm.rawForm_eq C κ hκ M hbound e A' positive' negative' z u hz' hu').symm)

end PfHk.PauliCoefficientLocality

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
