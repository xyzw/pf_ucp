import PfHk.PauliCurrentAlgebra
import PfHk.PauliReference
import PfHk.PhysicalLocalEnergyRough

/-! The concrete finite-spin Pauli form on the common physical reference
space. This module separates its raw form and weak equation from global
potential classes and the normalized fermionic state construction. -/

noncomputable section
namespace PfHk.PauliGroundState

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift PfHk.PauliSpin PfHk.PauliCurrentAlgebra
  PfHk.PhysicalLocalEnergy
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

variable {N : ℕ}
abbrev Ref (N : ℕ) := PauliReference.Ref N
attribute [local irreducible] referenceSubspace

def mass (z u : Ref N) : ℂ :=
  ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
    (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))

def normSquared (u : Ref N) : ℝ :=
  ∑ s, ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s)‖ ^ 2

def Domain (A : (Fin N × Fin 3) → Configuration N → ℝ)
    (positive negative : Configuration N → ℝ) (u : Ref N) : Prop :=
  ∀ s, ExternalDomain (fun _ => 0) A positive negative (u s)

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)

def rawCovariant (A : (Fin N × Fin 3) → Configuration N → ℝ)
    (positive negative : Configuration N → ℝ)
    (u : Ref N) (hu : Domain A positive negative u)
    (q : Fin N × Fin 3) (s : SpinIndex N) : WaveSpace (Fin N × Fin 3) :=
  externalCovariant (fun _ => 0) C κ hκ M hκbound e A positive negative (u s) (hu s) q

def rawContraction (A : (Fin N × Fin 3) → Configuration N → ℝ)
    (positive negative : Configuration N → ℝ)
    (u : Ref N) (hu : Domain A positive negative u) (n : Fin N) :
    SpinIndex N → WaveSpace (Fin N × Fin 3) :=
  contraction n (fun a => rawCovariant C κ hκ M hκbound e A positive negative u hu (n, a))

/-- The full sesquilinear Pauli form, including radiation and signed scalar terms. -/
def rawForm (A : (Fin N × Fin 3) → Configuration N → ℝ)
    (positive negative : Configuration N → ℝ)
    (z u : Ref N) (hz : Domain A positive negative z) (hu : Domain A positive negative u) : ℂ :=
  (1 / 2 : ℂ) * ∑ n, ∑ s,
    inner ℂ (rawContraction C κ hκ M hκbound e A positive negative z hz n s)
      (rawContraction C κ hκ M hκbound e A positive negative u hu n s) +
  (∑ s, inner ℂ (radiation (Fin N × Fin 3) (fun _ => 0) (z s))
    (radiation (Fin N × Fin 3) (fun _ => 0) (u s))) +
  (∑ s, inner ℂ (roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (hz s).positive)
    (roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hu s).positive)) -
  ∑ s, inner ℂ (roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (hz s).negative)
    (roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hu s).negative)

def rawEnergy (A : (Fin N × Fin 3) → Configuration N → ℝ)
    (positive negative : Configuration N → ℝ)
    (u : Ref N) (hu : Domain A positive negative u) : ℝ :=
  (rawForm C κ hκ M hκbound e A positive negative u u hu hu).re

theorem rawEnergy_eq (A : (Fin N × Fin 3) → Configuration N → ℝ)
    (positive negative : Configuration N → ℝ)
    (u : Ref N) (hu : Domain A positive negative u) :
    rawEnergy C κ hκ M hκbound e A positive negative u hu =
      (1 / 2 : ℝ) * ∑ n, ∑ s,
        ‖rawContraction C κ hκ M hκbound e A positive negative u hu n s‖ ^ 2 +
      (∑ s, ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s)‖ ^ 2) +
      (∑ s, ‖roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
        (hu s).positive‖ ^ 2) -
      ∑ s, ‖roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
        (hu s).negative‖ ^ 2 := by
  simp only [rawEnergy, rawForm, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im,
    Complex.re_sum, Complex.im_sum, re_inner_self (H := WaveSpace (Fin N × Fin 3)), zero_div, zero_mul, sub_zero]


/-- The weak eigenvalue equation for this concrete finite-spin form. -/
def IsWeakEigenstate (A : (Fin N × Fin 3) → Configuration N → ℝ)
    (positive negative : Configuration N → ℝ) (E : ℝ)
    (u : Ref N) (hu : Domain A positive negative u) : Prop :=
  ∀ (z : Ref N) (hz : Domain A positive negative z),
    rawForm C κ hκ M hκbound e A positive negative z u hz hu = (E : ℂ) * mass z u


end PfHk.PauliGroundState
