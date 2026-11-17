import PfHk.PauliRawForm

/-! The orbital form on finite spin families is the sum of the existing
physical orbital forms. The zero potential coordinate of the free
reference domain vanishes, leaving exactly the radiation and signed
scalar terms shared with the Pauli form. -/

noncomputable section
namespace PfHk.PauliOrbitalForm

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift PfHk.PauliSpin PfHk.PauliGroundState
  PfHk.PhysicalLocalEnergy
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

attribute [local irreducible] referenceSubspace inclusion radiation potential
  roughMultiply externalCovariant

theorem potential_zero {I : Type} [Fintype I] [DecidableEq I]
    (u : Reference I (fun _ => 0)) : potential I (fun _ => 0) u = 0 := by
  have hp : ∀ᵐ x ∂volume, potential I (fun _ => 0) u x =
      (Real.sqrt (0 : ℝ) : ℂ) •
        PhysicalMultiplicationGraph.inclusion volume _
          (potentialSource I (fun _ => 0) u) x := by
    unfold potential
    exact (potentialSource I (fun _ => 0) u).property
  apply Lp.ext
  filter_upwards [hp, Lp.coeFn_zero PhotonFock 2 (volume : Measure (Position I))]
    with x hx hzero
  have h : potential I (fun _ => 0) u x = 0 := by
    simpa only [Real.sqrt_zero, Complex.ofReal_zero, zero_smul] using hx
  exact h.trans hzero.symm

private theorem sum_form {S J K : Type*} [Fintype S] [Fintype J] [Fintype K]
    (d : S → J × K → ℂ) (r p m : S → ℂ) :
    (∑ s, ((1 / 2 : ℂ) * (∑ q, d s q) + r s + p s - m s)) =
      (1 / 2 : ℂ) * (∑ j, ∑ k, ∑ s, d s (j, k)) +
        ((∑ s, r s) + (∑ s, p s) - ∑ s, m s) := by
  have hd : (∑ s, ∑ q, d s q) = ∑ j, ∑ k, ∑ s, d s (j, k) :=
    Finset.sum_comm.trans (Fintype.sum_prod_type (fun q : J × K => ∑ s, d s q))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hd]
  ring

variable {N : ℕ}
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : (Fin N × Fin 3) → Configuration N → ℝ)
  (positive negative : Configuration N → ℝ)

def common (z u : Ref N) (hz : Domain A positive negative z)
    (hu : Domain A positive negative u) : ℂ :=
  (∑ s, inner ℂ (radiation (Fin N × Fin 3) (fun _ => 0) (z s))
    (radiation (Fin N × Fin 3) (fun _ => 0) (u s))) +
  (∑ s, inner ℂ
    (roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) (hz s).positive)
    (roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hu s).positive)) -
  ∑ s, inner ℂ
    (roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) (hz s).negative)
    (roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hu s).negative)

/-- Finite spin amplification of the existing physical orbital form. -/
def form (z u : Ref N) (hz : Domain A positive negative z)
    (hu : Domain A positive negative u) : ℂ :=
  ∑ s, externalForm (fun _ => 0) C κ hκ M hκbound e A positive negative
    (z s) (u s) (hz s) (hu s)

theorem form_eq (z u : Ref N) (hz : Domain A positive negative z)
    (hu : Domain A positive negative u) :
    form C κ hκ M hκbound e A positive negative z u hz hu =
      (1 / 2 : ℂ) * (∑ n, ∑ a, ∑ s,
        inner ℂ (rawCovariant C κ hκ M hκbound e A positive negative z hz (n, a) s)
          (rawCovariant C κ hκ M hκbound e A positive negative u hu (n, a) s)) +
        common A positive negative z u hz hu := by
  unfold form
  have he (s : SpinIndex N) :
      externalForm (fun _ => 0) C κ hκ M hκbound e A positive negative
        (z s) (u s) (hz s) (hu s) =
      (1 / 2 : ℂ) * (∑ q,
        inner ℂ (rawCovariant C κ hκ M hκbound e A positive negative z hz q s)
          (rawCovariant C κ hκ M hκbound e A positive negative u hu q s)) +
      inner ℂ (radiation (Fin N × Fin 3) (fun _ => 0) (z s))
        (radiation (Fin N × Fin 3) (fun _ => 0) (u s)) +
      inner ℂ
        (roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) (hz s).positive)
        (roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hu s).positive) -
      inner ℂ
        (roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) (hz s).negative)
        (roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hu s).negative) := by
    simp only [externalForm, rawCovariant, potential_zero, inner_zero_left, add_zero]
  exact (Finset.sum_congr rfl (fun s _ => he s)).trans (sum_form _ _ _ _)

theorem rawForm_eq (z u : Ref N) (hz : Domain A positive negative z)
    (hu : Domain A positive negative u) :
    rawForm C κ hκ M hκbound e A positive negative z u hz hu =
      (1 / 2 : ℂ) * (∑ n, ∑ s,
        inner ℂ (rawContraction C κ hκ M hκbound e A positive negative z hz n s)
          (rawContraction C κ hκ M hκbound e A positive negative u hu n s)) +
        common A positive negative z u hz hu := by
  unfold rawForm common
  ring

end PfHk.PauliOrbitalForm

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
