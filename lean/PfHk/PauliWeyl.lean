import PfHk.PauliReference
import PfHk.PauliCurrentCovariance
import GptLean.PhysicalWeylReference

/-! Actual photon Weyl displacements on finite-spin Pauli reference
vectors. The pointwise current and kinetic identities include the spin
contribution automatically through the Pauli contraction. -/

noncomputable section
namespace PfHk.PauliWeyl

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.Representability GptLean.PhysicalWeyl GptLean.SymmetricLift
  PauliSpin PauliCurrentAlgebra
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 25000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

variable {N : ℕ}
  (W : ConcreteWeylLaw photonMeasure) {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
  (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)

local instance referenceAddCommGroup : AddCommGroup (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  (referenceSubspace (Fin N × Fin 3) (fun _ => 0)).addCommGroup
local instance referenceModule : Module ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  (referenceNormedSpace (Fin N × Fin 3) (fun _ => 0)).toModule
local instance referenceSMul : SMul ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  (referenceModule (N := N)).toSMul

attribute [local irreducible] referenceSubspace

abbrev Ref := PauliReference.Ref N

def displaced (u : Ref (N := N)) : Ref (N := N) :=
  fun s => weylRef (I := Fin N × Fin 3) (f := f) (fun _ => 0) W K hK (u s)

theorem sigma_displaced (n : Fin N) (a : Fin 3) (u : Ref (N := N)) :
    sigmaFamily n a (displaced W K hK u) = displaced W K hK (sigmaFamily n a u) :=
  sigmaFamily_map (H := Reference (Fin N × Fin 3) (fun _ => 0))
    (K := Reference (Fin N × Fin 3) (fun _ => 0)) n a
    (weylRef (I := Fin N × Fin 3) (f := f) (fun _ => 0) W K hK).toLinearMap u

theorem wave_norm_sq_displaced (u : Ref (N := N)) :
    ‖PauliReference.wave (displaced W K hK u)‖^2 = ‖PauliReference.wave u‖^2 := by
  have h (s : SpinIndex N) :
      ‖inclusion (Fin N × Fin 3) (fun _ => 0) (displaced W K hK u s)‖^2 =
        ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s)‖^2 :=
    congrArg (fun r : ℝ => r ^ 2)
      (inclusion_weylRef_norm (I := Fin N × Fin 3) (f := f) (fun _ => 0) W K hK (u s))
  exact (PauliReference.wave_norm_sq (N := N) (displaced W K hK u)).trans
    ((Finset.sum_congr rfl (fun s _ => h s)).trans (PauliReference.wave_norm_sq (N := N) u).symm)

theorem radiation_norm_sq_displaced (u : Ref (N := N)) :
    (∑ s, ‖radiation (Fin N × Fin 3) (fun _ => 0) (displaced W K hK u s)‖^2) =
      (∑ s, ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s)‖^2) +
        2 * (∑ s, (inner ℂ (annihilationRef (fun _ => 0) K (u s))
          (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))).re) +
        ‖K.val.2‖^2 * ‖PauliReference.wave u‖^2 := by
  simp only [displaced, radiation_weylRef_norm_sq, Finset.sum_add_distrib,
    ← Finset.mul_sum, PauliReference.wave_norm_sq]

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)

/-- Every spin component has the same photon isometry and classical shift. -/
theorem pointwise_data (n : Fin N) (u : Ref (N := N)) :
    ∀ᵐ X ∂volume,
      (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (displaced W K hK u s) X) =
        (fun s => W.weyl f (inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)) ∧
      (fun a s => covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e (n, a)
        (displaced W K hK u s) X) =
        (fun a s => W.weyl f (covariant (Fin N × Fin 3) (fun _ => 0)
          C κ hκ M hbound e (n, a) (u s) X +
          ((-(e * classicalField κ f (n, a) X) : ℝ) : ℂ) •
            inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)) := by
  filter_upwards [ae_all_iff.mpr (fun s => inclusion_weylRef_ae (I := Fin N × Fin 3) (f := f) (fun _ => 0) W K hK (u s)),
    ae_all_iff.mpr (fun a : Fin 3 => ae_all_iff.mpr (fun s =>
      covariant_weylRef_ae (I := Fin N × Fin 3) (f := f) (fun _ => 0) W K hK C κ hκ M hbound e (n, a) (u s)))]
      with X hv hd
  constructor
  · funext s
    exact hv s
  · funext a s
    simpa only [displaced, Complex.ofReal_neg, neg_smul, sub_eq_add_neg] using hd a s

theorem current_displaced_ae (n : Fin N) (u : Ref (N := N)) (a : Fin 3) :
    ∀ᵐ X ∂volume,
      current (H := PhotonFock) n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (displaced W K hK u s) X)
        (fun b s => covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e (n, b)
          (displaced W K hK u s) X) a =
      current (H := PhotonFock) n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
        (fun b s => covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e (n, b)
          (u s) X) a - e * classicalField κ f (n, a) X *
        density (H := PhotonFock) (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) := by
  filter_upwards [pointwise_data W K hK C κ hκ M hbound e n u] with X hX
  have hj := congrArg₂ (fun (v : SpinIndex N → PhotonFock)
      (d : Fin 3 → SpinIndex N → PhotonFock) => current (H := PhotonFock) n v d a)
    hX.1 hX.2
  exact hj.trans ((current_isometry_shift (H := PhotonFock) (K := PhotonFock) n
    (W.weyl f).toLinearIsometry _ _ _ a).trans (by ring))

theorem kinetic_displaced_ae (n : Fin N) (u : Ref (N := N)) :
    ∀ᵐ X ∂volume,
      kinetic (H := PhotonFock) n (fun a s => covariant (Fin N × Fin 3) (fun _ => 0)
        C κ hκ M hbound e (n, a) (displaced W K hK u s) X) =
      kinetic (H := PhotonFock) n (fun a s => covariant (Fin N × Fin 3) (fun _ => 0)
        C κ hκ M hbound e (n, a) (u s) X) +
      (∑ a, -(e * classicalField κ f (n, a) X) *
        current (H := PhotonFock) n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
          (fun b s => covariant (Fin N × Fin 3) (fun _ => 0)
            C κ hκ M hbound e (n, b) (u s) X) a) +
      (1 / 2 : ℝ) * (∑ a, (-(e * classicalField κ f (n, a) X))^2) *
        density (H := PhotonFock) (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) := by
  filter_upwards [pointwise_data W K hK C κ hκ M hbound e n u] with X hX
  exact (congrArg (kinetic (H := PhotonFock) n) hX.2).trans
    (kinetic_isometry_shift (H := PhotonFock) (K := PhotonFock) n
      (W.weyl f).toLinearIsometry _ _ _)

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

end PfHk.PauliWeyl
