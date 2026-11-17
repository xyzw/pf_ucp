import PfHk.PauliQuantumCommutator
import PfHk.PauliExternalCommutatorAlgebra
import PfHk.PauliRawForm

/-! Add the real external vector potential to the proved physical
quantum covariant commutator. Only the classical weak curl pairing is
left for the distributional local theorem. -/

noncomputable section
namespace PfHk.PauliPhysicalCovariantCommutator

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  PfHk.PhysicalLocalEnergy PfHk.PhysicalFieldRegularity
  PfHk.CenteredPhysicalReference PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference
  PfHk.PauliPhysicalFieldLinearity
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion ordinary roughMultiply
  covariant PauliMagneticOperator.component

variable {N : ℕ}
  (C : CanonicalSectorCCR photonMeasure) (F : Frame) (χ : ArticleCutoff) (e : ℝ)
  (hUV : CarlemanUV χ) (W : ConcreteWeylLaw photonMeasure)
  (G : StandardWeylGraphC1 W) (D : StandardWeylFormCoreDensity W G)
  (A : (Fin N × Fin 3) → Configuration N → ℝ)
  (positive negative : Configuration N → ℝ)

include W G D in
theorem cross_of_classical (n : Fin N) (k : Fin 3)
    (z u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hz : ExternalDomain (fun _ => 0) A positive negative z)
    (hu : ExternalDomain (fun _ => 0) A positive negative u)
    (hzc : CompactlySupportedIn Set.univ z) (huc : CompactlySupportedIn Set.univ u)
    (b : ℂ)
    (hclassical :
      (inner ℂ (qP C F χ e (n, k + 1) z)
        (roughMultiply (A (n, k + 2)) (inclusion (Fin N × Fin 3) (fun _ => 0) u)
          (hu.vector (n, k + 2))) -
      inner ℂ (roughMultiply (A (n, k + 2)) (inclusion (Fin N × Fin 3) (fun _ => 0) z)
        (hz.vector (n, k + 2))) (qP C F χ e (n, k + 1) u)) -
      (inner ℂ (qP C F χ e (n, k + 2) z)
        (roughMultiply (A (n, k + 1)) (inclusion (Fin N × Fin 3) (fun _ => 0) u)
          (hu.vector (n, k + 1))) -
      inner ℂ (roughMultiply (A (n, k + 1)) (inclusion (Fin N × Fin 3) (fun _ => 0) z)
        (hz.vector (n, k + 1))) (qP C F χ e (n, k + 2) u)) = -Complex.I * b) :
    inner ℂ
      (externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e A positive negative z hz (n, k + 1))
      (externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e A positive negative u hu (n, k + 2)) -
    inner ℂ
      (externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e A positive negative z hz (n, k + 2))
      (externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e A positive negative u hu (n, k + 1)) =
      -Complex.I * b + Complex.I * (e : ℂ) * inner ℂ
        (inclusion (Fin N × Fin 3) (fun _ => 0) z)
        (PauliMagneticOperator.component F χ hUV C n k u) := by
  have hq := PauliQuantumCommutator.qP_cross_curl F χ e C hUV W G D
    n k Set.univ isOpen_univ z u hzc huc
  have ha := PauliExternalCommutatorAlgebra.rough_pair_commute
    (A (n, k + 1)) (A (n, k + 2))
    (inclusion (Fin N × Fin 3) (fun _ => 0) z)
    (inclusion (Fin N × Fin 3) (fun _ => 0) u)
    (hz.vector (n, k + 1)) (hz.vector (n, k + 2))
    (hu.vector (n, k + 1)) (hu.vector (n, k + 2))
  exact (PauliExternalCommutatorAlgebra.add_scalar_commutator
    (H := WaveSpace (Fin N × Fin 3))
    (qP C F χ e (n, k + 1) z) (qP C F χ e (n, k + 2) z)
    (qP C F χ e (n, k + 1) u) (qP C F χ e (n, k + 2) u)
    _ _ _ _ _ _ hq hclassical ha).trans (add_comm _ _)

end PfHk.PauliPhysicalCovariantCommutator

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
