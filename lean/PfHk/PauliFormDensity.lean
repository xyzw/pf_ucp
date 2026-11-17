import PfHk.PauliCommonFormDomain
import PfHk.KatoRellichBackground

/-! Density of the actual spin--photon form domain. The retained free
self-adjoint graph has a dense domain contained in the reference range.
Finite spin amplification and the onto L2 bundle preserve this density. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliFormDensity

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PauliSpin PfHk.KatoRellichBackground PfHk.PhysicalExternalOperator

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

private theorem bundle_denseRange {S X H Q : Type*} [Fintype S] [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (μ : Measure X)
    (J : Q → Lp H 2 μ) (hJ : DenseRange J) :
    DenseRange (fun u : S → Q => FiniteFiberL2.bundle (fun s => J (u s))) := by
  have hp : DenseRange (fun u : S → Q => fun s => J (u s)) :=
    DenseRange.piMap (fun _ : S => hJ)
  have hb : Function.Surjective (FiniteFiberL2.bundle (S := S) (H := H) (μ := μ)) :=
    fun ψ => ⟨fun s => FiniteFiberL2.coordinate s ψ, FiniteFiberL2.bundle_coordinate ψ⟩
  have hc : Continuous (FiniteFiberL2.bundle (S := S) (H := H) (μ := μ)) :=
    FiniteFiberL2.isometry.continuous.comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : S => Lp H 2 μ)).symm.continuous
  exact hb.denseRange.comp hp hc

variable {N : ℕ}
attribute [local irreducible] referenceSubspace inclusion

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (hSA : SelfAdjointGraph
    (freeHilbertGraph (fun _ => 0) C κ hκ M hκbound e))

include C κ hκ M hκbound e hSA

theorem wave_denseRange : DenseRange (PauliReference.wave (N := N)) := by
  have hd : DenseRange (inclusion (Fin N × Fin 3) (fun _ => 0)) := by
    apply hSA.dense.mono
    intro x hx
    have hgraph := Classical.choose_spec hx
    let u := Classical.choose hgraph
    have hu := Classical.choose_spec hgraph
    exact ⟨u, hu.1⟩
  exact bundle_denseRange (S := SpinIndex N) (X := Position (Fin N × Fin 3))
    (H := PhotonFock) (Q := Reference (Fin N × Fin 3) (fun _ => 0)) volume
    (inclusion (Fin N × Fin 3) (fun _ => 0)) hd

theorem physicalDomain_dense : Dense (PauliClosedForm.physicalDomain (N := N)) :=
  wave_denseRange C κ hκ M hκbound e hSA

theorem electronicRadiationDomain_dense :
    Dense {ψ : PauliReference.Wave N | PauliCommonFormDomain.ElectronicRadiationDomain ψ} := by
  have h : {ψ : PauliReference.Wave N | PauliCommonFormDomain.ElectronicRadiationDomain ψ} =
      PauliClosedForm.physicalDomain (N := N) := by
    ext ψ
    exact (PauliCommonFormDomain.physicalDomain_iff ψ).symm
  exact Eq.mpr (congrArg (fun S : Set (PauliReference.Wave N) => Dense S) h)
    (physicalDomain_dense C κ hκ M hκbound e hSA)

end PfHk.PauliFormDensity

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
