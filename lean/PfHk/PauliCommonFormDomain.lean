import PfHk.PauliClosedForm

/-! An explicit description of the common Pauli form domain in the
physical spin--photon L2 space. Every spin component has L2 weak
electronic derivatives and belongs to the actual radiation square-root
graph. The external coefficient classes impose no additional domain. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliCommonFormDomain

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PauliGroundState PfHk.PauliSpin

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

variable {N : ℕ}
attribute [local irreducible] referenceSubspace inclusion ordinary radiation

/-- H1 in the electronic variables intersected with the radiation
square-root domain, in each of the finitely many spin components. -/
def ElectronicRadiationDomain (ψ : PauliReference.Wave N) : Prop :=
  ∀ s : SpinIndex N,
    ∃ d : (Fin N × Fin 3) → WaveSpace (Fin N × Fin 3),
    ∃ r : WaveSpace (Fin N × Fin 3),
      SymmetricLift.HasWeakH1Local
        (fun X => FiniteFiberL2.coordinate s ψ X) (fun q X => d q X) ∧
      ∀ᵐ X ∂volume, (FiniteFiberL2.coordinate s ψ X, r X) ∈ radiationRoot.graph

private theorem zero_relation (w : WaveSpace (Fin N × Fin 3)) :
    ∀ᵐ X ∂volume, (0 : WaveSpace (Fin N × Fin 3)) X = (Real.sqrt (0 : ℝ) : ℂ) • w X := by
  filter_upwards [Lp.coeFn_zero PhotonFock 2 (volume : Measure (Position (Fin N × Fin 3)))]
    with X hX
  simp only [hX, Pi.zero_apply, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]

def referenceOfFree
    (f : SpinIndex N → PhotonLocalization.SpatialFreeVector (I := Fin N × Fin 3) radiationRoot) :
    Ref N :=
  fun s => PhysicalPFFormEvaluation.referenceOfFree (Fin N × Fin 3) (fun _ => 0)
    (f s) 0 (zero_relation (f s).value)

theorem wave_referenceOfFree
    (f : SpinIndex N → PhotonLocalization.SpatialFreeVector (I := Fin N × Fin 3) radiationRoot) :
    PauliReference.wave (referenceOfFree f) = FiniteFiberL2.bundle (fun s => (f s).value) := by
  unfold PauliReference.wave
  apply congrArg (FiniteFiberL2.bundle (S := SpinIndex N) (H := PhotonFock) (μ := volume))
  funext s
  exact PhysicalPFFormEvaluation.referenceOfFree_value (Fin N × Fin 3) (fun _ => 0)
    (f s) 0 (zero_relation (f s).value)

theorem physicalDomain_iff (ψ : PauliReference.Wave N) :
    ψ ∈ PauliClosedForm.physicalDomain (N := N) ↔ ElectronicRadiationDomain ψ := by
  constructor
  · intro h s
    let u := Classical.choose h
    have hu := Classical.choose_spec h
    have he : FiniteFiberL2.coordinate s ψ =
        inclusion (Fin N × Fin 3) (fun _ => 0) (u s) :=
      (congrArg (FiniteFiberL2.coordinate s) hu).symm.trans
        (FiniteFiberL2.coordinate_bundle _ s)
    refine ⟨fun q => ordinary (Fin N × Fin 3) (fun _ => 0) q (u s),
      radiation (Fin N × Fin 3) (fun _ => 0) (u s), ?_, ?_⟩
    · have hw : SymmetricLift.HasWeakH1Local
          (fun X => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
          (fun q X => ordinary (Fin N × Fin 3) (fun _ => 0) q (u s) X) := by
        unfold inclusion ordinary
        exact ElectronicH1Complex.weak (electronic (Fin N × Fin 3) (fun _ => 0) (u s))
      exact Eq.mpr (congrArg (fun w : WaveSpace (Fin N × Fin 3) =>
        SymmetricLift.HasWeakH1Local (fun X => w X)
          (fun q X => ordinary (Fin N × Fin 3) (fun _ => 0) q (u s) X)) he) hw
    · exact Eq.mpr (congrArg (fun w : WaveSpace (Fin N × Fin 3) =>
        ∀ᵐ X ∂volume, (w X, radiation (Fin N × Fin 3) (fun _ => 0) (u s) X) ∈
          radiationRoot.graph) he) (radiation_graph (Fin N × Fin 3) (fun _ => 0) (u s))
  · intro h
    let d : SpinIndex N → (Fin N × Fin 3) → WaveSpace (Fin N × Fin 3) :=
      fun s => Classical.choose (h s)
    let r : SpinIndex N → WaveSpace (Fin N × Fin 3) :=
      fun s => Classical.choose (Classical.choose_spec (h s))
    let f : SpinIndex N → PhotonLocalization.SpatialFreeVector (I := Fin N × Fin 3) radiationRoot :=
      fun s => ⟨FiniteFiberL2.coordinate s ψ, d s, r s,
        (Classical.choose_spec (Classical.choose_spec (h s))).1,
        (Classical.choose_spec (Classical.choose_spec (h s))).2⟩
    refine ⟨referenceOfFree f, ?_⟩
    exact (wave_referenceOfFree f).trans (FiniteFiberL2.bundle_coordinate ψ)

end PfHk.PauliCommonFormDomain

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
