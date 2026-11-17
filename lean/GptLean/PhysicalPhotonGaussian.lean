import GptLean.PhysicalFockWienerSegal
import GptLean.PhysicalGaussianTensorFields

/-!
The full photon and spatial Gaussian unitaries are constructed from the
scalar soft-Fock realization and the proved orthogonal Fock split. The
soft-vacuum image and the source/Fubini identity concern these exact maps.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory Filter Topology PhysicalGaussianCoordinates SymmetricLift
open TensorCoordinates
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

local instance generatedComplete {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] (V : Submodule ℂ (Lp ℂ 2 μ)) :
    CompleteSpace (generatedSubspace μ V) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

abbrev SoftPhotonFock (κ : ℝ) := generatedFockSubspace (softOnePhoton κ)
abbrev HardPhotonFock (κ : ℝ) := generatedFockSubspace (hardOnePhoton κ)

def softBasisIndex (κ : ℝ) : Set (SoftPhotonFock κ) :=
  (exists_hilbertBasis ℂ (SoftPhotonFock κ)).choose

def softBasis (κ : ℝ) : HilbertBasis (softBasisIndex κ) ℂ (SoftPhotonFock κ) :=
  (exists_hilbertBasis ℂ (SoftPhotonFock κ)).choose_spec.choose

variable (BF : StandardSymmetricFockExponential) (κ : ℝ)
  {J : RealStructure (softOnePhoton κ)}
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)

/-- The actual full photon unitary keeps the hard factor and realizes only
its soft factor as scalar Gaussian L². -/
def photonGaussianUnitary : PhotonFock ≃ₗᵢ[ℂ] Lp (HardPhotonFock κ) 2 W.space.measure :=
  (supportedFockEquivalence photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ) (photonExponential BF)).trans
      (tensorLift (softBasis κ) W.unitary)

attribute [local irreducible] tensorLift supportedFockEquivalence

theorem photonGaussianUnitary_apply (u : PhotonFock) :
    photonGaussianUnitary BF κ W u =
      tensorLift (softBasis κ) W.unitary
        (supportedFockEquivalence photonMeasure (softMomentumSet κ)
          (softMomentumSet_measurable κ) (photonExponential BF) u) := rfl

attribute [local irreducible] photonGaussianUnitary

/-- Inserting the soft vacuum gives the constant hard-valued Gaussian fiber. -/
theorem photonGaussianUnitary_vacuum (v : HardPhotonFock κ) :
    photonGaussianUnitary BF κ W (hardPhotonVacuumEmbedding BF κ v) =ᵐ[W.space.measure]
      fun _ => v := by
  let E : PhotonFock ≃ₗᵢ[ℂ] TensorSpace (SoftPhotonFock κ) (HardPhotonFock κ) :=
    supportedFockEquivalence photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) (photonExponential BF)
  let L : TensorSpace (SoftPhotonFock κ) (HardPhotonFock κ) ≃ₗᵢ[ℂ]
      Lp (HardPhotonFock κ) 2 W.space.measure :=
    tensorLift (softBasis κ) W.unitary
  let vac : SoftPhotonFock κ := generatedVacuum photonMeasure (softOnePhoton κ)
  have hsplit : E (hardPhotonVacuumEmbedding BF κ v) = tensor vac v :=
    (congrArg (fun u : PhotonFock => E u)
      (hardPhotonVacuumEmbedding_apply BF κ v)).trans
        (supportedFockEquivalence_hard photonMeasure (softMomentumSet κ)
          (softMomentumSet_measurable κ) (photonExponential BF) v)
  have hvalue : photonGaussianUnitary BF κ W (hardPhotonVacuumEmbedding BF κ v) =
      L (tensor vac v) :=
    (photonGaussianUnitary_apply BF κ W _).trans
      (congrArg (fun z : TensorSpace (SoftPhotonFock κ) (HardPhotonFock κ) => L z) hsplit)
  have ht : L (tensor vac v) =ᵐ[W.space.measure] fun q => W.unitary vac q • v :=
    tensorLift_tensor_ae (softBasis κ) W.unitary vac v
  have hv : W.unitary vac =ᵐ[W.space.measure] fun _ => (1 : ℂ) := W.vacuum
  have he : photonGaussianUnitary BF κ W (hardPhotonVacuumEmbedding BF κ v) =ᵐ[W.space.measure]
      L (tensor vac v) :=
    Filter.Eventually.of_forall (fun q => congrArg
      (fun f : Lp (HardPhotonFock κ) 2 W.space.measure => f q) hvalue)
  exact he.trans (ht.trans (hv.mono (fun q hq => by
    change W.unitary vac q • v = v
    rw [hq, one_smul])))

attribute [local irreducible] productSource spatialUnitary

/-- The product-space source is the lift of the actual photon unitary. -/
def photonGaussianSource (N : ℕ) :
    Lp PhotonFock 2 (volume : Measure (Configuration N)) ≃ₗᵢ[ℂ]
      Lp (HardPhotonFock κ) 2 (W.space.measure.prod (volume : Measure (Configuration N))) :=
  productSource (X := Configuration N) (Q := W.space.Q)
    (H := PhotonFock) (K := HardPhotonFock κ)
    volume W.space.measure (photonGaussianUnitary BF κ W)

/-- Slicing is Fubini applied to exactly the same product-space source. -/
def photonGaussianSlicing (N : ℕ) :
    Lp PhotonFock 2 (volume : Measure (Configuration N)) ≃ₗᵢ[ℂ]
      Lp (Lp (HardPhotonFock κ) 2 (volume : Measure (Configuration N))) 2 W.space.measure :=
  spatialUnitary (X := Configuration N) (Q := W.space.Q)
    (H := PhotonFock) (K := HardPhotonFock κ)
    volume W.space.measure (photonGaussianUnitary BF κ W)

attribute [local irreducible] Gaussian.unitaryFiber PhysicalSourceFubini.curryEquiv
  photonGaussianSource photonGaussianSlicing

theorem photonGaussian_source_fubini (N : ℕ)
    (v : Lp PhotonFock 2 (volume : Measure (Configuration N))) :
    (photonGaussianSlicing BF κ W N v :
      W.space.Q → Lp (HardPhotonFock κ) 2 (volume : Measure (Configuration N))) =ᵐ[W.space.measure]
      fun q => PhysicalSourceFubini.curryEquiv (photonGaussianSource BF κ W N v) q := by
  have he : photonGaussianSlicing BF κ W N v =
      PhysicalSourceFubini.curryEquiv (photonGaussianSource BF κ W N v) := by
    unfold photonGaussianSlicing photonGaussianSource spatialUnitary
    rfl
  exact Filter.Eventually.of_forall (fun q => congrArg
    (fun z : Lp (Lp (HardPhotonFock κ) 2 (volume : Measure (Configuration N)))
      2 W.space.measure => z q) he)

end GptLean.PhysicalFock
