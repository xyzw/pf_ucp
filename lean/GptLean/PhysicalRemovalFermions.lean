import GptLean.PhysicalGaussianSource
import GptLean.PhysicalPhotonGaussian
import GptLean.PhysicalPFSource
import GptLean.PhysicalPFVacuumInsertion

/-!
Fermionic source vectors and vacuum insertion use the same normal
compression. The Gaussian source commutes with electronic permutations
because it acts on the photon fiber.
-/

noncomputable section
namespace GptLean.PhysicalPFSource

open MeasureTheory Filter PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalGaussianCoordinates PhysicalElectronicFermions
  PhysicalPFVacuumInsertion RemovalSource Repair SymmetricLift
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

private theorem productSource_permutation {Q H K : Type*} [MeasurableSpace Q]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] (N : ℕ) (μ : Measure Q)
    [SFinite μ] [IsSeparable μ] (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) :
    SpatialPermutationIntertwining
      (productSource (volume : Measure (Configuration N)) μ U) := by
  intro π u v h
  exact productSource_pullback volume μ U
    (permuteConfiguration π) (permuteConfiguration π).measurePreserving u v h

private theorem spatialLift_compression {H K T : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup T] [NormedSpace ℝ T] (N : ℕ)
    {R : Gaussian.RankOneData (FullSpace N K) T}
    (D : PhotonLocalizationChannel.NormalConjugationData R) (J : H →ₗᵢ[ℂ] K)
    (v : FullSpace N H)
    (hv : HasElectronicCharacter (fun π => permuteConfiguration π) (signCharacter N) v) :
    compression D (R.rankOne (spatialLift volume J v)) =
      R.rankOne (spatialLift volume J v) :=
  compression_rankOne_of_character D _
    (fiberOperator_character N H J.toContinuousLinearMap v hv)

variable (N : ℕ) (V : Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (k : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hk : ∀ i, AEStronglyMeasurable (k i) volume)
  (M : ℝ) (hM : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 400000 in
theorem fermionic_source_exists {x : B.FullTrace N} (hx : x ∈ B.fermionicStates N)
    (he : (normalEnergy (Fin N × Fin 3) V C k hk M hM B S e).expectation x < ⊤) :
    ∃ source : Source (Fin N × Fin 3) V B x, ∀ n,
      HasElectronicCharacter (fun π => permuteConfiguration π) (signCharacter N)
        (inclusion (Fin N × Fin 3) V (source.vector n)) := by
  have hsrc : ∃ v : ℕ → WaveSpace (Fin N × Fin 3),
      HasSum (fun n => (B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne (v n)) x ∧
        ∀ n, HasElectronicCharacter (fun π => permuteConfiguration π) (signCharacter N) (v n) :=
    B.fermionicState_sources N (x := x) hx
  obtain ⟨v, hv, hchar⟩ := hsrc
  have hd (n : ℕ) : ∃ u : Reference (Fin N × Fin 3) V,
      inclusion (Fin N × Fin 3) V u = v n :=
    (PhysicalPFRadiation.normalEnergy_rankOne_finite_iff
      (Fin N × Fin 3) V C k hk M hM B S e (v n)).mp
      (PhysicalNormalSpectral.source_form_finite
        (normalEnergy (Fin N × Fin 3) V C k hk M hM B S e) hv he n)
  choose u hu using hd
  refine ⟨⟨u, hv.congr_fun (fun n =>
    congrArg (B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne (hu n))⟩, ?_⟩
  intro n
  change HasElectronicCharacter _ _ (inclusion (Fin N × Fin 3) V (u n))
  rw [hu]
  exact hchar n

attribute [local irreducible] photonGaussianSource productSource photonGaussianUnitary
  insertion spatialLift hardPhotonVacuumEmbedding

variable (BF : StandardSymmetricFockExponential) (κ : ℝ)
  {J : RealStructure (softOnePhoton κ)}
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)

section Permutation

-- Match the direct normed-space parents used by the concrete source unitary.
local instance fermionPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance fermionHardDirectInner : InnerProductSpace ℂ (HardPhotonFock κ) :=
  { (inferInstance : InnerProductSpace ℂ (HardPhotonFock κ)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (HardPhotonFock κ)) }

set_option backward.isDefEq.respectTransparency.types true in
set_option diagnostics true in
theorem photonGaussianSource_permutation :
    SpatialPermutationIntertwining (Q := W.space.Q) (H := PhotonFock)
      (K := HardPhotonFock κ) (μ := W.space.measure) (N := N)
      (photonGaussianSource BF κ W N) := by
  unfold photonGaussianSource
  exact productSource_permutation (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
    N W.space.measure (photonGaussianUnitary BF κ W)

end Permutation

set_option backward.isDefEq.respectTransparency.types true in
theorem insertion_compression (v : Lp (HardPhotonFock κ) 2
    (volume : Measure (Configuration N)))
    (hv : HasElectronicCharacter (fun π => permuteConfiguration π) (signCharacter N) v) :
    B.fermionicCompression N ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne
      (insertion volume BF κ v)) =
      (B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne (insertion volume BF κ v) := by
  have h := spatialLift_compression (H := HardPhotonFock κ) (K := PhotonFock)
    (T := B.Trace (WaveSpace (Fin N × Fin 3))) N
    (R := (B.realization (WaveSpace (Fin N × Fin 3))).rank)
    (B.conjugation (H := WaveSpace (Fin N × Fin 3))) (hardPhotonVacuumEmbedding BF κ) v hv
  have he : insertion volume BF κ v = spatialLift volume (hardPhotonVacuumEmbedding BF κ) v := by
    unfold insertion
    rfl
  exact (congrArg (fun u : WaveSpace (Fin N × Fin 3) =>
    B.fermionicCompression N ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne u) =
      (B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne u) he).mpr h

end GptLean.PhysicalPFSource
