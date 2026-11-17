import GptLean.PhysicalRemovalOriginalTests
import GptLean.PhysicalRemovalHardTests
import GptLean.PhysicalGaussianRealTests
import GptLean.PhysicalPFCurrentBounds
import GptLean.PhysicalPFVacuumMoments
import GptLean.PhysicalGaussianPFSource
import GptLean.RemovalLatticeOutput

/-!
The observable part of physical infrared removal. Density and current
tests use the original normal source, while all hard and full marginal
coordinates use the same actual photon marginal. The hard spectral test
constructor is supplied separately and contains no removal output.
-/

noncomputable section

namespace GptLean.PhysicalRemovalObservables

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace PhysicalPFSource
  PhysicalPFVacuumInsertion PhysicalPFVacuumEnergy PhysicalPFCurrentEvaluation
  PhysicalPFCurrentBounds PhysicalRemovalMarginal PhotonLocalization RemovalState
  RemovalSource RemovalEnergy PhysicalPhotonMarginal
open scoped ENNReal InnerProductSpace BoundedContinuousFunction

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

local instance removalObservablesPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance removalObservablesHardDirectInner (κ : ℝ) :
    InnerProductSpace ℂ (generatedFockSubspace (hardOnePhoton κ)) :=
  { (inferInstance : InnerProductSpace ℂ (generatedFockSubspace (hardOnePhoton κ))) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (generatedFockSubspace (hardOnePhoton κ))) }

variable {DensityTest CurrentTest : Type} (N : ℕ) (c : ℝ) (hc : 0 ≤ c)
  (C : CanonicalSectorCCR photonMeasure)
  (k h s : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hk : ∀ i, AEStronglyMeasurable (k i) volume)
  (hh : ∀ i, AEStronglyMeasurable (h i) volume)
  (hs : ∀ i, AEStronglyMeasurable (s i) volume)
  (Mk Mh Ms : ℝ)
  (hMk : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ Mk)
  (hMh : ∀ i, ∀ᵐ x ∂volume, ‖h i x‖ ≤ Mh)
  (hMs : ∀ i, ∀ᵐ x ∂volume, ‖s i x‖ ≤ Ms)
  (hsplit : ∀ i, ∀ᵐ x ∂volume, k i x = h i x + s i x)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (BF : StandardSymmetricFockExponential) (κ e : ℝ)
  {J : RealStructure (softOnePhoton κ)}
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)
  (hsoft : ∀ i, ∀ᵐ x ∂volume, (s i x).val.1 ∈ (hardOnePhoton κ)ᗮ)
  (densityWeight : DensityTest → Position (Fin N × Fin 3) → ℝ)
  (densityMeasurable : ∀ t, AEStronglyMeasurable (densityWeight t) volume)
  (densityBound : DensityTest → ℝ) (densityNonneg : ∀ t, 0 ≤ densityBound t)
  (densityBounded : ∀ t x, |densityWeight t x| ≤ densityBound t)
  (currentWeight : CurrentTest → Position (Fin N × Fin 3) → ℝ)
  (currentMeasurable : ∀ t, AEStronglyMeasurable (currentWeight t) volume)
  (currentBound : CurrentTest → ℝ)
  (currentBounded : ∀ t x, |currentWeight t x| ≤ currentBound t)
  (direction : CurrentTest → Fin N × Fin 3)

/-- The bounded physical position test on the full spatial photon space. -/
def densityFull (t : DensityTest) : B.Trace (WaveSpace (Fin N × Fin 3)) →L[ℝ] ℝ :=
  boundedTrace (B.realization (WaveSpace (Fin N × Fin 3))).functional
    (realL2Multiplier (densityWeight t) (densityMeasurable t) (densityBound t)
      (ae_of_all _ (densityBounded t)))

/-- The same bounded position test on the hard spatial photon space. -/
def densityHard (t : DensityTest) :
    B.Trace (Lp (generatedFockSubspace (hardOnePhoton κ)) 2
      (volume : Measure (Position (Fin N × Fin 3)))) →L[ℝ] ℝ :=
  boundedTrace (B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2
    (volume : Measure (Position (Fin N × Fin 3))))).functional
    (realL2Multiplier (densityWeight t) (densityMeasurable t) (densityBound t)
      (ae_of_all _ (densityBounded t)))

set_option backward.isDefEq.respectTransparency.types true in
/-- Assembly uses the same source, form, current approximants, and marginal coordinates. -/
def latticeObservableData
    (m : (normalEnergy (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
      C k hk Mk hMk B S e).State)
    (source : Source (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x) B m.val)
    (hardTests : OriginalHardTests (volume : Measure (Position (Fin N × Fin 3))) B BF κ W
      (fun n => inclusion (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
        (source.vector n))
      (photonCoordinates B (hardTargetTrace BF κ B volume m.val))) :
    LatticeObservableData (Q := W.space.Q) (N := N) (μ := W.space.measure)
      (Ho := PhotonFock) (H := generatedFockSubspace (hardOnePhoton κ))
      (Hr := WithLp 2 (PhotonFock × PhotonFock))
      (F := WithLp 2 (generatedFockSubspace (hardOnePhoton κ) ×
        generatedFockSubspace (hardOnePhoton κ)))
      (Hfull := WaveSpace (Fin N × Fin 3))
      (source.gaussianLattice C k hk Mk hMk S e BF κ W m.property.2.2 m.property.2.1)
      (B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2
        (volume : Measure (Position (Fin N × Fin 3))))).rank
      (B.traceData (H := Lp (generatedFockSubspace (hardOnePhoton κ)) 2
        (volume : Measure (Position (Fin N × Fin 3)))))
      (hardEnergy (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
        C h hh Mh hMh B S BF κ e)
      (B.realization (WaveSpace (Fin N × Fin 3))).rank
      (B.traceData (H := WaveSpace (Fin N × Fin 3)))
      (normalEnergy (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
        C k hk Mk hMk B S e)
      (hardRadiationOperator κ) (fun i x => hardFieldOperator κ (h i x).val.1)
      e (insertion volume BF κ) m DensityTest CurrentTest Marginal Marginal where
  densityHard := densityHard N B κ densityWeight densityMeasurable densityBound densityBounded
  currentHard := hardTestedCurrent N c C h hh Mh hMh B S BF κ e currentWeight currentMeasurable
    currentBound (fun t => ae_of_all _ (currentBounded t)) direction
  density := densityFull N B densityWeight densityMeasurable densityBound densityBounded
  current t := testedCurrent (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
    C k hk Mk hMk B S e (currentWeight t) (currentMeasurable t) (currentBound t)
      (ae_of_all _ (currentBounded t)) (direction t)
  hardMarginal := PhysicalRemovalMarginal.hardMarginal B volume BF κ
  prepareMarginal := prepareMarginal
  marginal := fullMarginal B volume
  hardTarget := photonCoordinates B (hardTargetTrace BF κ B volume m.val)
  tests := {
    density t := source.gaussianDensityTest BF κ W (densityWeight t) (densityMeasurable t)
      (densityBound t) (densityNonneg t) (densityBounded t)
    direction := direction
    current t := source.gaussianCurrentTest BF κ W C k hk Mk hMk S e m.property.2.2
      (currentWeight t) (currentMeasurable t) (currentBound t) (currentBounded t) (direction t)
    hardTests := realCoordinateTests
    hard := hardTests.hard
    separating := hardTests.separating
    hard_rankOne := hardTests.hard_rankOne }
  density_rankOne t v := boundedTrace_multiplier_rankOne
    (B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2
      (volume : Measure (Position (Fin N × Fin 3))))).functional
      (densityWeight t) (densityMeasurable t) (densityBound t)
        (ae_of_all _ (densityBounded t)) v
  canonical := hardCanonicalCurrent N c hc C h hh Mh hMh B S BF κ e currentWeight
    currentMeasurable currentBound (fun t => ae_of_all _ (currentBounded t)) direction
  currentBound t := testedCurrentCoefficient (Fin N × Fin 3)
    (fun x => c * PhysicalCoulombH1.potential N x) C h hh Mh hMh e
      (currentWeight t) (currentMeasurable t) (currentBound t)
        (ae_of_all _ (currentBounded t)) (direction t)
  currentBound_nonneg t := testedCurrentCoefficient_nonneg (Fin N × Fin 3)
    (fun x => c * PhysicalCoulombH1.potential N x) C h hh Mh hMh e
      (currentWeight t) (currentMeasurable t) (currentBound t)
        (ae_of_all _ (currentBounded t)) (direction t)
  current_bound t n x hx he := hardTestedCurrent_approximation_bound N c C h hh Mh hMh B S BF κ e
    currentWeight currentMeasurable currentBound (fun t => ae_of_all _ (currentBounded t))
      direction t n x hx he
  marginalTests := PhysicalRemovalMarginal.tests
  marginalOperator := hardOperator B BF κ
  separate := tests_separate
  marginal_rankOne := hardMarginal_rankOne B volume BF κ
  density_vacuum t v := PhysicalPFVacuumInsertion.density_rankOne volume B (hardPhotonVacuumEmbedding BF κ)
    (densityWeight t) (densityMeasurable t) (densityBound t)
      (ae_of_all _ (densityBounded t)) v
  current_vacuum t v hv := inserted_current_eq (Fin N × Fin 3)
    (fun x => c * PhysicalCoulombH1.potential N x) C k h s hk hh hs Mk Mh Ms hMk hMh hMs hsplit
      B S BF κ e hsoft (currentWeight t) (currentMeasurable t) (currentBound t)
        (ae_of_all _ (currentBounded t)) (direction t) v hv
  marginal_vacuum := PhysicalRemovalMarginal.marginal_vacuum B volume BF κ
  fullCurrentBound t := testedCurrentCoefficient (Fin N × Fin 3)
    (fun x => c * PhysicalCoulombH1.potential N x) C k hk Mk hMk e
      (currentWeight t) (currentMeasurable t) (currentBound t)
        (ae_of_all _ (currentBounded t)) (direction t)
  fullCurrentBound_nonneg t := testedCurrentCoefficient_nonneg (Fin N × Fin 3)
    (fun x => c * PhysicalCoulombH1.potential N x) C k hk Mk hMk e
      (currentWeight t) (currentMeasurable t) (currentBound t)
        (ae_of_all _ (currentBounded t)) (direction t)
  full_current_bound t n x hx he := testedCurrent_approximation_bound (Fin N × Fin 3)
    (fun x => c * PhysicalCoulombH1.potential N x) C k hk Mk hMk B S e
      (currentWeight t) (currentMeasurable t) (currentBound t)
        (ae_of_all _ (currentBounded t)) (direction t) n x hx he
  original_energy := source.gaussianLattice_energy C k hk Mk hMk S e BF κ W
    m.property.2.2 m.property.2.1
  softForm := fullForm B volume (NormalPhoton.softEnergyForm (B.normal (H := PhotonFock))
    (B.realization PhotonFock).functional κ)
  vacuum_zero := insertion_rankOne_softEnergy volume B BF κ

/-- All hard spectral tests are constructed from the actual positive source. -/
def physicalLatticeObservableData
    (m : (normalEnergy (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
      C k hk Mk hMk B S e).State)
    (source : Source (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x) B m.val) :=
  latticeObservableData N c hc C k h s hk hh hs Mk Mh Ms hMk hMh hMs hsplit B S BF κ e W hsoft
    densityWeight densityMeasurable densityBound densityNonneg densityBounded
    currentWeight currentMeasurable currentBound currentBounded direction m source
    (gaussianOriginalHardTests B volume BF κ W
      (fun n => inclusion (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
        (source.vector n)) m.property.1 source.hasSum)

end GptLean.PhysicalRemovalObservables
