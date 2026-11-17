import GptLean.PhysicalGaussianPFGraphs
import GptLean.PhysicalRemovalPair
import GptLean.PhysicalRemovalVacuum
import GptLean.PhysicalRemovalFermions
import GptLean.PhysicalRemovalNumber
import GptLean.AttainmentPhysicalRemoval

/-!
All inputs of lattice infrared removal are instantiated on the actual
Pauli--Fierz normal state. The remaining parameters are the article
cutoff and universal analytic backgrounds. No removal conclusion,
source graph matching, marginal formula, or vacuum estimate is assumed.
-/

noncomputable section
namespace GptLean.PhysicalRemoval

open MeasureTheory Filter PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalGaussianCoordinates PhysicalPolarization
  PhysicalPFSource PhysicalPFVacuumInsertion PhysicalPFVacuumEnergy
  PhysicalRemovalKernels PhysicalRemovalMarginal PhysicalPairSpace
  RemovalSource RemovalEnergy RemovalConstraints Gaussian SymmetricLift
  AttainmentPhysicalRemoval
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] PhysicalPolarization.softPhotonHardNormedAddCommGroup
  PhysicalPolarization.softPhotonHardRealNormedSpace

local instance hardMeasurable (κ : ℝ) : MeasurableSpace (HardPhotonFock κ) := borel _
local instance hardBorel (κ : ℝ) : BorelSpace (HardPhotonFock κ) := ⟨rfl⟩
local instance hardPairMeasurable (κ : ℝ) :
    MeasurableSpace (WithLp 2 (HardPhotonFock κ × HardPhotonFock κ)) := borel _
local instance hardPairBorel (κ : ℝ) :
    BorelSpace (WithLp 2 (HardPhotonFock κ × HardPhotonFock κ)) := ⟨rfl⟩

section ScalarIntertwining

variable {N : ℕ} (BF : StandardSymmetricFockExponential) (κ : ℝ)
  {J : RealStructure (softOnePhoton κ)}
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)

local instance removalScalarPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance removalScalarHardDirectInner : InnerProductSpace ℂ (HardPhotonFock κ) :=
  { (inferInstance : InnerProductSpace ℂ (HardPhotonFock κ)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (HardPhotonFock κ)) }

attribute [local irreducible] photonGaussianSource photonGaussianUnitary productSource productUnitary

set_option backward.isDefEq.respectTransparency.types true in
private theorem photonSource_scalar :
    SpatialScalarIntertwining (X := Configuration N) (Q := W.space.Q)
      (H := PhotonFock) (K := HardPhotonFock κ)
      (μ := W.space.measure) (ν := (volume : Measure (Configuration N)))
      (photonGaussianSource BF κ W N) := by
  unfold photonGaussianSource
  exact productSource_scalar (X := Configuration N) (Q := W.space.Q)
    (H := PhotonFock) (K := HardPhotonFock κ)
    (volume : Measure (Configuration N)) W.space.measure (photonGaussianUnitary BF κ W)

set_option backward.isDefEq.respectTransparency.types true in
private theorem photonPairSource_scalar :
    SpatialScalarIntertwining (X := Configuration N) (Q := W.space.Q)
      (H := WithLp 2 (PhotonFock × PhotonFock))
      (K := WithLp 2 (HardPhotonFock κ × HardPhotonFock κ))
      (μ := W.space.measure) (ν := (volume : Measure (Configuration N)))
      (productSource (X := Configuration N) (Q := W.space.Q)
        (H := WithLp 2 (PhotonFock × PhotonFock))
        (K := WithLp 2 (HardPhotonFock κ × HardPhotonFock κ))
        (volume : Measure (Configuration N)) W.space.measure
        (productUnitary (H := PhotonFock) (K := HardPhotonFock κ)
          W.space.measure (photonGaussianUnitary BF κ W))) :=
  productSource_scalar (X := Configuration N) (Q := W.space.Q)
    (H := WithLp 2 (PhotonFock × PhotonFock))
    (K := WithLp 2 (HardPhotonFock κ × HardPhotonFock κ))
    (volume : Measure (Configuration N)) W.space.measure
    (productUnitary (H := PhotonFock) (K := HardPhotonFock κ)
      W.space.measure (photonGaussianUnitary BF κ W))

end ScalarIntertwining

variable {N : ℕ} (i : Fin N) (F : Frame) (χ : ArticleCutoff)
  (c : ℝ) (hc : 0 ≤ c) (C : CanonicalSectorCCR photonMeasure)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)
  (BF : StandardSymmetricFockExponential) (e κ : ℝ) (hκ : 0 ≤ κ)
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) (F.softRealStructure κ))

abbrev potential (N : ℕ) (c : ℝ) : Configuration N → ℝ :=
  fun x => c * PhysicalCoulombH1.potential N x

abbrev fullEnergy := normalEnergy (Fin N × Fin 3) (potential N c) C
  (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e

def observables (m : (fullEnergy F χ c C B S e (N := N)).State)
    (source : Source (Fin N × Fin 3) (potential N c) B m.val) :=
  PhysicalRemovalObservables.physicalLatticeObservableData N c hc C
    (full F χ N) (hard F χ N κ) (soft F χ N κ)
    (full_measurable F χ N) (hard_measurable F χ N κ) (soft_measurable F χ N κ)
    (bound F χ) (bound F χ) (bound F χ)
    (full_bound F χ N) (hard_bound F χ N κ) (soft_bound F χ N κ)
    (fun j => ae_of_all _ (full_eq_hard_add_soft F χ N κ j)) B S BF κ e W
    (fun j => ae_of_all _ fun x => WeightedPhotonKernel.soft_fst_mem_hard_orthogonal κ
      (full F χ N j x))
    (PhysicalRemovalPair.densityWeight N i) (PhysicalRemovalPair.densityWeight_measurable N i)
    (fun _ => (N : ℝ)) (fun _ => Nat.cast_nonneg N) (PhysicalRemovalPair.densityWeight_bound N i)
    (PhysicalRemovalPair.currentWeight N i) (PhysicalRemovalPair.currentWeight_measurable N i)
    (fun _ => 1) (PhysicalRemovalPair.currentWeight_bound N i)
    (PhysicalRemovalPair.direction N i) m source

variable (core : CountableSpatialTestCore) (smooth : SmoothSobolevBackground)
  (C₀ : ℝ) (scaled : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C₀)
  (B₀ : TensorBackground Repair.SixTag) (B₁ : TensorMultilinearData B₀)
  {ι : Type*} (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target) (index : ι ↪ ℕ)

/-- The original source, fields, observables and vacuum all use the same
physical kernels and normal state. -/
def latticeInput (m : (fullEnergy F χ c C B S e (N := N)).State)
    (source : Source (Fin N × Fin 3) (potential N c) B m.val)
    (hcharacter : ∀ n, Repair.HasElectronicCharacter
      (fun π => permuteConfiguration π) (PhysicalElectronicFermions.signCharacter N)
        (inclusion (Fin N × Fin 3) (potential N c) (source.vector n))) :
    LatticeRemovalInput (Q := W.space.Q) (Ω := PhotonMode) (G := DerivativeLabel)
      (Ho := PhotonFock) (H := HardPhotonFock κ)
      (Hr := WithLp 2 (PhotonFock × PhotonFock))
      (F := WithLp 2 (HardPhotonFock κ × HardPhotonFock κ))
      (T := B.Trace (Lp (HardPhotonFock κ) 2 (volume : Measure (Configuration N))))
      (Hfull := WaveSpace (Fin N × Fin 3)) (Marginal := Marginal) (HardMarginal := Marginal)
      (DensityTest := SpatialTest) (CurrentTest := Fin 3 × SpatialTest) (ι := ι)
      (Qv := W.space.Q) (Hv := PhotonFock) (Kv := HardPhotonFock κ) (Gv := DerivativeLabel)
      (μ := W.space.measure) (ν := photonMeasure) (μv := W.space.measure)
      (ρMeasure := (volume : Measure FieldSpace)) (N := N)
      (B.traceData (H := WaveSpace (Fin N × Fin 3))) (fullEnergy F χ c C B S e) m
      (B.fermionicCompression N) κ e C₀ (χ.removalA κ) (χ.removalB κ) where
  src := source.gaussianLattice C (full F χ N) (full_measurable F χ N)
    (bound F χ) (full_bound F χ N) S e BF κ W m.property.2.2 m.property.2.1
  W := spatialWienerSegal F χ κ hκ BF C W volume
  weight p := 1 / ‖p.1‖
  D := spatialKernelFieldData F χ κ hκ BF C W volume B.normal (B.realization PhotonFock).functional
  momentum := Prod.fst
  scaledSobolev := scaled
  label := removalLabel
  spatial := removalSpatialData F χ κ hκ BF C W B.normal
    (B.realization PhotonFock).functional N core smooth
  Fubini := PhysicalSourceFubini.curryEquiv
  hrep v := by
    filter_upwards [PhysicalSourceFubini.curryEquiv_represents_ae v] with q hq
    exact hq.symm
  hW := photonGaussian_source_fubini BF κ W N
  locality := spatialKernelFieldData_locality F χ κ hκ BF C W volume B.normal
    (B.realization PhotonFock).functional
  hdom n := ⟨radiationSource (Fin N × Fin 3) (potential N c) (source.vector n),
    radiation_matches (Fin N × Fin 3) (potential N c) (source.vector n)⟩
  hrad n := by
    have h := spatialGraphApply_of_graph (volume : Measure (Configuration N))
      (softRadiationRoot κ) (radiationSource (Fin N × Fin 3) (potential N c) (source.vector n))
    exact (congrArg (spatialGraphApply (volume : Measure (Configuration N))
      (softRadiationRoot κ)) (radiation_matches (Fin N × Fin 3) (potential N c)
        (source.vector n))).symm.trans h
  hU := photonSource_scalar (N := N) BF κ W
  hUr := photonPairSource_scalar (N := N) BF κ W
  B₀ := B₀
  B₁ := B₁
  basis := basis
  index := index
  Rrad := hardRadiationOperator κ
  A j x := hardFieldOperator κ (hard F χ N κ j x).val.1
  B x := hardRestOperator κ (Real.sqrt (potential N c x) : ℂ)
  R₁ := (B.realization (Lp (HardPhotonFock κ) 2 (volume : Measure (Configuration N)))).rank
  Tr := B.traceData (H := Lp (HardPhotonFock κ) 2 (volume : Measure (Configuration N)))
  E := hardEnergy (Fin N × Fin 3) (potential N c) C (hard F χ N κ)
    (hard_measurable F χ N κ) (bound F χ) (hard_bound F χ N κ) B S BF κ e
  sourcePF := source.gaussianPFData F χ κ hκ BF C W
    (removalSpatialData F χ κ hκ BF C W B.normal
      (B.realization PhotonFock).functional N core smooth).field S e
    m.property.2.2 m.property.2.1
    ((PhysicalCoulombH1.potential_measurable N).stronglyMeasurable.const_mul c)
  hform := PhysicalPFFormEvaluation.hardFormEvaluation (Fin N × Fin 3) (potential N c) C
    (hard F χ N κ) (hard_measurable F χ N κ) (bound F χ) (hard_bound F χ N κ) B S BF κ e
  hpositive := fun _ h => h
  htrace := rfl
  Rfull := (B.realization (WaveSpace (Fin N × Fin 3))).rank
  vacuum := insertion volume BF κ
  hpositiveFull := fun _ h => h
  htraceFull := rfl
  Wv := photonWienerSegal F χ κ hκ BF C W
  Dv := photonKernelFieldData F χ κ hκ BF C W B.normal (B.realization PhotonFock).functional
  labelV j x := removalLabel j [] x
  hkernelV _ _ := rfl
  vac := photonVacuum
  hVac := photonVacuum_norm
  hVacDomain := photonVacuum_radiationDomain
  hVacZero := photonVacuum_softRadiation_zero κ
  hVacOrth j x := photonVacuum_field_inner_zero F χ κ hκ BF C W (removalLabel j [] x)
  vacuumForms := PhysicalRemovalVacuum.articleVacuumFormData F χ N (potential N c) C B S BF κ hκ e W
  obs := observables i F χ c hc C B S BF e κ W m source
  χ := PhysicalElectronicFermions.signCharacter N
  hperm := photonGaussianSource_permutation N BF κ W
  hcharacter := hcharacter
  hcompression := insertion_compression N B BF κ
  pair := PhysicalRemovalPair.pairData N i (potential N c) C (full F χ N)
    (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e
  originalSoft := source.gaussianLattice_soft C (full F χ N) (full_measurable F χ N)
    (bound F χ) (full_bound F χ N) S e BF κ W m.property.2.2 m.property.2.1

end GptLean.PhysicalRemoval
