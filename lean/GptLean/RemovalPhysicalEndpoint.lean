import GptLean.RemovalLatticeOutput
import GptLean.RemovalLatticeFermionic
import GptLean.RemovalPhysicalConclusion
import GptLean.RemovalPhysicalSoftEnergy
import GptLean.RemovalGaussianCharacter
import GptLean.RemovalSourceSymmetry
import GptLean.RemovalOriginalOutputState
import GptLean.RemovalLatticeOriginalSource
import GptLean.RemovalGaussianLatticeSource
import GptLean.RemovalLatticePF
import GptLean.RemovalLatticeCoreData
import GptLean.RemovalGaussianLink
import GptLean.RemovalVacuumPhysical

/-!
The same exact-removal output is assembled from the original spectral
vectors, actual lattice localization, a first-chaos spatial field and the
soft-Fock vacuum. The local Gaussian moment, localization cost, physical
channel, canonical current link and vacuum energy error are conclusions
of the component constructions rather than inputs to this endpoint.
-/

noncomputable section

namespace GptLean.RemovalEnergy

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

open MeasureTheory Filter Gaussian RemovalSource RemovalState RemovalGeometry
  RemovalConstruction RemovalConstraints Repair SymmetricLift
open scoped ENNReal ContDiff

section Assembly

variable {Q Ω G Ho H Hr F T Hfull Tfull Marginal HardMarginal DensityTest CurrentTest ι : Type*}
  [MeasurableSpace Q] [MeasurableSpace Ω] {μ : Measure Q} {ν : Measure Ω}
  [IsProbabilityMeasure μ] [SFinite ν] [IsSeparable ν] {N : ℕ}
  [NormedAddCommGroup Ho] [InnerProductSpace ℂ Ho]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup Hfull] [InnerProductSpace ℂ Hfull]
  [NormedAddCommGroup Tfull] [NormedSpace ℝ Tfull] [CompleteSpace Tfull]
  [NormedAddCommGroup Marginal] [NormedSpace ℝ Marginal] [CompleteSpace Marginal]
  [NormedAddCommGroup HardMarginal] [NormedSpace ℝ HardMarginal] [CompleteSpace HardMarginal]
  {Qv Hv Kv Gv : Type*} [MeasurableSpace Qv] {μv : Measure Qv}
  [NormedAddCommGroup Hv] [InnerProductSpace ℂ Hv]
  [NormedAddCommGroup Kv] [NormedSpace ℝ Kv]

variable {X : Type*} [MeasurableSpace X] {ρMeasure : Measure X}

theorem latticeRemovalConstant_nonneg (N : ℕ) (C : ℝ) : 0 ≤ latticeRemovalConstant N C := by
  apply removalConstant_nonneg
  unfold latticeIMSConstant
  exact mul_nonneg (by positivity) LatticePartition.metricConstant_pos.le

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace F] [BorelSpace F] in
theorem lattice_physical_removal_ofPFData
    (src : LatticeSourceData N μ Ho H Hr F Ho)
    (W : WienerSegalData Q (Lp Ho 2 (volume : Measure (Configuration N)))
      (Lp H 2 (volume : Measure (Configuration N))) G μ)
    {weight : Ω → ℝ} (D : KernelFieldData ν W weight)
    (momentum : Ω → FieldSpace) {k R e C acut bcut : ℝ}
    (hR : 0 < R) (he : 0 ≤ e) (hC : 0 ≤ C) (hkR : k * R ≤ 1)
    (scaledSobolev : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C)
    (label : Fin 3 → List (Fin 3) → FieldSpace → G)
    (spatial : LatticeSpatialData W D momentum k acut bcut label)
    (Fubini : Lp H 2 (μ.prod (volume : Measure (Configuration N))) ≃ₗᵢ[ℂ]
      Lp (Lp H 2 (volume : Measure (Configuration N))) 2 μ)
    (hrep : ∀ v : Lp H 2 (μ.prod (volume : Measure (Configuration N))), ∀ᵐ q ∂μ,
      (fun x => v (q, x)) =ᵐ[volume] (fun x => Fubini v q x))
    (hW : ∀ v, W.toFiber v =ᵐ[μ] (fun q => Fubini (src.U v) q))
    (locality : SpatialRadiationLocality D.radiationDomain D.radiation)
    (hdom : ∀ n, D.radiationDomain (src.ψ n))
    (hrad : ∀ n, D.radiation (src.ψ n) = src.soft n)
    (hU : SpatialScalarIntertwining src.U) (hUr : SpatialScalarIntertwining src.Ur)
    (B₀ : TensorBackground SixTag) (B₁ : TensorMultilinearData B₀)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target) (index : ι ↪ ℕ)
    (Rrad : H →ₗ.[ℂ] H) (A : (Fin N × Fin 3) → Configuration N → H →ₗ.[ℂ] H)
    (B : Configuration N → H →ₗ.[ℂ] F)
    (R₁ : RankOneData (Lp H 2 (volume : Measure (Configuration N))) T)
    (Tr : PositiveTraceData T) (E : PositiveForm Tr)
    (sourcePF : src.original.PFData Rrad A B e
      (fun _ j qx => vectorField spatial.field.field [] qx.1 (particle qx.2 j.1) j.2))
    (hform : HasPFFormEvaluation Rrad A B e (fun v => E.expectation (R₁.rankOne v)))
    (hpositive : R₁.positive ⊆ Tr.positive) (htrace : R₁.trace = Tr.trace)
    (Rfull : RankOneData Hfull Tfull) (Trfull : PositiveTraceData Tfull)
    (Efull : PositiveForm Trfull)
    (vacuum : Lp H 2 (volume : Measure (Configuration N)) →ₗᵢ[ℂ] Hfull)
    (hpositiveFull : Rfull.positive ⊆ Trfull.positive) (htraceFull : Rfull.trace = Trfull.trace)
    (Wv : WienerSegalData Qv Hv Kv Gv μv) (Dv : KernelFieldData ν Wv weight)
    (labelV : Fin 3 → FieldSpace → Gv)
    (hkernelV : ∀ i x, Dv.kernel (labelV i x) =
      softDerivativeKernel momentum [] k x (spatial.kernels.base i))
    (vac : Hv) (hVac : ‖vac‖ = 1) (hVacDomain : Dv.radiationDomain vac)
    (hVacZero : Dv.radiation vac = 0)
    (hVacOrth : ∀ i x, inner ℂ vac (Wv.field (labelV i x) vac) = 0)
    (vacuumForms : RemovalVacuum.VacuumFormData R₁ Tr E Rfull Trfull Efull vacuum vac
      (fun (j : Fin N × Fin 3) x => Wv.field (labelV j.2 (particle x j.1)) vac) e)
    (m : Efull.State)
    (obs : LatticeObservableData src R₁ Tr E Rfull Trfull Efull Rrad A e vacuum m
      DensityTest CurrentTest Marginal HardMarginal)
    (χ : Equiv.Perm (Fin N) → ℂ)
    (hperm : SpatialPermutationIntertwining src.U)
    (hcharacter : ∀ n, HasElectronicCharacter (fun π => permuteConfiguration π) χ (src.ψ n))
    (compression : Tfull →L[ℝ] Tfull)
    (hcompression : ∀ v : Lp H 2 (volume : Measure (Configuration N)),
      HasElectronicCharacter (fun π => permuteConfiguration π) χ v →
        compression (Rfull.rankOne (vacuum v)) = Rfull.rankOne (vacuum v))
    (pair : PhysicalPairData obs.density obs.current ρMeasure (Fin N) (Fin 3))
    (originalSoft : obs.softForm.expectation m.val = ENNReal.ofReal (∑' n, ‖src.soft n‖ ^ 2)) :
    obs.softForm.expectation m.val < ⊤ ∧
    PhysicalRemovalConclusion pair m (lattice_exactOutput_ofPFData src W D momentum hR he hC hkR scaledSobolev label spatial
      Fubini hrep hW locality hdom hrad hU hUr B₀ B₁ basis index Rrad A B R₁ Tr E sourcePF
      hform hpositive htrace Rfull Trfull Efull vacuum hpositiveFull htraceFull
      Wv Dv labelV hkernelV vac hVac hVacDomain hVacZero hVacOrth vacuumForms m obs).val.state
      (fun s => obs.marginal s.val) (obs.prepareMarginal obs.hardTarget) obs.softForm
      (obs.softForm.expectation m.val).toReal
      (latticeRemovalConstant N C * RemovalEstimates.scaleError e k R bcut
        (acut ^ 2 * (obs.softForm.expectation m.val).toReal + bcut ^ 2)) ∧
    compression (lattice_exactOutput_ofPFData src W D momentum hR he hC hkR scaledSobolev label spatial
      Fubini hrep hW locality hdom hrad hU hUr B₀ B₁ basis index Rrad A B R₁ Tr E sourcePF
      hform hpositive htrace Rfull Trfull Efull vacuum hpositiveFull htraceFull
      Wv Dv labelV hkernelV vac hVac hVacDomain hVacZero hVacOrth vacuumForms m obs).val.state.val = (lattice_exactOutput_ofPFData src W D momentum hR he hC hkR scaledSobolev label spatial
      Fubini hrep hW locality hdom hrad hU hUr B₀ B₁ basis index Rrad A B R₁ Tr E sourcePF
      hform hpositive htrace Rfull Trfull Efull vacuum hpositiveFull htraceFull
      Wv Dv labelV hkernelV vac hVac hVacDomain hVacZero hVacOrth vacuumForms m obs).val.state.val := by
  let out := lattice_exactOutput_ofPFData src W D momentum hR he hC hkR scaledSobolev label spatial
      Fubini hrep hW locality hdom hrad hU hUr B₀ B₁ basis index Rrad A B R₁ Tr E sourcePF
      hform hpositive htrace Rfull Trfull Efull vacuum hpositiveFull htraceFull
      Wv Dv labelV hkernelV vac hVac hVacDomain hVacZero hVacOrth vacuumForms m obs
  obtain ⟨hfinite, hsoft⟩ := spectral_soft_energy_identification
    (fun s : Efull.State => obs.softForm.expectation s.val) m src.soft originalSoft
  refine ⟨hfinite, ?_, ?_⟩
  · have h := pair.exactOutput_conclusion out (latticeRemovalConstant_nonneg N C) he spatial.nonnegative
    simpa only [hsoft] using h
  · exact lattice_exactOutput_fixed_ofPFData src W D momentum hR he hC hkR scaledSobolev label spatial
      Fubini hrep hW locality hdom hrad hU hUr B₀ B₁ basis index Rrad A B R₁ Tr E sourcePF
      hform hpositive htrace Rfull Trfull Efull vacuum hpositiveFull htraceFull
      Wv Dv labelV hkernelV vac hVac hVacDomain hVacZero hVacOrth vacuumForms m obs χ hperm hcharacter compression hcompression

/-- Compatibility entry point for universal core descriptions. -/
theorem lattice_physical_removal
    (src : LatticeSourceData N μ Ho H Hr F Ho)
    (W : WienerSegalData Q (Lp Ho 2 (volume : Measure (Configuration N)))
      (Lp H 2 (volume : Measure (Configuration N))) G μ)
    {weight : Ω → ℝ} (D : KernelFieldData ν W weight)
    (momentum : Ω → FieldSpace) {k R e C acut bcut : ℝ}
    (hR : 0 < R) (he : 0 ≤ e) (hC : 0 ≤ C) (hkR : k * R ≤ 1)
    (scaledSobolev : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C)
    (label : Fin 3 → List (Fin 3) → FieldSpace → G)
    (spatial : LatticeSpatialData W D momentum k acut bcut label)
    (Fubini : Lp H 2 (μ.prod (volume : Measure (Configuration N))) ≃ₗᵢ[ℂ]
      Lp (Lp H 2 (volume : Measure (Configuration N))) 2 μ)
    (hrep : ∀ v : Lp H 2 (μ.prod (volume : Measure (Configuration N))), ∀ᵐ q ∂μ,
      (fun x => v (q, x)) =ᵐ[volume] (fun x => Fubini v q x))
    (hW : ∀ v, W.toFiber v =ᵐ[μ] (fun q => Fubini (src.U v) q))
    (locality : SpatialRadiationLocality D.radiationDomain D.radiation)
    (hdom : ∀ n, D.radiationDomain (src.ψ n))
    (hrad : ∀ n, D.radiation (src.ψ n) = src.soft n)
    (hU : SpatialScalarIntertwining src.U) (hUr : SpatialScalarIntertwining src.Ur)
    (B₀ : TensorBackground SixTag) (B₁ : TensorMultilinearData B₀)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target) (index : ι ↪ ℕ)
    (Rrad : H →ₗ.[ℂ] H) (A : (Fin N × Fin 3) → Configuration N → H →ₗ.[ℂ] H)
    (B : Configuration N → H →ₗ.[ℂ] F)
    (R₁ : RankOneData (Lp H 2 (volume : Measure (Configuration N))) T)
    (Tr : PositiveTraceData T) (E : PositiveForm Tr)
    (sourceCores : LatticePFCoreData src Rrad A B e
      (fun j qx => vectorField spatial.field.field [] qx.1 (particle qx.2 j.1) j.2))
    (hform : HasPFFormEvaluation Rrad A B e (fun v => E.expectation (R₁.rankOne v)))
    (hpositive : R₁.positive ⊆ Tr.positive) (htrace : R₁.trace = Tr.trace)
    (Rfull : RankOneData Hfull Tfull) (Trfull : PositiveTraceData Tfull)
    (Efull : PositiveForm Trfull)
    (vacuum : Lp H 2 (volume : Measure (Configuration N)) →ₗᵢ[ℂ] Hfull)
    (hpositiveFull : Rfull.positive ⊆ Trfull.positive) (htraceFull : Rfull.trace = Trfull.trace)
    (Wv : WienerSegalData Qv Hv Kv Gv μv) (Dv : KernelFieldData ν Wv weight)
    (labelV : Fin 3 → FieldSpace → Gv)
    (hkernelV : ∀ i x, Dv.kernel (labelV i x) =
      softDerivativeKernel momentum [] k x (spatial.kernels.base i))
    (vac : Hv) (hVac : ‖vac‖ = 1) (hVacDomain : Dv.radiationDomain vac)
    (hVacZero : Dv.radiation vac = 0)
    (hVacOrth : ∀ i x, inner ℂ vac (Wv.field (labelV i x) vac) = 0)
    (vacuumForms : RemovalVacuum.VacuumFormData R₁ Tr E Rfull Trfull Efull vacuum vac
      (fun (j : Fin N × Fin 3) x => Wv.field (labelV j.2 (particle x j.1)) vac) e)
    (m : Efull.State)
    (obs : LatticeObservableData src R₁ Tr E Rfull Trfull Efull Rrad A e vacuum m
      DensityTest CurrentTest Marginal HardMarginal)
    (χ : Equiv.Perm (Fin N) → ℂ)
    (hperm : SpatialPermutationIntertwining src.U)
    (hcharacter : ∀ n, HasElectronicCharacter (fun π => permuteConfiguration π) χ (src.ψ n))
    (compression : Tfull →L[ℝ] Tfull)
    (hcompression : ∀ v : Lp H 2 (volume : Measure (Configuration N)),
      HasElectronicCharacter (fun π => permuteConfiguration π) χ v →
        compression (Rfull.rankOne (vacuum v)) = Rfull.rankOne (vacuum v))
    (pair : PhysicalPairData obs.density obs.current ρMeasure (Fin N) (Fin 3))
    (originalSoft : obs.softForm.expectation m.val = ENNReal.ofReal (∑' n, ‖src.soft n‖ ^ 2)) :
    obs.softForm.expectation m.val < ⊤ ∧
    PhysicalRemovalConclusion pair m (lattice_exactOutput src W D momentum hR he hC hkR scaledSobolev label spatial
      Fubini hrep hW locality hdom hrad hU hUr B₀ B₁ basis index Rrad A B R₁ Tr E sourceCores
      hform hpositive htrace Rfull Trfull Efull vacuum hpositiveFull htraceFull
      Wv Dv labelV hkernelV vac hVac hVacDomain hVacZero hVacOrth vacuumForms m obs).val.state
      (fun s => obs.marginal s.val) (obs.prepareMarginal obs.hardTarget) obs.softForm
      (obs.softForm.expectation m.val).toReal
      (latticeRemovalConstant N C * RemovalEstimates.scaleError e k R bcut
        (acut ^ 2 * (obs.softForm.expectation m.val).toReal + bcut ^ 2)) ∧
    compression (lattice_exactOutput src W D momentum hR he hC hkR scaledSobolev label spatial
      Fubini hrep hW locality hdom hrad hU hUr B₀ B₁ basis index Rrad A B R₁ Tr E sourceCores
      hform hpositive htrace Rfull Trfull Efull vacuum hpositiveFull htraceFull
      Wv Dv labelV hkernelV vac hVac hVacDomain hVacZero hVacOrth vacuumForms m obs).val.state.val = (lattice_exactOutput src W D momentum hR he hC hkR scaledSobolev label spatial
      Fubini hrep hW locality hdom hrad hU hUr B₀ B₁ basis index Rrad A B R₁ Tr E sourceCores
      hform hpositive htrace Rfull Trfull Efull vacuum hpositiveFull htraceFull
      Wv Dv labelV hkernelV vac hVac hVacDomain hVacZero hVacOrth vacuumForms m obs).val.state.val := by
  exact lattice_physical_removal_ofPFData src W D momentum hR he hC hkR scaledSobolev label spatial
    Fubini hrep hW locality hdom hrad hU hUr B₀ B₁ basis index Rrad A B R₁ Tr E sourceCores.toPFData
    hform hpositive htrace Rfull Trfull Efull vacuum hpositiveFull htraceFull
    Wv Dv labelV hkernelV vac hVac hVacDomain hVacZero hVacOrth vacuumForms m obs χ hperm hcharacter compression hcompression pair originalSoft

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace F] [BorelSpace F] in
theorem lattice_physical_removal_optimized_ofPFData
    (src : LatticeSourceData N μ Ho H Hr F Ho)
    (W : WienerSegalData Q (Lp Ho 2 (volume : Measure (Configuration N)))
      (Lp H 2 (volume : Measure (Configuration N))) G μ)
    {weight : Ω → ℝ} (D : KernelFieldData ν W weight)
    (momentum : Ω → FieldSpace) {k e C acut bcut : ℝ}
    (he : 0 ≤ e) (hC : 0 ≤ C) (hk : 0 < k) (hk1 : k ≤ 1)
    (scaledSobolev : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C)
    (label : Fin 3 → List (Fin 3) → FieldSpace → G)
    (spatial : LatticeSpatialData W D momentum k acut bcut label)
    (Fubini : Lp H 2 (μ.prod (volume : Measure (Configuration N))) ≃ₗᵢ[ℂ]
      Lp (Lp H 2 (volume : Measure (Configuration N))) 2 μ)
    (hrep : ∀ v : Lp H 2 (μ.prod (volume : Measure (Configuration N))), ∀ᵐ q ∂μ,
      (fun x => v (q, x)) =ᵐ[volume] (fun x => Fubini v q x))
    (hW : ∀ v, W.toFiber v =ᵐ[μ] (fun q => Fubini (src.U v) q))
    (locality : SpatialRadiationLocality D.radiationDomain D.radiation)
    (hdom : ∀ n, D.radiationDomain (src.ψ n))
    (hrad : ∀ n, D.radiation (src.ψ n) = src.soft n)
    (hU : SpatialScalarIntertwining src.U) (hUr : SpatialScalarIntertwining src.Ur)
    (B₀ : TensorBackground SixTag) (B₁ : TensorMultilinearData B₀)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target) (index : ι ↪ ℕ)
    (Rrad : H →ₗ.[ℂ] H) (A : (Fin N × Fin 3) → Configuration N → H →ₗ.[ℂ] H)
    (B : Configuration N → H →ₗ.[ℂ] F)
    (R₁ : RankOneData (Lp H 2 (volume : Measure (Configuration N))) T)
    (Tr : PositiveTraceData T) (E : PositiveForm Tr)
    (sourcePF : src.original.PFData Rrad A B e
      (fun _ j qx => vectorField spatial.field.field [] qx.1 (particle qx.2 j.1) j.2))
    (hform : HasPFFormEvaluation Rrad A B e (fun v => E.expectation (R₁.rankOne v)))
    (hpositive : R₁.positive ⊆ Tr.positive) (htrace : R₁.trace = Tr.trace)
    (Rfull : RankOneData Hfull Tfull) (Trfull : PositiveTraceData Tfull)
    (Efull : PositiveForm Trfull)
    (vacuum : Lp H 2 (volume : Measure (Configuration N)) →ₗᵢ[ℂ] Hfull)
    (hpositiveFull : Rfull.positive ⊆ Trfull.positive) (htraceFull : Rfull.trace = Trfull.trace)
    (Wv : WienerSegalData Qv Hv Kv Gv μv) (Dv : KernelFieldData ν Wv weight)
    (labelV : Fin 3 → FieldSpace → Gv)
    (hkernelV : ∀ i x, Dv.kernel (labelV i x) =
      softDerivativeKernel momentum [] k x (spatial.kernels.base i))
    (vac : Hv) (hVac : ‖vac‖ = 1) (hVacDomain : Dv.radiationDomain vac)
    (hVacZero : Dv.radiation vac = 0)
    (hVacOrth : ∀ i x, inner ℂ vac (Wv.field (labelV i x) vac) = 0)
    (vacuumForms : RemovalVacuum.VacuumFormData R₁ Tr E Rfull Trfull Efull vacuum vac
      (fun (j : Fin N × Fin 3) x => Wv.field (labelV j.2 (particle x j.1)) vac) e)
    (m : Efull.State)
    (obs : LatticeObservableData src R₁ Tr E Rfull Trfull Efull Rrad A e vacuum m
      DensityTest CurrentTest Marginal HardMarginal)
    (χ : Equiv.Perm (Fin N) → ℂ)
    (hperm : SpatialPermutationIntertwining src.U)
    (hcharacter : ∀ n, HasElectronicCharacter (fun π => permuteConfiguration π) χ (src.ψ n))
    (compression : Tfull →L[ℝ] Tfull)
    (hcompression : ∀ v : Lp H 2 (volume : Measure (Configuration N)),
      HasElectronicCharacter (fun π => permuteConfiguration π) χ v →
        compression (Rfull.rankOne (vacuum v)) = Rfull.rankOne (vacuum v))
    (pair : PhysicalPairData obs.density obs.current ρMeasure (Fin N) (Fin 3))
    (originalSoft : obs.softForm.expectation m.val = ENNReal.ofReal (∑' n, ‖src.soft n‖ ^ 2)) :
    obs.softForm.expectation m.val < ⊤ ∧
    ∃ r : Efull.State,
      PhysicalRemovalConclusion pair m r (fun s => obs.marginal s.val)
        (obs.prepareMarginal obs.hardTarget) obs.softForm (obs.softForm.expectation m.val).toReal
        ((3 * latticeRemovalConstant N C) *
          SoftPurification.removalError e k acut bcut (obs.softForm.expectation m.val).toReal) ∧
      compression r.val = r.val := by
  obtain ⟨hfinite, hsoft⟩ := spectral_soft_energy_identification
    (fun s : Efull.State => obs.softForm.expectation s.val) m src.soft originalSoft
  refine ⟨hfinite, ?_⟩
  rw [hsoft]
  apply pair.optimized_output_conclusion_with_property m (fun s => obs.marginal s.val)
    (obs.prepareMarginal obs.hardTarget) obs.softForm (fun r => compression r.val = r.val)
    (latticeRemovalConstant_nonneg N C) he hk hk1
  intro R hR hkR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let out := lattice_exactOutput_ofPFData src W D momentum hRpos he hC hkR scaledSobolev label spatial
      Fubini hrep hW locality hdom hrad hU hUr B₀ B₁ basis index Rrad A B R₁ Tr E sourcePF
      hform hpositive htrace Rfull Trfull Efull vacuum hpositiveFull htraceFull
      Wv Dv labelV hkernelV vac hVac hVacDomain hVacZero hVacOrth vacuumForms m obs
  exact ⟨out.val, out.property, lattice_exactOutput_fixed_ofPFData src W D momentum hRpos he hC hkR scaledSobolev label spatial
      Fubini hrep hW locality hdom hrad hU hUr B₀ B₁ basis index Rrad A B R₁ Tr E sourcePF
      hform hpositive htrace Rfull Trfull Efull vacuum hpositiveFull htraceFull
      Wv Dv labelV hkernelV vac hVac hVacDomain hVacZero hVacOrth vacuumForms m obs χ hperm hcharacter compression hcompression⟩

/-- Compatibility entry point for universal core descriptions. -/
theorem lattice_physical_removal_optimized
    (src : LatticeSourceData N μ Ho H Hr F Ho)
    (W : WienerSegalData Q (Lp Ho 2 (volume : Measure (Configuration N)))
      (Lp H 2 (volume : Measure (Configuration N))) G μ)
    {weight : Ω → ℝ} (D : KernelFieldData ν W weight)
    (momentum : Ω → FieldSpace) {k e C acut bcut : ℝ}
    (he : 0 ≤ e) (hC : 0 ≤ C) (hk : 0 < k) (hk1 : k ≤ 1)
    (scaledSobolev : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C)
    (label : Fin 3 → List (Fin 3) → FieldSpace → G)
    (spatial : LatticeSpatialData W D momentum k acut bcut label)
    (Fubini : Lp H 2 (μ.prod (volume : Measure (Configuration N))) ≃ₗᵢ[ℂ]
      Lp (Lp H 2 (volume : Measure (Configuration N))) 2 μ)
    (hrep : ∀ v : Lp H 2 (μ.prod (volume : Measure (Configuration N))), ∀ᵐ q ∂μ,
      (fun x => v (q, x)) =ᵐ[volume] (fun x => Fubini v q x))
    (hW : ∀ v, W.toFiber v =ᵐ[μ] (fun q => Fubini (src.U v) q))
    (locality : SpatialRadiationLocality D.radiationDomain D.radiation)
    (hdom : ∀ n, D.radiationDomain (src.ψ n))
    (hrad : ∀ n, D.radiation (src.ψ n) = src.soft n)
    (hU : SpatialScalarIntertwining src.U) (hUr : SpatialScalarIntertwining src.Ur)
    (B₀ : TensorBackground SixTag) (B₁ : TensorMultilinearData B₀)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target) (index : ι ↪ ℕ)
    (Rrad : H →ₗ.[ℂ] H) (A : (Fin N × Fin 3) → Configuration N → H →ₗ.[ℂ] H)
    (B : Configuration N → H →ₗ.[ℂ] F)
    (R₁ : RankOneData (Lp H 2 (volume : Measure (Configuration N))) T)
    (Tr : PositiveTraceData T) (E : PositiveForm Tr)
    (sourceCores : LatticePFCoreData src Rrad A B e
      (fun j qx => vectorField spatial.field.field [] qx.1 (particle qx.2 j.1) j.2))
    (hform : HasPFFormEvaluation Rrad A B e (fun v => E.expectation (R₁.rankOne v)))
    (hpositive : R₁.positive ⊆ Tr.positive) (htrace : R₁.trace = Tr.trace)
    (Rfull : RankOneData Hfull Tfull) (Trfull : PositiveTraceData Tfull)
    (Efull : PositiveForm Trfull)
    (vacuum : Lp H 2 (volume : Measure (Configuration N)) →ₗᵢ[ℂ] Hfull)
    (hpositiveFull : Rfull.positive ⊆ Trfull.positive) (htraceFull : Rfull.trace = Trfull.trace)
    (Wv : WienerSegalData Qv Hv Kv Gv μv) (Dv : KernelFieldData ν Wv weight)
    (labelV : Fin 3 → FieldSpace → Gv)
    (hkernelV : ∀ i x, Dv.kernel (labelV i x) =
      softDerivativeKernel momentum [] k x (spatial.kernels.base i))
    (vac : Hv) (hVac : ‖vac‖ = 1) (hVacDomain : Dv.radiationDomain vac)
    (hVacZero : Dv.radiation vac = 0)
    (hVacOrth : ∀ i x, inner ℂ vac (Wv.field (labelV i x) vac) = 0)
    (vacuumForms : RemovalVacuum.VacuumFormData R₁ Tr E Rfull Trfull Efull vacuum vac
      (fun (j : Fin N × Fin 3) x => Wv.field (labelV j.2 (particle x j.1)) vac) e)
    (m : Efull.State)
    (obs : LatticeObservableData src R₁ Tr E Rfull Trfull Efull Rrad A e vacuum m
      DensityTest CurrentTest Marginal HardMarginal)
    (χ : Equiv.Perm (Fin N) → ℂ)
    (hperm : SpatialPermutationIntertwining src.U)
    (hcharacter : ∀ n, HasElectronicCharacter (fun π => permuteConfiguration π) χ (src.ψ n))
    (compression : Tfull →L[ℝ] Tfull)
    (hcompression : ∀ v : Lp H 2 (volume : Measure (Configuration N)),
      HasElectronicCharacter (fun π => permuteConfiguration π) χ v →
        compression (Rfull.rankOne (vacuum v)) = Rfull.rankOne (vacuum v))
    (pair : PhysicalPairData obs.density obs.current ρMeasure (Fin N) (Fin 3))
    (originalSoft : obs.softForm.expectation m.val = ENNReal.ofReal (∑' n, ‖src.soft n‖ ^ 2)) :
    obs.softForm.expectation m.val < ⊤ ∧
    ∃ r : Efull.State,
      PhysicalRemovalConclusion pair m r (fun s => obs.marginal s.val)
        (obs.prepareMarginal obs.hardTarget) obs.softForm (obs.softForm.expectation m.val).toReal
        ((3 * latticeRemovalConstant N C) *
          SoftPurification.removalError e k acut bcut (obs.softForm.expectation m.val).toReal) ∧
      compression r.val = r.val := by
  exact lattice_physical_removal_optimized_ofPFData src W D momentum he hC hk hk1 scaledSobolev label spatial
    Fubini hrep hW locality hdom hrad hU hUr B₀ B₁ basis index Rrad A B R₁ Tr E sourceCores.toPFData
    hform hpositive htrace Rfull Trfull Efull vacuum hpositiveFull htraceFull
    Wv Dv labelV hkernelV vac hVac hVacDomain hVacZero hVacOrth vacuumForms m obs χ hperm hcharacter compression hcompression pair originalSoft


end Assembly
end GptLean.RemovalEnergy
