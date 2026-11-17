import GptLean.RemovalOriginalOutput
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

section SpatialData

variable {Q Ω G Ho H : Type*} [MeasurableSpace Q] [MeasurableSpace Ω]
  {μ : Measure Q} {ν : Measure Ω} [IsProbabilityMeasure μ] [SFinite ν] [IsSeparable ν]
  [NormedAddCommGroup Ho] [InnerProductSpace ℂ Ho]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] {N : ℕ}

/-- One-photon kernels and standard first-chaos and deterministic Sobolev
background. No spatial random field or random supremum is supplied. -/
structure LatticeSpatialData
    (W : WienerSegalData Q (Lp Ho 2 (volume : Measure (Configuration N)))
      (Lp H 2 (volume : Measure (Configuration N))) G μ)
    {weight : Ω → ℝ} (D : KernelFieldData ν W weight)
    (momentum : Ω → FieldSpace) (k acut bcut : ℝ)
    (label : Fin 3 → List (Fin 3) → FieldSpace → G) where
  kernels : RemovalKernelData W D momentum k acut bcut label
  core : CountableSpatialTestCore
  sobolev : SmoothSobolevBackground
  firstChaos : Lp ℂ 2 ν →L[ℝ] Lp ℝ 2 μ
  momentum_measurable : Measurable momentum
  nonnegative : 0 ≤ k
  base_measurable : ∀ i, Measurable (kernels.base i)
  base_integrable : ∀ i, Integrable (fun y => ‖kernels.base i y‖ ^ 2) ν
  firstChaos_eq : ∀ i ds x,
    (firstChaos (softKernelL2 momentum momentum_measurable ds nonnegative
      (kernels.base i) (base_measurable i) (base_integrable i) x) : Q → ℝ)
      =ᵐ[μ] W.coordinate (label i ds x)

def LatticeSpatialData.field
    {W : WienerSegalData Q (Lp Ho 2 (volume : Measure (Configuration N)))
      (Lp H 2 (volume : Measure (Configuration N))) G μ}
    {weight : Ω → ℝ} {D : KernelFieldData ν W weight}
    {momentum : Ω → FieldSpace} {k acut bcut : ℝ}
    {label : Fin 3 → List (Fin 3) → FieldSpace → G}
    (s : LatticeSpatialData W D momentum k acut bcut label) :
    SpatialWISField (μ := μ) W.coordinate label :=
  SpatialWISField.ofFirstChaos W s.core s.sobolev s.firstChaos momentum s.momentum_measurable
    s.nonnegative s.kernels.base s.base_measurable s.base_integrable label s.firstChaos_eq

end SpatialData

section ObservableData

variable {Q Ho H Hr F T Hfull Tfull Marginal HardMarginal DensityTest CurrentTest : Type*}
  [MeasurableSpace Q] {μ : Measure Q} [IsProbabilityMeasure μ] {N : ℕ}
  [NormedAddCommGroup Ho] [InnerProductSpace ℂ Ho]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup Hfull] [InnerProductSpace ℂ Hfull]
  [NormedAddCommGroup Tfull] [NormedSpace ℝ Tfull] [CompleteSpace Tfull]
  [NormedAddCommGroup Marginal] [NormedSpace ℝ Marginal] [CompleteSpace Marginal]
  [NormedAddCommGroup HardMarginal] [NormedSpace ℝ HardMarginal] [CompleteSpace HardMarginal]

/-- Original spectral tests and universal observable formulas. All vacuum
identities hold for every vector, independently of the removal output. -/
structure LatticeObservableData
    (src : LatticeSourceData N μ Ho H Hr F Ho)
    (R₁ : RankOneData (Lp H 2 (volume : Measure (Configuration N))) T)
    (Tr : PositiveTraceData T) (E : PositiveForm Tr)
    (Rfull : RankOneData Hfull Tfull) (Trfull : PositiveTraceData Tfull)
    (Efull : PositiveForm Trfull)
    (Rrad : H →ₗ.[ℂ] H) (A : (Fin N × Fin 3) → Configuration N → H →ₗ.[ℂ] H) (e : ℝ)
    (vacuum : Lp H 2 (volume : Measure (Configuration N)) →ₗᵢ[ℂ] Hfull)
    (m : Efull.State) (DensityTest CurrentTest Marginal HardMarginal : Type*)
    [NormedAddCommGroup Marginal] [NormedSpace ℝ Marginal] [CompleteSpace Marginal]
    [NormedAddCommGroup HardMarginal] [NormedSpace ℝ HardMarginal] [CompleteSpace HardMarginal] where
  densityHard : DensityTest → T →L[ℝ] ℝ
  currentHard : CurrentTest → FormObservable E
  density : DensityTest → Tfull →L[ℝ] ℝ
  current : CurrentTest → FormObservable Efull
  hardMarginal : T →L[ℝ] HardMarginal
  prepareMarginal : HardMarginal →L[ℝ] Marginal
  marginal : Tfull →L[ℝ] Marginal
  hardTarget : HardMarginal
  tests : OriginalSourceTests src.U src.ψ src.dψ R₁ hardMarginal
    (fun t => density t m.val) (fun t => (current t).value m.val) hardTarget
  density_rankOne : ∀ t (v : Lp H 2 (volume : Measure (Configuration N))),
    densityHard t (R₁.rankOne v) = ∫ x, (tests.density t).weight x * ‖v x‖ ^ 2
  canonical : RemovalPhysicalCurrent.CanonicalCurrent R₁ Rrad A e currentHard
    (fun t => (tests.current t).weight) tests.direction
  currentBound : CurrentTest → ℝ
  currentBound_nonneg : ∀ t, 0 ≤ currentBound t
  current_bound : ∀ t n x, x ∈ Tr.positive → E.expectation x < ⊤ →
    ‖(currentHard t).approximation n x‖ ≤ currentBound t * (Tr.trace x + (E.expectation x).toReal)
  marginalTests : ℕ → Marginal →L[ℝ] ℂ
  marginalOperator : ℕ → H →L[ℂ] H
  separate : ∀ x y : Marginal, (∀ t, marginalTests t x = marginalTests t y) → x = y
  marginal_rankOne : ∀ t (v : Lp H 2 (volume : Measure (Configuration N))),
    marginalTests t (prepareMarginal (hardMarginal (R₁.rankOne v))) =
      ∫ x, inner ℂ (v x) (marginalOperator t (v x))
  density_vacuum : ∀ t v, density t (Rfull.rankOne (vacuum v)) = densityHard t (R₁.rankOne v)
  current_vacuum : ∀ t v, E.expectation (R₁.rankOne v) < ⊤ →
    (current t).value (Rfull.rankOne (vacuum v)) = (currentHard t).value (R₁.rankOne v)
  marginal_vacuum : ∀ v, marginal (Rfull.rankOne (vacuum v)) =
    prepareMarginal (hardMarginal (R₁.rankOne v))
  fullCurrentBound : CurrentTest → ℝ
  fullCurrentBound_nonneg : ∀ t, 0 ≤ fullCurrentBound t
  full_current_bound : ∀ t n x, x ∈ Trfull.positive → Efull.expectation x < ⊤ →
    ‖(current t).approximation n x‖ ≤
      fullCurrentBound t * (Trfull.trace x + (Efull.expectation x).toReal)
  original_energy : src.inputEnergy = (Efull.expectation m.val).toReal
  softForm : PositiveForm Trfull
  vacuum_zero : ∀ v, softForm.expectation (Rfull.rankOne (vacuum v)) = 0

end ObservableData

def latticeRemovalConstant (N : ℕ) (C : ℝ) : ℝ :=
  removalConstant (latticeIMSConstant N) (clusterRepairMetricConstant N)
    (clusterGaussianConstant N C) (3 * (N : ℝ) / 2)

section Assembly

variable {Q Ω G Ho H Hr F T Hfull Tfull Marginal HardMarginal DensityTest CurrentTest ι : Type*}
  [MeasurableSpace Q] [MeasurableSpace Ω] {μ : Measure Q} {ν : Measure Ω}
  [IsProbabilityMeasure μ] [SFinite ν] [IsSeparable ν] {N : ℕ}
  [NormedAddCommGroup Ho] [InnerProductSpace ℂ Ho] [CompleteSpace Ho]
  [TopologicalSpace.SeparableSpace Ho]
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

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace F] [BorelSpace F] in
/-- Exact soft removal with all localization, spatial realization,
source-moment, physical-channel and vacuum-energy steps instantiated.
The physical source is supplied by the original PF graph data.
Universal core descriptions remain available through the compatibility entry point. -/
def lattice_exactOutput_ofPFData
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
      DensityTest CurrentTest Marginal HardMarginal) :
    {out : SoftRemoval.LocalizedOutput (VectorData.model (testedPair obs.density obs.current)) m
      (fun s => obs.marginal s.val) (obs.prepareMarginal obs.hardTarget) (∑' n, ‖src.soft n‖ ^ 2)
      (latticeRemovalConstant N C) e k R acut bcut // obs.softForm.expectation out.state.val = 0} := by
  let S := src.conditioned R hR
  let field := spatial.field
  let gsrc := GaussianSourceData.ofLattice src W D Fubini hrep hW locality hdom hrad R hR
  let P₀ := sourcePF
  let P := src.localizedPFData R hR hU hUr Rrad A B e
    (fun j qx => vectorField field.field [] qx.1 (particle qx.2 j.1) j.2) P₀
  have hsupport := src.source_support R hR
    (hU.localized_commute (latticeMultiplier R) (latticeMultiplier_partition R)
      (latticeMultiplier_measurable R))
  let channel := physicalChannel_from_kernels S W D gsrc momentum acut bcut
    spatial.nonnegative hR he hC hkR scaledSobolev (sourceLatticeCentre R) label spatial.kernels field
    B₀ B₁ basis index Rrad A B R₁ Tr E P hform hsupport hpositive htrace
  let link := physicalSourceLink_from_kernels S W D gsrc momentum acut bcut
    spatial.nonnegative hR he hC hkR scaledSobolev (sourceLatticeCentre R) label spatial.kernels field
    B₀ B₁ basis index Rrad A B R₁ Tr E P hform hsupport hpositive htrace
  have hvac := vacuumForms.energy_bound_from_kernels Dv momentum k bcut e spatial.kernels.base labelV
    hkernelV spatial.kernels.weighted_integrable spatial.kernels.square_integrable
    spatial.kernels.cutoff_square vac hVac hVacDomain hVacZero hVacOrth R₁ Tr E Rfull Trfull Efull vacuum
  have hims : 0 ≤ latticeIMSConstant N := by
    unfold latticeIMSConstant
    exact mul_nonneg (by positivity) LatticePartition.metricConstant_pos.le
  have hcost : (1 / 2 : ℝ) * ∑ j, (src.toOriginalSource R hR).metric j ≤
      latticeIMSConstant N * (R ^ 2)⁻¹ := by
    rw [src.toOriginalSource_metric_sum R hR, div_eq_mul_inv]
  exact ChannelData.exactOutput_original (src.toOriginalSource R hR) channel link hims
    (clusterRepairMetricConstant_nonneg N) (clusterGaussianConstant_nonneg N hC) (by positivity)
    he spatial.nonnegative P vacuum hpositiveFull htraceFull hvac m
    obs.densityHard obs.currentHard obs.density obs.current obs.hardMarginal obs.prepareMarginal
    obs.marginal obs.hardTarget obs.tests obs.density_rankOne obs.canonical
    obs.currentBound obs.currentBound_nonneg obs.current_bound obs.marginalTests obs.marginalOperator
    obs.separate obs.marginal_rankOne obs.density_vacuum obs.current_vacuum obs.marginal_vacuum
    obs.fullCurrentBound obs.fullCurrentBound_nonneg obs.full_current_bound obs.original_energy hcost
    obs.softForm obs.vacuum_zero

/-- Compatibility entry point for universal core descriptions. -/
def lattice_exactOutput
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
      DensityTest CurrentTest Marginal HardMarginal) :
    {out : SoftRemoval.LocalizedOutput (VectorData.model (testedPair obs.density obs.current)) m
      (fun s => obs.marginal s.val) (obs.prepareMarginal obs.hardTarget) (∑' n, ‖src.soft n‖ ^ 2)
      (latticeRemovalConstant N C) e k R acut bcut // obs.softForm.expectation out.state.val = 0} := by
  exact lattice_exactOutput_ofPFData src W D momentum hR he hC hkR scaledSobolev label spatial
    Fubini hrep hW locality hdom hrad hU hUr B₀ B₁ basis index Rrad A B R₁ Tr E sourceCores.toPFData
    hform hpositive htrace Rfull Trfull Efull vacuum hpositiveFull htraceFull
    Wv Dv labelV hkernelV vac hVac hVacDomain hVacZero hVacOrth vacuumForms m obs

end Assembly
end GptLean.RemovalEnergy
