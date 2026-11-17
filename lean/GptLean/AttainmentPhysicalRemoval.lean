import GptLean.AttainmentPhysical
import GptLean.RemovalPhysicalEndpoint

/-!
Exact lattice removal on the same finite-energy normal state sector used
by attainment. The raw input contains the existing source, graph, WIS,
vacuum and observable data. Its optimized conclusion is obtained by
calling the proved lattice construction, never supplied as a field.

The output is transported through the canonical form-sector equivalence.
The common pair, soft-energy and photon-marginal identities are explicit,
so all conclusions concern the same fermionic normal operator.
-/

noncomputable section

namespace GptLean.AttainmentPhysicalRemoval

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

open MeasureTheory Filter Topology Gaussian RemovalSource RemovalState RemovalGeometry
  RemovalConstruction RemovalConstraints Repair SymmetricLift RemovalEnergy
open scoped ENNReal ContDiff

variable {Q Ω G Ho H Hr F T Hfull Tfull Marginal HardMarginal DensityTest CurrentTest ι : Type*}
  [MeasurableSpace Q] [MeasurableSpace Ω] {μ : Measure Q} {ν : Measure Ω}
  [IsProbabilityMeasure μ] [SFinite ν] [IsSeparable ν] {N : ℕ}
  [NormedAddCommGroup Ho] [InnerProductSpace ℂ Ho]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup Hfull] [InnerProductSpace ℂ Hfull]
  [NormedAddCommGroup Tfull] [NormedSpace ℝ Tfull] [CompleteSpace Tfull]
  [NormedAddCommGroup Marginal] [NormedSpace ℝ Marginal] [CompleteSpace Marginal]
  [NormedAddCommGroup HardMarginal] [NormedSpace ℝ HardMarginal] [CompleteSpace HardMarginal]
  {Qv Hv Kv Gv : Type*} [MeasurableSpace Qv] {μv : Measure Qv}
  [NormedAddCommGroup Hv] [InnerProductSpace ℂ Hv]
  [NormedAddCommGroup Kv] [NormedSpace ℝ Kv]

variable {X : Type*} [MeasurableSpace X] {ρMeasure : Measure X}

/-- The actual inputs of the lattice removal construction for one source
and one infrared cutoff. No output state or removal estimate is a field. -/
structure LatticeRemovalInput
    (Trfull : PositiveTraceData Tfull) (Efull : PositiveForm Trfull)
    (m : Efull.State) (compression : Tfull →L[ℝ] Tfull)
    (k e C acut bcut : ℝ) where
  src : LatticeSourceData N μ Ho H Hr F Ho
  W : WienerSegalData Q (Lp Ho 2 (volume : Measure (Configuration N)))
    (Lp H 2 (volume : Measure (Configuration N))) G μ
  weight : Ω → ℝ
  D : KernelFieldData ν W weight
  momentum : Ω → FieldSpace
  scaledSobolev : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C
  label : Fin 3 → List (Fin 3) → FieldSpace → G
  spatial : LatticeSpatialData W D momentum k acut bcut label
  Fubini : Lp H 2 (μ.prod (volume : Measure (Configuration N))) ≃ₗᵢ[ℂ]
    Lp (Lp H 2 (volume : Measure (Configuration N))) 2 μ
  hrep : ∀ v : Lp H 2 (μ.prod (volume : Measure (Configuration N))), ∀ᵐ q ∂μ,
    (fun x => v (q, x)) =ᵐ[volume] (fun x => Fubini v q x)
  hW : ∀ v, W.toFiber v =ᵐ[μ] (fun q => Fubini (src.U v) q)
  locality : SpatialRadiationLocality D.radiationDomain D.radiation
  hdom : ∀ n, D.radiationDomain (src.ψ n)
  hrad : ∀ n, D.radiation (src.ψ n) = src.soft n
  hU : SpatialScalarIntertwining src.U
  hUr : SpatialScalarIntertwining src.Ur
  B₀ : TensorBackground SixTag
  B₁ : TensorMultilinearData B₀
  basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target
  index : ι ↪ ℕ
  Rrad : H →ₗ.[ℂ] H
  A : (Fin N × Fin 3) → Configuration N → H →ₗ.[ℂ] H
  B : Configuration N → H →ₗ.[ℂ] F
  R₁ : RankOneData (Lp H 2 (volume : Measure (Configuration N))) T
  Tr : PositiveTraceData T
  E : PositiveForm Tr
  sourcePF : src.original.PFData Rrad A B e
    (fun _ j qx => vectorField spatial.field.field [] qx.1 (particle qx.2 j.1) j.2)
  hform : HasPFFormEvaluation Rrad A B e (fun v => E.expectation (R₁.rankOne v))
  hpositive : R₁.positive ⊆ Tr.positive
  htrace : R₁.trace = Tr.trace
  Rfull : RankOneData Hfull Tfull
  vacuum : Lp H 2 (volume : Measure (Configuration N)) →ₗᵢ[ℂ] Hfull
  hpositiveFull : Rfull.positive ⊆ Trfull.positive
  htraceFull : Rfull.trace = Trfull.trace
  Wv : WienerSegalData Qv Hv Kv Gv μv
  Dv : KernelFieldData ν Wv weight
  labelV : Fin 3 → FieldSpace → Gv
  hkernelV : ∀ i x, Dv.kernel (labelV i x) =
    softDerivativeKernel momentum [] k x (spatial.kernels.base i)
  vac : Hv
  hVac : ‖vac‖ = 1
  hVacDomain : Dv.radiationDomain vac
  hVacZero : Dv.radiation vac = 0
  hVacOrth : ∀ i x, inner ℂ vac (Wv.field (labelV i x) vac) = 0
  vacuumForms : RemovalVacuum.VacuumFormData R₁ Tr E Rfull Trfull Efull vacuum vac
    (fun (j : Fin N × Fin 3) x => Wv.field (labelV j.2 (particle x j.1)) vac) e
  obs : LatticeObservableData src R₁ Tr E Rfull Trfull Efull Rrad A e vacuum m
    DensityTest CurrentTest Marginal HardMarginal
  χ : Equiv.Perm (Fin N) → ℂ
  hperm : SpatialPermutationIntertwining src.U
  hcharacter : ∀ n, HasElectronicCharacter (fun π => permuteConfiguration π) χ (src.ψ n)
  hcompression : ∀ v : Lp H 2 (volume : Measure (Configuration N)),
    HasElectronicCharacter (fun π => permuteConfiguration π) χ v →
      compression (Rfull.rankOne (vacuum v)) = Rfull.rankOne (vacuum v)
  pair : PhysicalPairData obs.density obs.current ρMeasure (Fin N) (Fin 3)
  originalSoft : obs.softForm.expectation m.val = ENNReal.ofReal (∑' n, ‖src.soft n‖ ^ 2)

namespace LatticeRemovalInput

variable {Trfull : PositiveTraceData Tfull} {Efull : PositiveForm Trfull}
  {m : Efull.State} {compression : Tfull →L[ℝ] Tfull} {k e C acut bcut : ℝ}
  (L : LatticeRemovalInput (Q := Q) (Ω := Ω) (G := G) (Ho := Ho) (H := H)
    (Hr := Hr) (F := F) (T := T) (Hfull := Hfull) (Marginal := Marginal)
    (HardMarginal := HardMarginal) (DensityTest := DensityTest) (CurrentTest := CurrentTest)
    (ι := ι) (Qv := Qv) (Hv := Hv) (Kv := Kv) (Gv := Gv)
    (μ := μ) (ν := ν) (μv := μv) (ρMeasure := ρMeasure) (N := N)
    Trfull Efull m compression k e C acut bcut)

/-- The existing optimized physical construction is applied to the raw
inputs. The same output is fixed by the electronic compression. -/
theorem optimized (he : 0 ≤ e) (hC : 0 ≤ C) (hk : 0 < k) (hk1 : k ≤ 1) :
    ∃ r : Efull.State,
      PhysicalRemovalConclusion L.pair m r (fun s => L.obs.marginal s.val)
        (L.obs.prepareMarginal L.obs.hardTarget) L.obs.softForm
        (L.obs.softForm.expectation m.val).toReal
        ((3 * latticeRemovalConstant N C) * SoftPurification.removalError e k acut bcut
          (L.obs.softForm.expectation m.val).toReal) ∧ compression r.val = r.val := by
  exact (lattice_physical_removal_optimized_ofPFData
    L.src L.W L.D L.momentum he hC hk
    hk1 L.scaledSobolev L.label L.spatial L.Fubini L.hrep L.hW
    L.locality L.hdom L.hrad L.hU L.hUr L.B₀ L.B₁
    L.basis L.index L.Rrad L.A L.B L.R₁ L.Tr
    L.E L.sourcePF L.hform L.hpositive L.htrace L.Rfull Trfull
    Efull L.vacuum L.hpositiveFull L.htraceFull L.Wv L.Dv L.labelV
    L.hkernelV L.vac L.hVac L.hVacDomain L.hVacZero L.hVacOrth L.vacuumForms
    m L.obs L.χ L.hperm L.hcharacter compression L.hcompression
    L.pair L.originalSoft).2

end LatticeRemovalInput

section Common

variable {Test Pair : Type*} [TopologicalSpace Pair]

/-- The form-state representative is the canonical common-sector
equivalence, so it retains the same underlying normal operator. -/
def formState
    (loss : PhotonLoss.LocalizationData Tfull) (trace : PhotonLoss.TraceData loss Test)
    (Trfull : PositiveTraceData Tfull) (Efull : PositiveForm Trfull)
    (compression : Tfull →L[ℝ] Tfull)
    (hstates : ∀ x, x ∈ loss.states ↔
      x ∈ Trfull.positive ∧ Trfull.trace x = 1 ∧ compression x = x)
    (henergy : ∀ x ∈ loss.states, trace.energy x = Efull.expectation x)
    (s : PhotonLoss.FiniteEnergyState loss trace) : Efull.State :=
  ((PhotonLoss.FiniteEnergyState.equivFormSector loss trace Trfull Efull
    {x | compression x = x} hstates henergy) s).val

/-- The physical pair is evaluated on that same form-state representative. -/
def finitePair
    (loss : PhotonLoss.LocalizationData Tfull) (trace : PhotonLoss.TraceData loss Test)
    (Trfull : PositiveTraceData Tfull) (Efull : PositiveForm Trfull)
    (compression : Tfull →L[ℝ] Tfull)
    (hstates : ∀ x, x ∈ loss.states ↔
      x ∈ Trfull.positive ∧ Trfull.trace x = 1 ∧ compression x = x)
    (henergy : ∀ x ∈ loss.states, trace.energy x = Efull.expectation x)
    (pair : Efull.State → Pair) (s : PhotonLoss.FiniteEnergyState loss trace) : Pair :=
  pair (formState loss trace Trfull Efull compression hstates henergy s)

/-- Raw construction inputs identified with the common state model.
The marginal number identity concerns the full photon marginal and is
universal on all form states. The prepared-target identity is the
vacuum plus hard-marginal number law.
Neither refers to a selected removal output. -/
structure CommonRemovalInput
    (loss : PhotonLoss.LocalizationData Tfull) (trace : PhotonLoss.TraceData loss Test)
    (Trfull : PositiveTraceData Tfull) (Efull : PositiveForm Trfull)
    (compression : Tfull →L[ℝ] Tfull)
    (hstates : ∀ x, x ∈ loss.states ↔
      x ∈ Trfull.positive ∧ Trfull.trace x = 1 ∧ compression x = x)
    (henergy : ∀ x ∈ loss.states, trace.energy x = Efull.expectation x)
    (pair : Efull.State → Pair) (s : PhotonLoss.FiniteEnergyState loss trace)
    (κ e C a b soft hard : ℝ) where
  lattice : LatticeRemovalInput (Q := Q) (Ω := Ω) (G := G) (Ho := Ho) (H := H)
    (Hr := Hr) (F := F) (T := T) (Hfull := Hfull) (Marginal := Marginal)
    (HardMarginal := HardMarginal) (DensityTest := DensityTest) (CurrentTest := CurrentTest)
    (ι := ι) (Qv := Qv) (Hv := Hv) (Kv := Kv) (Gv := Gv)
    (μ := μ) (ν := ν) (μv := μv) (ρMeasure := ρMeasure) (N := N)
    Trfull Efull (formState loss trace Trfull Efull compression hstates henergy s)
    compression κ e C a b
  pair_identification : ∀ r m : Efull.State,
    lattice.pair.rho r =ᵐ[ρMeasure] lattice.pair.rho m →
    lattice.pair.currentDensity r =ᵐ[ρMeasure] lattice.pair.currentDensity m → pair r = pair m
  soft_identification : (lattice.obs.softForm.expectation s.val).toReal = soft
  marginalNumber : Marginal → ℝ≥0∞
  number_identification : ∀ r : Efull.State,
    trace.number r.val = marginalNumber (lattice.obs.marginal r.val)
  target_number : marginalNumber (lattice.obs.prepareMarginal lattice.obs.hardTarget) =
    ENNReal.ofReal hard

namespace CommonRemovalInput

variable {loss : PhotonLoss.LocalizationData Tfull} {trace : PhotonLoss.TraceData loss Test}
  {Trfull : PositiveTraceData Tfull} {Efull : PositiveForm Trfull}
  {compression : Tfull →L[ℝ] Tfull}
  {hstates : ∀ x, x ∈ loss.states ↔
    x ∈ Trfull.positive ∧ Trfull.trace x = 1 ∧ compression x = x}
  {henergy : ∀ x ∈ loss.states, trace.energy x = Efull.expectation x}
  {pair : Efull.State → Pair} {s : PhotonLoss.FiniteEnergyState loss trace}
  {κ e C a b soft hard : ℝ}
  (I : CommonRemovalInput (Q := Q) (Ω := Ω) (G := G) (Ho := Ho) (H := H)
    (Hr := Hr) (F := F) (T := T) (Hfull := Hfull) (Marginal := Marginal)
    (HardMarginal := HardMarginal) (DensityTest := DensityTest) (CurrentTest := CurrentTest)
    (ι := ι) (Qv := Qv) (Hv := Hv) (Kv := Kv) (Gv := Gv)
    (μ := μ) (ν := ν) (μv := μv) (ρMeasure := ρMeasure) (N := N)
    loss trace Trfull Efull compression hstates henergy pair s κ e C a b soft hard)

omit [TopologicalSpace Pair] in
include I in
/-- The optimized lattice output is an actual member of the common
finite-energy fermionic state type. Pair preservation, energy gain and
the number bound are all derived for this one transported output. -/
theorem repair (he : 0 ≤ e) (hC : 0 ≤ C) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ r : PhotonLoss.FiniteEnergyState loss trace,
      finitePair loss trace Trfull Efull compression hstates henergy pair r =
        finitePair loss trace Trfull Efull compression hstates henergy pair s ∧
      (trace.energy r.val).toReal ≤ (trace.energy s.val).toReal - soft +
        (3 * latticeRemovalConstant N C) * SoftPurification.removalError e κ a b soft ∧
      trace.number r.val ≤ ENNReal.ofReal hard := by
  obtain ⟨r, hr, hfixed⟩ := I.lattice.optimized he hC hκ hκ1
  let equiv := PhotonLoss.FiniteEnergyState.equivFormSector loss trace Trfull Efull
    {x | compression x = x} hstates henergy
  let rstate := equiv.symm ⟨r, hfixed⟩
  have hrepr : rstate.val = r.val := rfl
  have hform : formState loss trace Trfull Efull compression hstates henergy rstate = r :=
    Subtype.ext rfl
  refine ⟨rstate, ?_, ?_, ?_⟩
  · change pair (formState loss trace Trfull Efull compression hstates henergy rstate) =
      pair (formState loss trace Trfull Efull compression hstates henergy s)
    rw [hform]
    exact I.pair_identification r _ hr.density_eq hr.current_eq
  · have h := hr.energy_bound
    change (Efull.expectation r.val).toReal ≤ (Efull.expectation s.val).toReal -
      (I.lattice.obs.softForm.expectation s.val).toReal +
      (3 * latticeRemovalConstant N C) * SoftPurification.removalError e κ a b
        (I.lattice.obs.softForm.expectation s.val).toReal at h
    rw [I.soft_identification] at h
    rw [henergy rstate.val rstate.property.1, henergy s.val s.property.1, hrepr]
    exact h
  · change trace.number r.val ≤ ENNReal.ofReal hard
    rw [I.number_identification, hr.marginal_eq, I.target_number]

end CommonRemovalInput

omit [TopologicalSpace Pair] in
/-- The infrared repair interface for the common model is obtained from
raw lattice construction families and universal physical identifications.
There is no optimized-removal hypothesis in this theorem. -/
theorem infraredRepair
    (loss : PhotonLoss.LocalizationData Tfull) (trace : PhotonLoss.TraceData loss Test)
    (Trfull : PositiveTraceData Tfull) (Efull : PositiveForm Trfull)
    (compression : Tfull →L[ℝ] Tfull)
    (hstates : ∀ x, x ∈ loss.states ↔
      x ∈ Trfull.positive ∧ Trfull.trace x = 1 ∧ compression x = x)
    (henergy : ∀ x ∈ loss.states, trace.energy x = Efull.expectation x)
    (pair : Efull.State → Pair) (dispersion : Ω → ℝ) (w : Ω → ℝ≥0∞)
    (moments : InfraredRepair.InfraredMoments
      (PhotonLoss.finiteEnergyModel loss trace
        (finitePair loss trace Trfull Efull compression hstates henergy pair))
      (fun s => trace.number s.val) ν dispersion w)
    {e C : ℝ} (he : 0 ≤ e) (hC : 0 ≤ C)
    (inputs : ∀ (s : PhotonLoss.FiniteEnergyState loss trace) κ, 0 < κ → κ ≤ 1 →
      Nonempty (CommonRemovalInput (Q := Q) (Ω := Ω) (G := G) (Ho := Ho) (H := H)
        (Hr := Hr) (F := F) (T := T) (Hfull := Hfull) (Marginal := Marginal)
        (HardMarginal := HardMarginal) (DensityTest := DensityTest) (CurrentTest := CurrentTest)
        (ι := ι) (Qv := Qv) (Hv := Hv) (Kv := Kv) (Gv := Gv)
        (μ := μ) (ν := ν) (μv := μv) (ρMeasure := ρMeasure) (N := N)
        loss trace Trfull Efull compression hstates henergy pair s κ e C
        (Real.sqrt (CutoffProfile.asq ν dispersion w κ))
        (Real.sqrt (CutoffProfile.bsq ν dispersion w κ))
        (moments.softEnergy s κ) (moments.hardNumber s κ))) :
    Nonempty (AttainmentConstruction.InfraredRepairData
      (PhotonLoss.finiteEnergyModel loss trace
        (finitePair loss trace Trfull Efull compression hstates henergy pair))
      (fun s => trace.number s.val) ν dispersion w) := by
  apply InfraredRepair.exists_data_of_optimized moments
    (show 0 ≤ 3 * latticeRemovalConstant N C from
      mul_nonneg (by norm_num) (latticeRemovalConstant_nonneg N C)) he
  intro s κ hκ hκ1
  obtain ⟨I⟩ := inputs s κ hκ hκ1
  exact I.repair he hC hκ hκ1

end Common

section Endpoint

variable {Test Pair Pure Potential : Type*}
  [NormedAddCommGroup Pair] [NormedSpace ℝ Pair]

/-- Attainment, the minimizing-state photon-number bound, lower
semicontinuity and Lieb duality on the common fermionic normal states.
The optimized removal step is proved from the raw lattice input family,
and the constraint realization is constructed on the same state type.
The localization estimates remain an explicit input of this assembly. -/
theorem all_conclusions
    (loss : PhotonLoss.LocalizationData Tfull) (trace : PhotonLoss.TraceData loss Test)
    (J : PhotonLoss.LocalizationEstimates loss trace)
    (Trfull : PositiveTraceData Tfull) (Efull : PositiveForm Trfull)
    (compression : Tfull →L[ℝ] Tfull)
    (hstates : ∀ x, x ∈ loss.states ↔
      x ∈ Trfull.positive ∧ Trfull.trace x = 1 ∧ compression x = x)
    (henergy : ∀ x ∈ loss.states, trace.energy x = Efull.expectation x)
    (pair : Efull.State → Pair)
    (pairTest : Test → Pair → ℝ)
    (hcontinuous : ∀ t, Continuous (pairTest t))
    (hseparates : ∀ d d', (∀ t, pairTest t d = pairTest t d') → d = d')
    (htest : ∀ t s, trace.test t s.val = pairTest t
      (finitePair loss trace Trfull Efull compression hstates henergy pair s))
    (density : Tfull → Lp ℝ 1 ρMeasure)
    (densityComponent : Pair → Lp ℝ 1 ρMeasure)
    (hcomponent : Continuous densityComponent)
    (hdensity : ∀ s, density s.val = densityComponent
      (finitePair loss trace Trfull Efull compression hstates henergy pair s))
    (htight : J.electronicTight = fun u =>
      ∃ ρ, Tendsto (fun n => density (u n)) atTop (𝓝 ρ))
    (dispersion : Ω → ℝ) (w : Ω → ℝ≥0∞)
    (moments : InfraredRepair.InfraredMoments
      (PhotonLoss.finiteEnergyModel loss trace
        (finitePair loss trace Trfull Efull compression hstates henergy pair))
      (fun s => trace.number s.val) ν dispersion w)
    {e C : ℝ} (he : 0 ≤ e) (hC : 0 ≤ C)
    (inputs : ∀ (s : PhotonLoss.FiniteEnergyState loss trace) κ, 0 < κ → κ ≤ 1 →
      Nonempty (CommonRemovalInput (Q := Q) (Ω := Ω) (G := G) (Ho := Ho) (H := H)
        (Hr := Hr) (F := F) (T := T) (Hfull := Hfull) (Marginal := Marginal)
        (HardMarginal := HardMarginal) (DensityTest := DensityTest) (CurrentTest := CurrentTest)
        (ι := ι) (Qv := Qv) (Hv := Hv) (Kv := Kv) (Gv := Gv)
        (μ := μ) (ν := ν) (μv := μv) (ρMeasure := ρMeasure) (N := N)
        loss trace Trfull Efull compression hstates henergy pair s κ e C
        (Real.sqrt (CutoffProfile.asq ν dispersion w κ))
        (Real.sqrt (CutoffProfile.bsq ν dispersion w κ))
        (moments.softEnergy s κ) (moments.hardNumber s κ)))
    (A : DFT.StateModel Pure Pair)
    (m₀ : PhotonLoss.FiniteEnergyState loss trace)
    (hmix : DFT.MixtureClosed (PhotonLoss.finiteEnergyModel loss trace
      (finitePair loss trace Trfull Efull compression hstates henergy pair)))
    (emb : DFT.PureEmbedding A (PhotonLoss.finiteEnergyModel loss trace
      (finitePair loss trace Trfull Efull compression hstates henergy pair)))
    (duality : Potential → Pair → ℝ)
    (spectral : ∀ m v, Nonempty (Theorem48.SpectralEnsemble A
      (PhotonLoss.finiteEnergyModel loss trace
        (finitePair loss trace Trfull Efull compression hstates henergy pair)) duality m v))
    (fm : DFT.FenchelMoreau duality) :
    ∃ Cnumber : ℝ, 0 ≤ Cnumber ∧
      (∀ d, DFT.search (PhotonLoss.finiteEnergyModel loss trace
          (finitePair loss trace Trfull Efull compression hstates henergy pair)) d < ⊤ → ∃ m,
        finitePair loss trace Trfull Efull compression hstates henergy pair m = d ∧
        ((trace.energy m.val).toReal : EReal) =
          DFT.search (PhotonLoss.finiteEnergyModel loss trace
            (finitePair loss trace Trfull Efull compression hstates henergy pair)) d ∧
        trace.number m.val ≤ ENNReal.ofReal (Cnumber * (1 + (trace.energy m.val).toReal)) ∧
        trace.number m.val < ⊤) ∧
      (∀ m, ((trace.energy m.val).toReal : EReal) =
          DFT.search (PhotonLoss.finiteEnergyModel loss trace
            (finitePair loss trace Trfull Efull compression hstates henergy pair))
            (finitePair loss trace Trfull Efull compression hstates henergy pair m) →
        trace.number m.val ≤ ENNReal.ofReal (Cnumber * (1 + (trace.energy m.val).toReal))) ∧
      LowerSemicontinuous (DFT.search (PhotonLoss.finiteEnergyModel loss trace
        (finitePair loss trace Trfull Efull compression hstates henergy pair))) ∧
      (∀ d, DFT.search (PhotonLoss.finiteEnergyModel loss trace
        (finitePair loss trace Trfull Efull compression hstates henergy pair)) d =
          DFT.lieb A duality d) := by
  obtain ⟨I⟩ := infraredRepair loss trace Trfull Efull compression hstates henergy
    pair dispersion w moments he hC inputs
  let realization := PhotonLoss.ConstraintRealization.ofFiniteEnergyStates loss trace J
    (finitePair loss trace Trfull Efull compression hstates henergy pair)
    pairTest hcontinuous hseparates htest density densityComponent hcomponent hdensity htight
  exact ⟨I.numberConstant, I.numberConstant_nonneg,
    Theorem48.all_conclusions A (PhotonLoss.finiteEnergyModel loss trace
      (finitePair loss trace Trfull Efull compression hstates henergy pair))
      (fun s => trace.number s.val) ν dispersion w I loss trace J realization m₀ hmix
      emb duality spectral fm⟩

end Endpoint

end GptLean.AttainmentPhysicalRemoval

namespace GptLean.RemovalConstraints.PhysicalPairData

open MeasureTheory RemovalState

variable {X T DensityTest CurrentTest Particle Direction : Type*}
  [MeasurableSpace X] {ν : Measure X}
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  {Tr : PositiveTraceData T} {E : PositiveForm Tr}
  [Fintype Particle] [Fintype Direction]
  {density : DensityTest → T →L[ℝ] ℝ} {current : CurrentTest → FormObservable E}

/-- The physical density and current are represented by their actual L¹
classes, with the finitely many current components kept in a product. -/
def l1Pair (P : PhysicalPairData density current ν Particle Direction) (s : E.State) :
    Lp ℝ 1 ν × (Direction → Lp ℝ 1 ν) :=
  ⟨(P.rho_integrable s).toL1 (P.rho s),
    fun j => (P.current_integrable s j).toL1 (fun x => P.currentDensity s x j)⟩

/-- The pair-identification field of `CommonRemovalInput` is automatic
for the canonical L¹ realization of the physical functions. -/
theorem l1Pair_eq_of_ae (P : PhysicalPairData density current ν Particle Direction)
    (r s : E.State) (hρ : P.rho r =ᵐ[ν] P.rho s)
    (hj : P.currentDensity r =ᵐ[ν] P.currentDensity s) : P.l1Pair r = P.l1Pair s := by
  apply Prod.ext
  · exact (Integrable.toL1_eq_toL1_iff _ _ (P.rho_integrable r) (P.rho_integrable s)).mpr hρ
  · funext j
    apply (Integrable.toL1_eq_toL1_iff _ _ (P.current_integrable r j)
      (P.current_integrable s j)).mpr
    exact hj.mono fun x hx => congrArg (fun v => v j) hx

end GptLean.RemovalConstraints.PhysicalPairData
