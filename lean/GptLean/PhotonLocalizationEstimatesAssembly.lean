import GptLean.PhotonLocalizationElectronicPartition
import GptLean.PhotonLocalizationSharpEnergy
import GptLean.PhotonLocalizationCurrentChannel
import GptLean.PhotonLocalizationCoarseEndpoint
import GptLean.PhotonLocalizationStateRestriction

/-!
Assembly on a common localization channel.

The electronic IMS estimate below starts with the covariant form's
spatial graph identity. Its scalar density may have either sign, so an
attractive potential is included. Positivity is used only for the full
shifted form on the other partition branches. The resulting pure estimate
is lifted through the original positive spectral expansion.
-/

noncomputable section

namespace GptLean.PhotonLocalization

open Filter Topology MeasureTheory ElectronicLocalization
open PhotonLocalizationChannel
open scoped InnerProductSpace ENNReal

section ElectronicIMS

variable {Ω K α ι : Type*}
  [NormedAddCommGroup Ω] [NormedSpace ℝ Ω] [MeasurableSpace Ω]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [Fintype α] [Fintype ι]

/-- Full shifted PF form density. The scalar term includes the signed
potential, radiation density and the chosen constant energy shift. -/
def partitionFormDensity (f : α → Ω → ℝ) (direction : ι → Ω)
    (d : ι → Ω → K) (ψ : Ω → K) (scalar : Ω → ℝ) (a : α) (x : Ω) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ‖localizedDerivative f (d i) ψ (direction i) a x‖ ^ 2 +
    f a x ^ 2 * scalar x

omit [MeasurableSpace Ω] in
/-- Exact scalar partition identities give the coefficient-one pointwise
IMS estimate, including a signed scalar form term. -/
theorem partitionFormDensity_sum_le
    (f : α → Ω → ℝ) (direction : ι → Ω)
    (hd : ∀ a, Differentiable ℝ (f a)) (hpos : ∀ a x, 0 ≤ f a x)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (d : ι → Ω → K) (ψ : Ω → K) (scalar : Ω → ℝ)
    (C : ℝ) (hmetric : ∀ x,
      (1 / 2 : ℝ) * ∑ i, ∑ a, fderiv ℝ (f a) x (direction i) ^ 2 ≤ C)
    (x : Ω) :
    (∑ a, partitionFormDensity f direction d ψ scalar a x) ≤
      (1 / 2 : ℝ) * ∑ i, ‖d i x‖ ^ 2 + scalar x + C * ‖ψ x‖ ^ 2 := by
  classical
  have hi (i : ι) := (localization_ims_hasSum f (locallyFinite_of_finite _)
    hd hpos hpart (d i) ψ x (direction i)).tsum_eq
  simp only [tsum_fintype] at hi
  have hp := (hpart x).tsum_eq
  simp only [tsum_fintype] at hp
  calc
    _ = (1 / 2 : ℝ) * ∑ i, ∑ a,
        ‖localizedDerivative f (d i) ψ (direction i) a x‖ ^ 2 +
        (∑ a, f a x ^ 2) * scalar x := by
      simp only [partitionFormDensity, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = (1 / 2 : ℝ) * ∑ i, ‖d i x‖ ^ 2 + scalar x +
        ((1 / 2 : ℝ) * ∑ i, ∑ a, fderiv ℝ (f a) x (direction i) ^ 2) * ‖ψ x‖ ^ 2 := by
      simp only [hi, hp, one_mul, Finset.sum_add_distrib, ← Finset.sum_mul]
      ring
    _ ≤ _ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (hmetric x) (sq_nonneg _))

/-- Integrating the exact partition identities and dropping the other
nonnegative full-form branches proves the sharp electronic cutoff bound.
No sign condition is imposed on the scalar density. -/
theorem partitionFormDensity_integral_bound
    (μ : Measure Ω) (f : α → Ω → ℝ) (direction : ι → Ω)
    (hd : ∀ a, Differentiable ℝ (f a)) (hpos : ∀ a x, 0 ≤ f a x)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (d : ι → Ω → K) (ψ : Ω → K) (scalar : Ω → ℝ)
    (C : ℝ) (hmetric : ∀ x,
      (1 / 2 : ℝ) * ∑ i, ∑ a, fderiv ℝ (f a) x (direction i) ^ 2 ≤ C)
    (hbranch : ∀ a, Integrable (partitionFormDensity f direction d ψ scalar a) μ)
    (hsource : Integrable (fun x => (1 / 2 : ℝ) * ∑ i, ‖d i x‖ ^ 2 + scalar x) μ)
    (hmass : Integrable (fun x => ‖ψ x‖ ^ 2) μ)
    (hbranch_nonneg : ∀ a, 0 ≤ ∫ x, partitionFormDensity f direction d ψ scalar a x ∂μ)
    (selected : α) :
    (∫ x, partitionFormDensity f direction d ψ scalar selected x ∂μ) ≤
      (∫ x, (1 / 2 : ℝ) * ∑ i, ‖d i x‖ ^ 2 + scalar x ∂μ) +
        C * ∫ x, ‖ψ x‖ ^ 2 ∂μ := by
  classical
  calc
    _ ≤ ∑ a, ∫ x, partitionFormDensity f direction d ψ scalar a x ∂μ :=
      Finset.single_le_sum (fun a _ => hbranch_nonneg a) (Finset.mem_univ _)
    _ = ∫ x, ∑ a, partitionFormDensity f direction d ψ scalar a x ∂μ :=
      (integral_finsetSum _ (fun a _ => hbranch a)).symm
    _ ≤ ∫ x, ((1 / 2 : ℝ) * ∑ i, ‖d i x‖ ^ 2 + scalar x) + C * ‖ψ x‖ ^ 2 ∂μ :=
      integral_mono (integrable_finsetSum _ (fun a _ => hbranch a))
        (hsource.add (hmass.const_mul C))
        (partitionFormDensity_sum_le f direction hd hpos hpart d ψ scalar C hmetric)
    _ = _ := by rw [integral_add hsource (hmass.const_mul C), integral_const_mul]

end ElectronicIMS

section TraceIMS

variable {H X Ω K α ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Ω] [NormedSpace ℝ Ω] [MeasurableSpace Ω]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [Fintype α] [Fintype ι]
  {A : Gaussian.RankOneData H X} {Tr : RemovalState.PositiveTraceData X}

/-- Universal spatial covariant-form matching for one finite-energy
vector. The integrals are the original and multiplied closed form, not
estimates on them. Only the complete shifted form must be nonnegative. -/
structure ElectronicIMSSource (energy : RemovalState.PositiveForm Tr)
    (μ : Measure Ω) (f : α → Ω → ℝ) (direction : ι → Ω)
    (multiplier : α → H →L[ℂ] H) (v : H) where
  derivative : ι → Ω → K
  wave : Ω → K
  scalar : Ω → ℝ
  branch_integrable : ∀ a,
    Integrable (partitionFormDensity f direction derivative wave scalar a) μ
  source_integrable : Integrable
    (fun x => (1 / 2 : ℝ) * ∑ i, ‖derivative i x‖ ^ 2 + scalar x) μ
  mass_integrable : Integrable (fun x => ‖wave x‖ ^ 2) μ
  mass_eq : (∫ x, ‖wave x‖ ^ 2 ∂μ) = ‖v‖ ^ 2
  original_form : (energy.expectation (A.rankOne v)).toReal =
    ∫ x, (1 / 2 : ℝ) * ∑ i, ‖derivative i x‖ ^ 2 + scalar x ∂μ
  branch_finite : ∀ a, energy.expectation (A.rankOne (multiplier a v)) < ⊤
  branch_form : ∀ a, (energy.expectation (A.rankOne (multiplier a v))).toReal =
    ∫ x, partitionFormDensity f direction derivative wave scalar a x ∂μ

omit [CompleteSpace X] in
theorem ElectronicIMSSource.bound
    {energy : RemovalState.PositiveForm Tr}
    {μ : Measure Ω} {f : α → Ω → ℝ} {direction : ι → Ω}
    {multiplier : α → H →L[ℂ] H} {v : H}
    (S : ElectronicIMSSource (A := A) (K := K) energy μ f direction multiplier v)
    (hd : ∀ a, Differentiable ℝ (f a)) (hpos : ∀ a x, 0 ≤ f a x)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    {C : ℝ} (hC : 0 ≤ C) (hmetric : ∀ x,
      (1 / 2 : ℝ) * ∑ i, ∑ a, fderiv ℝ (f a) x (direction i) ^ 2 ≤ C)
    (selected : α) (hfinite : energy.expectation (A.rankOne v) < ⊤) :
    energy.expectation (A.rankOne (multiplier selected v)) ≤
      energy.expectation (A.rankOne v) + ENNReal.ofReal (C * ‖v‖ ^ 2) := by
  have h := partitionFormDensity_integral_bound μ f direction hd hpos hpart
    S.derivative S.wave S.scalar C hmetric S.branch_integrable S.source_integrable
    S.mass_integrable (fun a => S.branch_form a ▸ ENNReal.toReal_nonneg) selected
  rw [S.mass_eq, ← S.original_form, ← S.branch_form] at h
  rw [← ENNReal.ofReal_toReal (S.branch_finite selected).ne,
    ← ENNReal.ofReal_toReal hfinite.ne,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg (mul_nonneg hC (sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal h

omit [CompleteSpace X] in
/-- Any continuous electronic compression lifts the derived pure IMS
bound along the original source expansion. The mass term is its actual
trace, so a normalized source incurs precisely the scalar IMS cost. -/
theorem normal_electronic_ims
    (N : NormalTraceData A) (energy : RemovalState.PositiveForm Tr)
    (hpositive : A.positive ⊆ Tr.positive)
    (compression : X →L[ℝ] X) (multiplier : H →L[ℂ] H)
    (hcompression : ∀ v, compression (A.rankOne v) = A.rankOne (multiplier v))
    {C : ℝ} (hC : 0 ≤ C)
    (hvector : ∀ v, energy.expectation (A.rankOne v) < ⊤ →
      energy.expectation (A.rankOne (multiplier v)) ≤
        energy.expectation (A.rankOne v) + ENNReal.ofReal (C * ‖v‖ ^ 2))
    {x : X} (hx : x ∈ A.positive) (hfinite : energy.expectation x < ⊤) :
    compression x ∈ A.positive ∧
      energy.expectation (compression x) ≤ energy.expectation x + ENNReal.ofReal (C * A.trace x) := by
  obtain ⟨v, hv⟩ := N.positive_decomposition x hx
  have hout : HasSum (fun n => A.rankOne (multiplier (v n))) (compression x) := by
    simpa only [hcompression] using compression.hasSum hv
  have hpos : compression x ∈ A.positive := by
    apply A.closed_positive.mem_of_tendsto hout
    apply Eventually.of_forall
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using A.zero_positive
    | @insert n s hn ih =>
      simpa only [Finset.sum_insert hn] using A.add_positive (A.rankOne_positive _) ih
  have he : energy.expectation x = ∑' n, energy.expectation (A.rankOne (v n)) := by
    rw [← hv.tsum_eq, energy.expectation_tsum hv.summable
      (fun n => hpositive (A.rankOne_positive _))]
  have hf n : energy.expectation (A.rankOne (v n)) < ⊤ :=
    (ENNReal.le_tsum n).trans_lt (he ▸ hfinite)
  have hm : HasSum (fun n => ‖v n‖ ^ 2) (A.trace x) := by
    simpa only [A.trace_rankOne] using A.trace.hasSum hv
  refine ⟨hpos, ?_⟩
  rw [← hout.tsum_eq, energy.expectation_tsum hout.summable
    (fun n => hpositive (A.rankOne_positive _)), he]
  calc
    _ ≤ ∑' n, (energy.expectation (A.rankOne (v n)) + ENNReal.ofReal (C * ‖v n‖ ^ 2)) :=
      ENNReal.tsum_le_tsum fun n => hvector (v n) (hf n)
    _ = _ := by
      rw [ENNReal.tsum_add, ← ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg hC (sq_nonneg _)) (hm.mul_left C).summable,
        (hm.mul_left C).tsum_eq]

end TraceIMS

section ElectronicCutoffs

variable {H X Ω K α ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Ω] [NormedSpace ℝ Ω] [MeasurableSpace Ω]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [Fintype α] [Fintype ι]
  {A : Gaussian.RankOneData H X} {Tr : RemovalState.PositiveTraceData X}

/-- A family of actual scalar multipliers and universal covariant graph
identifications. The IMS inequality is a theorem of this data. -/
structure ElectronicCutoffData (energy : RemovalState.PositiveForm Tr) where
  measure : Measure Ω
  partition : ℕ → α → Ω → ℝ
  direction : ι → Ω
  differentiable : ∀ l a, Differentiable ℝ (partition l a)
  nonneg : ∀ l a x, 0 ≤ partition l a x
  square_partition : ∀ l x, HasSum (fun a => partition l a x ^ 2) 1
  cost : ℕ → ℝ
  cost_nonneg : ∀ l, 0 ≤ cost l
  cost_zero : Tendsto cost atTop (𝓝 0)
  metric : ∀ l x,
    (1 / 2 : ℝ) * ∑ i, ∑ a, fderiv ℝ (partition l a) x (direction i) ^ 2 ≤ cost l
  multiplier : ℕ → α → H →L[ℂ] H
  selected : α
  compression : ℕ → X →L[ℝ] X
  compression_rankOne : ∀ l v,
    compression l (A.rankOne v) = A.rankOne (multiplier l selected v)
  source : ∀ l v, energy.expectation (A.rankOne v) < ⊤ →
    Nonempty (ElectronicIMSSource (A := A) (K := K) energy measure
      (partition l) direction (multiplier l) v)

omit [CompleteSpace X] in
/-- The full-form IMS bound on any normalized finite-energy source.
Its sign-indefinite electronic potential has already been included in
the spatial scalar density, before the other branches are discarded. -/
theorem ElectronicCutoffData.bound
    {energy : RemovalState.PositiveForm Tr}
    (L : ElectronicCutoffData (A := A) (Ω := Ω) (K := K) (α := α) (ι := ι) energy)
    (N : NormalTraceData A) (hpositive : A.positive ⊆ Tr.positive)
    (l : ℕ) {x : X} (hx : x ∈ A.positive)
    (hfinite : energy.expectation x < ⊤) (htrace : A.trace x = 1) :
    L.compression l x ∈ A.positive ∧
      energy.expectation (L.compression l x) ≤ energy.expectation x + ENNReal.ofReal (L.cost l) := by
  have h := normal_electronic_ims N energy hpositive (L.compression l)
    (L.multiplier l L.selected) (L.compression_rankOne l) (L.cost_nonneg l)
    (fun v hv => by
      obtain ⟨S⟩ := L.source l v hv
      exact S.bound (L.differentiable l) (L.nonneg l) (L.square_partition l)
        (L.cost_nonneg l) (L.metric l) L.selected hv) hx hfinite
  simpa only [htrace, mul_one] using h

end ElectronicCutoffs

section PhysicalElectronicCutoffs

open PhotonLocalizationKernelCutoffs SymmetricLift

variable {H X K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  {A : Gaussian.RankOneData H X} {Tr : RemovalState.PositiveTraceData X}

/-- The electronic family used in local compactness, with its actual
permutation-symmetric square partition and proved radius-dependent IMS
cost. Only the common physical graph/form identifications remain inputs. -/
noncomputable def ElectronicCutoffData.ofPhysicalPartition
    (electrons : ℕ) (energy : RemovalState.PositiveForm Tr)
    (μ : Measure (Fin electrons → ElectronicPosition))
    (multiplier : ℕ → (Fin electrons → Bool) → H →L[ℂ] H)
    (compression : ℕ → X →L[ℝ] X)
    (hcompression : ∀ l v,
      compression l (A.rankOne v) = A.rankOne (multiplier l (fun _ => false) v))
    (source : ∀ (l : ℕ) (v : H), energy.expectation (A.rankOne v) < ⊤ →
      Nonempty (ElectronicIMSSource (A := A) (K := K) energy μ
        (symmetricMultiplier (electronicPair ((l : ℝ) + 1)))
        (fun i : Fin electrons × Fin 3 => Pi.single i.1 (EuclideanSpace.single i.2 1))
        (multiplier l) v)) :
    ElectronicCutoffData (A := A) (Ω := Fin electrons → ElectronicPosition)
      (K := K) (α := Fin electrons → Bool) (ι := Fin electrons × Fin 3) energy where
  measure := μ
  partition l := symmetricMultiplier (electronicPair ((l : ℝ) + 1))
  direction i := Pi.single i.1 (EuclideanSpace.single i.2 1)
  differentiable l := symmetricElectronicPartition_differentiable _
  nonneg l := symmetricElectronicPartition_nonneg _
  square_partition l := symmetricElectronicPartition_hasSum_sq _
  cost l := 3 * electrons * electronicPartitionConstant / (2 * ((l : ℝ) + 1) ^ 2)
  cost_nonneg l := by
    have := electronicPartitionConstant_nonneg
    positivity
  cost_zero := physicalElectronicFamily_ims_cost_zero
  metric := symmetricElectronicPartition_ims_metric
  multiplier := multiplier
  selected := fun _ => false
  compression := compression
  compression_rankOne := hcompression
  source := source

end PhysicalElectronicCutoffs


section TestedCurrent

open PhotonLocalizationCurrent RemovalState

variable {H X ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [Fintype ι] {A : Gaussian.RankOneData H X} {Tr : PositiveTraceData X}
  {control : PositiveForm Tr} {current : FormObservable control}

/-- Actual first-order graph vectors for one tested current. Kernel
smallness is required after the compactly supported test is applied.
The untested field may have no uniform spatial error bound. -/
structure TestedCurrentSource (U : KrausIsometry H) (v : H)
    (test : ι → H →L[ℂ] H) (Z : ι → ℝ) (charge ε B : ℝ) where
  derivative : ι → H
  field : ι → H
  noise : ι → lp (fun _ : ℕ => H) 2
  localized : ι → lp (fun _ : ℕ => H) 2
  mass_le : ‖v‖ ≤ Real.sqrt (control.expectation (A.rankOne v)).toReal
  tested_field_le : ∀ i, ‖test i (field i)‖ ≤
    Z i * ε * B * Real.sqrt (control.expectation (A.rankOne v)).toReal
  graph : ∀ i, localized i = U (derivative i + (charge : ℂ) • field i) + noise i
  orthogonality : ∀ i w, ⟪U w, noise i⟫_ℂ = 0
  output_finite : control.expectation (pure A U v) < ⊤
  original_form : current.value (A.rankOne v) = (⟪v, ∑ i, test i (derivative i)⟫_ℂ).re
  coordinate_form : ∀ a, current.value (A.rankOne (U v a)) =
    (⟪U v a, ∑ i, test i (localized i a)⟫_ℂ).re

theorem TestedCurrentSource.bound
    (approximation : RelativeApproximation (R := A) control current)
    (N : NormalTraceData A) (hpositive : A.positive ⊆ Tr.positive)
    {U : KrausIsometry H} {v : H} {test : ι → H →L[ℂ] H}
    {Z : ι → ℝ} {charge ε B : ℝ}
    (S : TestedCurrentSource (A := A) (control := control) (current := current)
      U v test Z charge ε B)
    (hintertwine : ∀ i w a, U (test i w) a = test i (U w a))
    (hadjoint : ∀ i w a, U ((test i).adjoint w) a = (test i).adjoint (U w a)) :
    |current.value (pure A U v) - current.value (A.rankOne v)| ≤
      (|charge| * (∑ i, Z i) * ε * B) * (control.expectation (A.rankOne v)).toReal := by
  rw [pure_current_difference approximation N hpositive U v test hintertwine hadjoint
    S.derivative S.field S.noise S.localized charge S.graph S.orthogonality
    S.output_finite S.original_form S.coordinate_form]
  exact tested_current_correction_bound v test S.field Z ENNReal.toReal_nonneg
    S.mass_le S.tested_field_le

/-- Mixed tested-current error from graph and kernel data on the same
Kraus channel. No pure or mixed current error is an input. -/
theorem channel_current_of_sources
    (approximation : RelativeApproximation (R := A) control current)
    (N : NormalTraceData A) (hpositive : A.positive ⊆ Tr.positive)
    (U : KrausIsometry H) (test : ι → H →L[ℂ] H)
    (hintertwine : ∀ i w a, U (test i w) a = test i (U w a))
    (hadjoint : ∀ i w a, U ((test i).adjoint w) a = (test i).adjoint (U w a))
    (Z : ι → ℝ) (charge ε B : ℝ)
    (source : ∀ v, control.expectation (A.rankOne v) < ⊤ →
      Nonempty (TestedCurrentSource (A := A) (control := control) (current := current)
        U v test Z charge ε B))
    {x : X} (hx : x ∈ A.positive)
    (hin : control.expectation x < ⊤) (hout : control.expectation (N.extend U x) < ⊤) :
    |current.value (N.extend U x) - current.value x| ≤
      (|charge| * (∑ i, Z i) * ε * B) * (control.expectation x).toReal := by
  apply channel_current_bound approximation N hpositive U hx hin hout
  intro v hv
  obtain ⟨S⟩ := source v hv
  exact S.bound approximation N hpositive hintertwine hadjoint

end TestedCurrent

section CommonEnergy

open PhotonLocalizationFockChannel PhotonLocalizationFormBounds

variable {h H V X Q Ω K α ι Test : Type*}
  [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Ω] [NormedSpace ℝ Ω] [MeasurableSpace Ω]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [Fintype α] [Fintype ι]
  {A : Gaussian.RankOneData H X} {Tr : RemovalState.PositiveTraceData X}

/-- Common-model input for the sharp energy construction. These are
universal trace, form, graph and kernel identifications. In particular
the local kinetic sources are required only on the actual electronically
cut vectors. The physical realization of these identities is explicit,
and is stronger than a collection of unrelated cutoff lemmas. -/
structure CommonChannelEnergyData (D : PhotonLoss.LocalizationData X)
    (T : PhotonLoss.TraceData D Test) where
  normal : NormalTraceData A
  fock : FockFactorization h H
  forms : FockFormCalculus A Tr fock Q
  split : ℕ → h →ₗᵢ[ℂ] WithLp 2 (h × h)
  positive : A.positive ⊆ Tr.positive
  states_positive : D.states ⊆ A.positive
  trace_one : ∀ x ∈ D.states, A.trace x = 1
  channel : ∀ m x, x ∈ D.states → D.localize m x = normal.extend (fock.factor (split m)) x
  energy : RemovalState.PositiveForm Tr
  energy_match : ∀ x ∈ A.positive, T.energy x = energy.expectation x
  electronic : ElectronicCutoffData (A := A) (Ω := Ω) (K := K) (α := α) (ι := ι) energy
  cutoff_match : ∀ l x, x ∈ D.states → T.cutoff l x = electronic.compression l x
  multiplier_contraction : ∀ l v, ‖electronic.multiplier l electronic.selected v‖ ≤ ‖v‖
  cutoff_commute : ∀ l m v a,
    electronic.multiplier l electronic.selected (fock.factor (split m) v a) =
      fock.factor (split m) (electronic.multiplier l electronic.selected v) a
  kinetic : RemovalState.PositiveForm Tr
  potential : Bool → RemovalState.PositiveForm Tr
  control : RemovalState.PositiveForm Tr
  radiation : Q
  truncation : ℕ → Q
  radiationFamily : RadiationFamily V
  modes : (k : ℕ) → Fin k → h
  truncation_value : ∀ k u, forms.value (truncation k) u =
    ENNReal.ofReal (∑ i, ‖⟪modes k i, u⟫_ℂ‖ ^ 2)
  radiation_duality : ∀ m k u, forms.value radiation u < ⊤ → ∃ z : V,
    forms.value radiation u = ENNReal.ofReal (‖z‖ ^ 2) ∧
      ∀ i, ⟪modes k i, retainedMap (split m) u⟫_ℂ = ⟪radiationFamily.localized k m i, z⟫_ℂ
  potential_operator : Bool → ℕ → H →L[ℂ] H
  potential_trace : ∀ b n v, ((potential b).truncation n (A.rankOne v) : ℂ) =
    inner ℂ v (potential_operator b n v)
  potential_commute : ∀ m b n v a,
    fock.factor (split m) (potential_operator b n v) a =
      potential_operator b n (fock.factor (split m) v a)
  comparison : ℝ
  comparison_nonneg : 0 ≤ comparison
  reference_bound : ∀ x ∈ A.positive, energy.expectation x < ⊤ →
    control.expectation x ≤ ENNReal.ofReal (comparison * ((energy.expectation x).toReal + A.trace x))
  kinetic_le_control : ∀ x ∈ A.positive, kinetic.expectation x ≤ control.expectation x
  potential_le_control : ∀ b x, x ∈ A.positive → (potential b).expectation x ≤ control.expectation x
  radiation_le_control : ∀ x ∈ A.positive,
    (forms.observable radiation).expectation x ≤ control.expectation x
  full_form : ∀ x ∈ A.positive, energy.expectation x < ⊤ →
    (energy.expectation x).toReal = (kinetic.expectation x).toReal +
      ((potential true).expectation x).toReal - ((potential false).expectation x).toReal +
      ((forms.observable radiation).expectation x).toReal
  truncated_form : ∀ k x, x ∈ A.positive → kinetic.expectation x < ⊤ →
    (∀ b, (potential b).expectation x < ⊤) →
    (forms.observable (truncation k)).expectation x < ⊤ →
    T.truncatedEnergy k x = ENNReal.ofReal ((kinetic.expectation x).toReal +
      ((potential true).expectation x).toReal - ((potential false).expectation x).toReal +
      ((forms.observable (truncation k)).expectation x).toReal)
  charge : ℝ
  epsilon : ℕ → ℕ → ℝ
  epsilon_nonneg : ∀ l m, 0 ≤ epsilon l m
  epsilon_zero : ∀ l, Tendsto (epsilon l) atTop (𝓝 0)
  fieldConstant : ℕ → ℝ
  derivativeConstant : ℕ → ℝ
  fieldConstant_nonneg : ∀ l, 0 ≤ fieldConstant l
  derivativeConstant_nonneg : ∀ l, 0 ≤ derivativeConstant l
  kinetic_source : ∀ l m v, energy.expectation (A.rankOne v) < ⊤ →
    Nonempty (KineticDilationSource (A := A) (ι := ι) kinetic control
      (fock.factor (split m)) (electronic.multiplier l electronic.selected v)
      charge (epsilon l m) (fieldConstant l) (derivativeConstant l))

namespace CommonChannelEnergyData

variable {D : PhotonLoss.LocalizationData X} {T : PhotonLoss.TraceData D Test}
  (S : CommonChannelEnergyData (A := A) (Tr := Tr) (h := h) (V := V)
    (Q := Q) (Ω := Ω) (K := K) (α := α) (ι := ι) D T)

def cap (E : ℝ) (l : ℕ) : ℝ :=
  S.comparison * (max E 0 + S.electronic.cost l + 1)

omit [CompleteSpace X] in
theorem cap_nonneg (E : ℝ) (l : ℕ) : 0 ≤ S.cap E l :=
  mul_nonneg S.comparison_nonneg (by
    have := S.electronic.cost_nonneg l
    have := le_max_right E 0
    linarith)

def localError (E : ℝ) (l k m : ℕ) : ℝ :=
  kineticError ι S.charge (S.fieldConstant l) (S.derivativeConstant l) (S.epsilon l m) *
    S.cap E l + S.radiationFamily.error k m * S.cap E l

omit [CompleteSpace X] in
theorem localError_zero (E : ℝ) (l k : ℕ) :
    Tendsto (S.localError E l k) atTop (𝓝 0) :=
  sharp_channel_energy_error_zero S.radiationFamily k (S.epsilon l)
    (S.epsilon_zero l) S.charge (S.fieldConstant l) (S.derivativeConstant l)
    (S.cap E l) (S.cap E l)

omit [CompleteSpace X] in
theorem compression_trace_le (l : ℕ) {x : X} (hx : x ∈ A.positive) :
    A.trace (S.electronic.compression l x) ≤ A.trace x := by
  obtain ⟨v, hv⟩ := S.normal.positive_decomposition x hx
  have hmass : HasSum (fun n => ‖v n‖ ^ 2) (A.trace x) := by
    simpa only [A.trace_rankOne] using A.trace.hasSum hv
  have hcut : HasSum (fun n => ‖S.electronic.multiplier l S.electronic.selected (v n)‖ ^ 2)
      (A.trace (S.electronic.compression l x)) := by
    simpa only [S.electronic.compression_rankOne, A.trace_rankOne] using
      A.trace.hasSum ((S.electronic.compression l).hasSum hv)
  rw [← hcut.tsum_eq, ← hmass.tsum_eq]
  exact Summable.tsum_le_tsum (fun n =>
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (S.multiplier_contraction l (v n)))
    hcut.summable hmass.summable

/-- The sharp combined cutoff estimate on the common normal channel.
Electronic IMS is derived from the finite square partition, and the
photon estimate is applied only to the actual cut source vectors. -/
theorem combined_bound (E e : ℝ) (l k m : ℕ) {x : X} (hx : x ∈ D.states)
    (he : 0 ≤ e) (hE : T.energy x ≤ ENNReal.ofReal E)
    (hebound : T.energy x ≤ ENNReal.ofReal e) :
    T.truncatedEnergy k (T.cutoff l (D.localize m x)) ≤
      ENNReal.ofReal (e + S.electronic.cost l + S.localError E l k m) := by
  have hxpos := S.states_positive hx
  rw [S.energy_match x hxpos] at hE hebound
  have hxfinite := hE.trans_lt ENNReal.ofReal_lt_top
  obtain ⟨hcutpos, hcut⟩ := S.electronic.bound S.normal S.positive l hxpos hxfinite (S.trace_one x hx)
  have hcost := S.electronic.cost_nonneg l
  have hcutE : S.energy.expectation (S.electronic.compression l x) ≤
      ENNReal.ofReal (max E 0 + S.electronic.cost l) := by
    apply hcut.trans
    rw [ENNReal.ofReal_add (le_max_right E 0) hcost, ENNReal.ofReal_max, ENNReal.ofReal_zero,
      max_eq_left zero_le]
    exact add_le_add hE le_rfl
  have hcute : S.energy.expectation (S.electronic.compression l x) ≤
      ENNReal.ofReal (e + S.electronic.cost l) := by
    rw [ENNReal.ofReal_add he hcost]
    exact hcut.trans (add_le_add hebound le_rfl)
  have hcutfinite := hcutE.trans_lt ENNReal.ofReal_lt_top
  have hcutReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcutE
  rw [ENNReal.toReal_ofReal (add_nonneg (le_max_right E 0) hcost)] at hcutReal
  have htrace := S.compression_trace_le l hxpos
  rw [S.trace_one x hx] at htrace
  have hcontrol : S.control.expectation (S.electronic.compression l x) ≤ ENNReal.ofReal (S.cap E l) :=
    (S.reference_bound _ hcutpos hcutfinite).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (add_le_add hcutReal htrace) S.comparison_nonneg))
  have hcontrolfinite := hcontrol.trans_lt ENNReal.ofReal_lt_top
  have hsource : (S.kinetic.expectation (S.electronic.compression l x)).toReal +
      ((S.potential true).expectation (S.electronic.compression l x)).toReal -
      ((S.potential false).expectation (S.electronic.compression l x)).toReal +
      ((S.forms.observable S.radiation).expectation (S.electronic.compression l x)).toReal ≤
        e + S.electronic.cost l := by
    rw [← S.full_form _ hcutpos hcutfinite]
    simpa only [ENNReal.toReal_ofReal (add_nonneg he hcost)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hcute
  obtain ⟨v, hv⟩ := S.normal.positive_decomposition x hxpos
  have hvfinite n : S.energy.expectation (A.rankOne (v n)) < ⊤ := by
    have hs : (∑' n, S.energy.expectation (A.rankOne (v n))) = S.energy.expectation x := by
      rw [← S.energy.expectation_tsum hv.summable
        (fun n => S.positive (A.rankOne_positive _)), hv.tsum_eq]
    exact (ENNReal.le_tsum n).trans_lt (hs ▸ hxfinite)
  have hvcut : HasSum (fun n => A.rankOne (S.electronic.multiplier l S.electronic.selected (v n)))
      (S.electronic.compression l x) := by
    simpa only [S.electronic.compression_rankOne] using (S.electronic.compression l).hasSum hv
  obtain ⟨hk, hp, hr, hb⟩ := sharp_channel_signed_energy_bound S.forms S.normal S.positive
    S.kinetic S.control S.potential S.radiationFamily S.radiation S.truncation
    m k (S.split m) (S.modes k) (S.truncation_value k) (S.radiation_duality m k)
    S.potential_operator S.potential_trace (S.potential_commute m)
    (S.epsilon_nonneg l m) (S.fieldConstant_nonneg l) (S.derivativeConstant_nonneg l)
    (S.cap_nonneg E l) (S.cap_nonneg E l) hcutpos
    (fun n => S.electronic.multiplier l S.electronic.selected (v n)) hvcut
    (fun n _ => S.kinetic_source l m (v n) (hvfinite n))
    ((S.kinetic_le_control _ hcutpos).trans_lt hcontrolfinite)
    (fun b => (S.potential_le_control b _ hcutpos).trans_lt hcontrolfinite)
    hcontrol ((S.radiation_le_control _ hcutpos).trans hcontrol) hsource
  have hcommute : T.cutoff l (D.localize m x) =
      S.normal.extend (S.fock.factor (S.split m)) (S.electronic.compression l x) := by
    rw [S.cutoff_match l _ (D.localize_state m x hx), S.channel m x hx]
    exact S.normal.compression_commutes _ _ _ (S.electronic.compression_rankOne l)
      (S.cutoff_commute l m) hxpos
  rw [hcommute, S.truncated_form k _ (S.normal.positive _ hcutpos) hk hp hr]
  exact ENNReal.ofReal_le_ofReal (by simpa only [localError, add_assoc] using hb)

end CommonChannelEnergyData

end CommonEnergy

section CommonCurrent

open PhotonLocalizationCurrent RemovalState

variable {h H V X Q Ω K α ι Test : Type*}
  [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Ω] [NormedSpace ℝ Ω] [MeasurableSpace Ω]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [Fintype α] [Fintype ι]
  {A : Gaussian.RankOneData H X} {Tr : PositiveTraceData X}
  {D : PhotonLoss.LocalizationData X} {T : PhotonLoss.TraceData D Test}

/-- Tested graph identities for the same normal channel used in energy
and compactness. The relative approximation is a universal current
construction, while the source graph and tested kernel matchings remain
explicit physical obligations. -/
structure CommonChannelCurrentData
    (S : CommonChannelEnergyData (A := A) (Tr := Tr) (h := h) (V := V)
      (Q := Q) (Ω := Ω) (K := K) (α := α) (ι := ι) D T) where
  control : Test → PositiveForm Tr
  current : (t : Test) → FormObservable (control t)
  approximation : ∀ t, RelativeApproximation (R := A) (control t) (current t)
  test_match : ∀ t x, x ∈ A.positive → (control t).expectation x < ⊤ →
    T.test t x = (current t).value x
  comparison : Test → ℝ
  comparison_nonneg : ∀ t, 0 ≤ comparison t
  reference_bound : ∀ t x, x ∈ A.positive → S.energy.expectation x < ⊤ →
    (control t).expectation x ≤
      ENNReal.ofReal (comparison t * ((S.energy.expectation x).toReal + A.trace x))
  testOperator : Test → ι → H →L[ℂ] H
  test_commute : ∀ t m i v a,
    S.fock.factor (S.split m) (testOperator t i v) a =
      testOperator t i (S.fock.factor (S.split m) v a)
  test_adjoint_commute : ∀ t m i v a,
    S.fock.factor (S.split m) ((testOperator t i).adjoint v) a =
      (testOperator t i).adjoint (S.fock.factor (S.split m) v a)
  weight : Test → ι → ℝ
  weight_nonneg : ∀ t i, 0 ≤ weight t i
  epsilon : Test → ℕ → ℝ
  epsilon_nonneg : ∀ t m, 0 ≤ epsilon t m
  epsilon_zero : ∀ t, Tendsto (epsilon t) atTop (𝓝 0)
  fieldConstant : Test → ℝ
  fieldConstant_nonneg : ∀ t, 0 ≤ fieldConstant t
  source : ∀ t m v, (control t).expectation (A.rankOne v) < ⊤ →
    Nonempty (TestedCurrentSource (A := A) (control := control t) (current := current t)
      (S.fock.factor (S.split m)) v (testOperator t) (weight t)
      S.charge (epsilon t m) (fieldConstant t))

namespace CommonChannelCurrentData

variable {S : CommonChannelEnergyData (A := A) (Tr := Tr) (h := h) (V := V)
    (Q := Q) (Ω := Ω) (K := K) (α := α) (ι := ι) D T}
  (J : CommonChannelCurrentData S)

def cap (E : ℝ) (t : Test) : ℝ := J.comparison t * (max E 0 + 1)

omit [CompleteSpace X] in
theorem cap_nonneg (E : ℝ) (t : Test) : 0 ≤ J.cap E t :=
  mul_nonneg (J.comparison_nonneg t) (by have := le_max_right E 0; linarith)

def error (E : ℝ) (t : Test) (m : ℕ) : ℝ :=
  (|S.charge| * (∑ i, J.weight t i) * J.epsilon t m * J.fieldConstant t) * J.cap E t

omit [CompleteSpace X] in
theorem error_zero (E : ℝ) (t : Test) : Tendsto (J.error E t) atTop (𝓝 0) := by
  unfold error
  simpa only [mul_zero, zero_mul] using
    (((J.epsilon_zero t).const_mul (|S.charge| * ∑ i, J.weight t i)).mul_const
      (J.fieldConstant t)).mul_const (J.cap E t)

omit [CompleteSpace X] in
theorem state_control_bound (E : ℝ) (t : Test) {x : X} (hx : x ∈ D.states)
    (hE : T.energy x ≤ ENNReal.ofReal E) :
    (J.control t).expectation x ≤ ENNReal.ofReal (J.cap E t) := by
  have hxpos := S.states_positive hx
  rw [S.energy_match x hxpos] at hE
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE
  rw [ENNReal.toReal_ofReal'] at hreal
  apply (J.reference_bound t x hxpos (hE.trans_lt ENNReal.ofReal_lt_top)).trans
  apply ENNReal.ofReal_le_ofReal
  rw [S.trace_one x hx]
  exact mul_le_mul_of_nonneg_left (add_le_add hreal le_rfl) (J.comparison_nonneg t)

/-- The uniform tested-current localization error, with output domain
membership obtained from the independently constructed coarse bound. -/
theorem test_bound (C : CoarseData D T) (E : ℝ) (t : Test) (m : ℕ)
    {x : X} (hx : x ∈ D.states) (hE : T.energy x ≤ ENNReal.ofReal E) :
    |T.test t (D.localize m x) - T.test t x| ≤ J.error E t m := by
  have hin := J.state_control_bound E t hx hE
  have hout := J.state_control_bound (C.rough E) t (D.localize_state m x hx)
    (C.rough_bound E m x hx hE)
  have hinfinite := hin.trans_lt ENNReal.ofReal_lt_top
  have houtfinite := hout.trans_lt ENNReal.ofReal_lt_top
  rw [J.test_match t _ (S.states_positive (D.localize_state m x hx)) houtfinite,
    J.test_match t x (S.states_positive hx) hinfinite, S.channel m x hx]
  rw [S.channel m x hx] at houtfinite
  have h := channel_current_of_sources (J.approximation t) S.normal S.positive
    (S.fock.factor (S.split m)) (J.testOperator t) (J.test_commute t m)
    (J.test_adjoint_commute t m) (J.weight t) S.charge (J.epsilon t m)
    (J.fieldConstant t) (J.source t m) (S.states_positive hx) hinfinite houtfinite
  apply h.trans
  apply mul_le_mul_of_nonneg_left
  · simpa only [ENNReal.toReal_ofReal (J.cap_nonneg E t)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hin
  · exact mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
      (Finset.sum_nonneg fun i _ => J.weight_nonneg t i)) (J.epsilon_nonneg t m))
      (J.fieldConstant_nonneg t)

end CommonChannelCurrentData

/-- All fields of the localization-estimate interface are constructed
on one common channel. The inputs expose the physical graph and form
matching still needed to instantiate the article's specific model.
No sharp energy, current or electronic cutoff inequality is an input. -/
noncomputable def localizationEstimates_of_commonChannel
    (C : CoarseData D T)
    (S : CommonChannelEnergyData (A := A) (Tr := Tr) (h := h) (V := V)
      (Q := Q) (Ω := Ω) (K := K) (α := α) (ι := ι) D T)
    (J : CommonChannelCurrentData S) : PhotonLoss.LocalizationEstimates D T where
  electronicTight := C.electronicTight
  precompact := C.precompact
  rough := C.rough
  rough_bound := C.rough_bound
  imsError := S.electronic.cost
  imsError_zero := S.electronic.cost_zero
  localError := S.localError
  localError_zero := S.localError_zero
  combined_bound E e l k m _x hx he hE he' := S.combined_bound E e l k m hx he hE he'
  testError := J.error
  testError_zero := J.error_zero
  test_bound E t m _x hx hE := J.test_bound C E t m hx hE

end CommonCurrent

end GptLean.PhotonLocalization
