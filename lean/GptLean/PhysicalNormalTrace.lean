import GptLean.PhysicalElectronicFermions

/-!
One universal normal trace realization for all Hilbert spaces.

The background consists of ordinary trace-class representation, positive
spectral decomposition, the trace ideal action of arbitrary bounded maps,
and partial trace of arbitrary isometric dilations. Its fields contain no
Hamiltonian, cutoff, constraint, removal construction, or attainment claim.
All positivity, trace conservation, compatibility with the positive-form
interface, and fermionic source support are derived below.
-/

noncomputable section

namespace GptLean.PhysicalNormalTrace

open PhotonLocalizationChannel RemovalState Filter Topology
open scoped InnerProductSpace ComplexOrder

section Cone

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  {R : Gaussian.RankOneData H T}

theorem rankOne_real_smul (F : NormalFunctionalData R) (r : ℝ) (v : H) :
    R.rankOne ((r : ℂ) • v) = r ^ 2 • R.rankOne v := by
  apply F.isometry.injective
  ext B
  simp only [map_smul, F.rankOne, smul_apply,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, Complex.real_smul]
  push_cast
  ring

theorem positive_smul (normal : NormalTraceData R) (F : NormalFunctionalData R)
    {x : T} (hx : x ∈ R.positive) {r : ℝ} (hr : 0 ≤ r) : r • x ∈ R.positive := by
  obtain ⟨v, hv⟩ := normal.positive_decomposition x hx
  have hs := hv.const_smul r
  have he (n : ℕ) : r • R.rankOne (v n) = R.rankOne ((Real.sqrt r : ℂ) • v n) := by
    rw [rankOne_real_smul F, Real.sq_sqrt hr]
  simp_rw [he] at hs
  apply R.closed_positive.mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using R.zero_positive
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      R.add_positive (R.rankOne_positive ((Real.sqrt r : ℂ) • v a)) ih

theorem positive_convex (normal : NormalTraceData R) (F : NormalFunctionalData R) :
    Convex ℝ R.positive := by
  intro x hx y hy a b ha hb _
  exact R.add_positive (positive_smul normal F hx ha) (positive_smul normal F hy hb)

variable [CompleteSpace T]

theorem norm_eq_trace (normal : NormalTraceData R) (F : NormalFunctionalData R)
    {x : T} (hx : x ∈ R.positive) : ‖x‖ = R.trace x := by
  let : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
  have hn : ‖F.repr x‖ = ‖x‖ := by
    simpa only [map_zero, dist_zero_right] using F.isometry.dist_eq x 0
  rw [← hn, PhotonTrace.IsPosFunctional.opNorm_eq (F.positive normal hx), F.mass normal hx]

/-- The positive cone and trace in the form interface are constructed
from exactly the same normal rank-one representation. -/
def positiveTrace (normal : NormalTraceData R) (F : NormalFunctionalData R) :
    PositiveTraceData T where
  trace := R.trace
  positive := R.positive
  closed_positive := R.closed_positive
  convex_positive := positive_convex normal F
  zero_positive := R.zero_positive
  add_positive := R.add_positive
  norm_eq_trace := norm_eq_trace normal F

end Cone

section FermionicChannel

variable {N : ℕ} {H T : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData (PhysicalElectronicFermions.FullSpace N H) T}

theorem preserves_fermionic_states (normal : NormalTraceData R) (C : NormalConjugationData R)
    (U : KrausIsometry (PhysicalElectronicFermions.FullSpace N H)) (A : ℕ → H →L[ℂ] H)
    (hcoordinates : ∀ v a, U v a = (A a).compLpL 2 MeasureTheory.volume v)
    {x : T} (hx : x ∈ PhysicalElectronicFermions.states C) :
    normal.extend U x ∈ PhysicalElectronicFermions.states C := by
  obtain ⟨v, hv, hchar⟩ :=
    (PhysicalElectronicFermions.compression_fixed_iff C normal hx.1).mp hx.2.2
  have hp := normal.positive U hx.1
  refine ⟨hp, (normal.trace U hx.1).trans hx.2.1, ?_⟩
  apply (PhysicalElectronicFermions.compression_fixed_iff C normal hp).mpr
  refine ⟨Repair.flattenVectors (fun n a => U (v n) a), normal.mixed_hasSum U hv, ?_⟩
  intro n
  change Repair.HasElectronicCharacter _ _ (U (v (Nat.unpair n).1) (Nat.unpair n).2)
  rw [hcoordinates]
  exact PhysicalElectronicFermions.fiberOperator_character N H
    (A (Nat.unpair n).2) (v (Nat.unpair n).1) (hchar (Nat.unpair n).1)

end FermionicChannel

/-- A real Banach space, bundled to choose the standard trace space for
each Hilbert space without choosing an article-specific state model. -/
structure TraceBanachSpace where
  Carrier : Type
  [normed : NormedAddCommGroup Carrier]
  [space : NormedSpace ℝ Carrier]
  [complete : CompleteSpace Carrier]

attribute [instance] TraceBanachSpace.normed TraceBanachSpace.space TraceBanachSpace.complete

/-- The ordinary normal trace representation on a fixed Hilbert space.
The countable vectors are square-root eigenvectors, so no normalization
or particular observable is built into the spectral theorem. -/
structure Realization (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  traceSpace : TraceBanachSpace
  rank : Gaussian.RankOneData H traceSpace.Carrier
  functional : NormalFunctionalData rank
  spectral : ∀ x ∈ rank.positive, ∃ v : ℕ → H,
    HasSum (fun n => rank.rankOne (v n)) x

/-- Named universal operator-theory background. Every bounded map and
every countable Hilbert dilation has its ordinary trace-ideal action.
The same family is used for both sides of every map. -/
structure StandardNormalTraceBackground where
  realization : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H], Realization H
  push : ∀ {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
    (H →L[ℂ] K) → (realization H).traceSpace.Carrier →L[ℝ] (realization K).traceSpace.Carrier
  push_rankOne : ∀ {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (B : H →L[ℂ] K) (v : H),
    push B ((realization H).rank.rankOne v) = (realization K).rank.rankOne (B v)
  partialTrace : ∀ {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
    (H →ₗᵢ[ℂ] lp (fun _ : ℕ => K) 2) →
      (realization H).traceSpace.Carrier →L[ℝ] (realization K).traceSpace.Carrier
  partialTrace_rankOne : ∀ {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => K) 2) (v : H),
    partialTrace U ((realization H).rank.rankOne v) =
      ∑' n, (realization K).rank.rankOne (U v n)

namespace StandardNormalTraceBackground

variable (B : StandardNormalTraceBackground)

abbrev Trace (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  (B.realization H).traceSpace.Carrier

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def normal : NormalTraceData (B.realization H).rank where
  extend := B.partialTrace
  extend_rankOne := B.partialTrace_rankOne
  positive_decomposition := (B.realization H).spectral

def conjugation : NormalConjugationData (B.realization H).rank where
  conjugate := B.push
  rankOne := B.push_rankOne

def traceData : PositiveTraceData (B.Trace H) :=
  positiveTrace B.normal (B.realization H).functional

@[simp] theorem traceData_positive : (B.traceData (H := H)).positive = (B.realization H).rank.positive := rfl

@[simp] theorem traceData_trace : (B.traceData (H := H)).trace = (B.realization H).rank.trace := rfl

theorem push_positive (L : H →L[ℂ] K) {x : B.Trace H}
    (hx : x ∈ (B.realization H).rank.positive) :
    B.push L x ∈ (B.realization K).rank.positive := by
  obtain ⟨v, hv⟩ := (B.realization H).spectral x hx
  have hs := (B.push L).hasSum hv
  simp only [B.push_rankOne] at hs
  apply (B.realization K).rank.closed_positive.mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using (B.realization K).rank.zero_positive
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (B.realization K).rank.add_positive ((B.realization K).rank.rankOne_positive (L (v a))) ih

theorem push_trace_isometry (L : H →ₗᵢ[ℂ] K) {x : B.Trace H}
    (hx : x ∈ (B.realization H).rank.positive) :
    (B.realization K).rank.trace (B.push L.toContinuousLinearMap x) =
      (B.realization H).rank.trace x := by
  obtain ⟨v, hv⟩ := (B.realization H).spectral x hx
  have h₁ := (B.realization K).rank.trace.hasSum ((B.push L.toContinuousLinearMap).hasSum hv)
  have h₂ := (B.realization H).rank.trace.hasSum hv
  simp only [B.push_rankOne, (B.realization K).rank.trace_rankOne,
    LinearIsometry.coe_toContinuousLinearMap, L.norm_map] at h₁
  simp only [(B.realization H).rank.trace_rankOne] at h₂
  exact h₁.unique h₂

omit [CompleteSpace H] [CompleteSpace K] in
theorem dilation_mass (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => K) 2) (v : H) :
    HasSum (fun n => ‖U v n‖ ^ 2) (‖v‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, U.norm_map] using
    lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (U v)

theorem partialTrace_pure_positive (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => K) 2) (v : H) :
    B.partialTrace U ((B.realization H).rank.rankOne v) ∈ (B.realization K).rank.positive := by
  rw [B.partialTrace_rankOne]
  exact Repair.rankOneSeries_positive (B.realization K).rank (dilation_mass U v)

theorem partialTrace_pure_trace (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => K) 2) (v : H) :
    (B.realization K).rank.trace (B.partialTrace U ((B.realization H).rank.rankOne v)) = ‖v‖ ^ 2 := by
  rw [B.partialTrace_rankOne]
  exact Repair.rankOneSeries_trace (B.realization K).rank (dilation_mass U v)

theorem partialTrace_positive (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => K) 2) {x : B.Trace H}
    (hx : x ∈ (B.realization H).rank.positive) :
    B.partialTrace U x ∈ (B.realization K).rank.positive := by
  obtain ⟨v, hv⟩ := (B.realization H).spectral x hx
  apply (B.realization K).rank.closed_positive.mem_of_tendsto ((B.partialTrace U).hasSum hv)
  apply Filter.Eventually.of_forall
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using (B.realization K).rank.zero_positive
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (B.realization K).rank.add_positive (B.partialTrace_pure_positive U (v a)) ih

theorem partialTrace_trace (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => K) 2) {x : B.Trace H}
    (hx : x ∈ (B.realization H).rank.positive) :
    (B.realization K).rank.trace (B.partialTrace U x) = (B.realization H).rank.trace x := by
  obtain ⟨v, hv⟩ := (B.realization H).spectral x hx
  have h₁ := (B.realization K).rank.trace.hasSum ((B.partialTrace U).hasSum hv)
  have h₂ := (B.realization H).rank.trace.hasSum hv
  simp only [B.partialTrace_pure_trace] at h₁
  simp only [(B.realization H).rank.trace_rankOne] at h₂
  exact h₁.unique h₂

abbrev FullHilbert (N : ℕ) := PhysicalElectronicFermions.FullSpace N PhysicalFock.PhotonFock

abbrev FermionicHilbert (N : ℕ) := PhysicalElectronicFermions.PhotonSpace N

abbrev FullTrace (N : ℕ) := B.Trace (FullHilbert N)

abbrev FermionicTrace (N : ℕ) := B.Trace (FermionicHilbert N)

def fermionicCompression (N : ℕ) : B.FullTrace N →L[ℝ] B.FullTrace N :=
  PhysicalElectronicFermions.compression (B.conjugation (H := FullHilbert N))

def fermionicStates (N : ℕ) : Set (B.FullTrace N) :=
  PhysicalElectronicFermions.states (B.conjugation (H := FullHilbert N))

theorem fermionicStates_closed (N : ℕ) : IsClosed (B.fermionicStates N) :=
  PhysicalElectronicFermions.states_closed _

theorem fermionicState_sources (N : ℕ) {x : B.FullTrace N}
    (hx : x ∈ B.fermionicStates N) :
    ∃ v : ℕ → FullHilbert N, HasSum (fun n => (B.realization (FullHilbert N)).rank.rankOne (v n)) x ∧
      ∀ n, Repair.HasElectronicCharacter (fun π => SymmetricLift.permuteConfiguration π)
        (PhysicalElectronicFermions.signCharacter N) (v n) :=
  (PhysicalElectronicFermions.compression_fixed_iff B.conjugation B.normal hx.1).mp hx.2.2

/-- A photon channel whose Kraus coordinates act on the fiber preserves
the actual closed fermionic normal state set. Electronic commutation or
sector stability is not an additional hypothesis. -/
theorem fermionicStates_channel (N : ℕ) (U : KrausIsometry (FullHilbert N))
    (A : ℕ → PhysicalFock.PhotonFock →L[ℂ] PhysicalFock.PhotonFock)
    (hcoordinates : ∀ v a, U v a = (A a).compLpL 2 MeasureTheory.volume v)
    {x : B.FullTrace N} (hx : x ∈ B.fermionicStates N) :
    (B.normal (H := FullHilbert N)).extend U x ∈ B.fermionicStates N :=
  preserves_fermionic_states (B.normal (H := FullHilbert N))
    (B.conjugation (H := FullHilbert N)) U A hcoordinates hx

end StandardNormalTraceBackground
end GptLean.PhysicalNormalTrace
