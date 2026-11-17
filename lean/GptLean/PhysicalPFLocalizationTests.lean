import GptLean.PhysicalPFLocalizationControl
import GptLean.PhysicalNormalCompression
import GptLean.PhotonLocalizationEstimatesAssembly

/-!
The actual density and component-current tests are written in the common
finite-coordinate format used by the localization channel. Their pure
values and their operator commutation laws follow from the constructed
normal observables and scalar spatial multipliers.
-/

noncomputable section

namespace GptLean.PhysicalPFLocalization

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalPFSource PhysicalPFStates PhysicalPairSpace
  PhotonLocalization PhotonLocalizationChannel
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
set_option Elab.async false

section Sparse
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype ι] [DecidableEq ι]

private def sparseOperator (j : ι) (c : ℝ) (A : H →L[ℂ] H) (q : ι) : H →L[ℂ] H :=
  if q = j then c • A else 0

omit [CompleteSpace H] in
private theorem sparse_sum (j : ι) (c : ℝ) (A : H →L[ℂ] H) (d : ι → H) :
    (∑ q, sparseOperator j c A q (d q)) = c • A (d j) := by
  have h (q : ι) : sparseOperator j c A q (d q) =
      if q = j then c • A (d q) else 0 := by
    by_cases hq : q = j <;> simp only [sparseOperator, hq, ite_true, ite_false, smul_apply, zero_apply]
  simp_rw [h]
  simp

private theorem real_scale_selfadjoint (c : ℝ) (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) : IsSelfAdjoint (c • A) := by
  have hc : IsSelfAdjoint (c : ℂ) := by simp [isSelfAdjoint_iff]
  simpa only [Complex.coe_smul] using hc.smul hA

omit [Fintype ι] in
private theorem sparse_selfadjoint (j : ι) (c : ℝ) (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (q : ι) : IsSelfAdjoint (sparseOperator j c A q) := by
  by_cases hq : q = j
  · simpa only [sparseOperator, hq, ite_true] using real_scale_selfadjoint c A hA
  · simpa only [sparseOperator, hq, ite_false] using (IsSelfAdjoint.zero (H →L[ℂ] H))

omit [CompleteSpace H] [Fintype ι] in
private theorem sparse_commute (j : ι) (c : ℝ) (A L : H →L[ℂ] H)
    (h : ∀ v, L (A v) = A (L v)) (q : ι) (v : H) :
    L (sparseOperator j c A q v) = sparseOperator j c A q (L v) := by
  by_cases hq : q = j
  · simp only [sparseOperator, hq, ite_true, smul_apply, ContinuousLinearMap.map_smul_of_tower]
    exact congrArg (fun w : H => c • w) (h v)
  · simp only [sparseOperator, hq, ite_false, zero_apply, map_zero]

private theorem commute_adjoint (A L : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (h : ∀ v, L (A v) = A (L v)) (v : H) : L (A.adjoint v) = A.adjoint (L v) := by
  have he : A.adjoint = A := hA.star_eq
  rw [he]
  exact h v

omit [CompleteSpace H] in
private theorem sparse_inner (j : ι) (c : ℝ) (A : H →L[ℂ] H) (u : H) (d : ι → H) :
    (⟪u, ∑ q, sparseOperator j c A q (d q)⟫_ℂ).re = c * (⟪u, A (d j)⟫_ℂ).re := by
  rw [sparse_sum]
  simp only [inner_smul_right_eq_smul, Complex.smul_re, smul_eq_mul]
end Sparse

variable {N : ℕ} (i : Fin N)

def testWeight : SmoothPairTest → SmoothSpatialTest
  | .inl t => t
  | .inr (_, t) => t

def testCoordinate : SmoothPairTest → Fin N × Fin 3
  | .inl _ => (i, 0)
  | .inr (b, _) => (i, b)

def testOperator (t : SmoothPairTest) (q : Fin N × Fin 3) :
    WaveSpace (Fin N × Fin 3) →L[ℂ] WaveSpace (Fin N × Fin 3) :=
  if q = testCoordinate i t then
    (N : ℝ) • spatialMultiplier i (testWeight t).toBoundedSpatialTest else 0

theorem testOperator_sum (t : SmoothPairTest)
    (d : (Fin N × Fin 3) → WaveSpace (Fin N × Fin 3)) :
    (∑ q, testOperator i t q (d q)) =
      (N : ℝ) • spatialMultiplier i (testWeight t).toBoundedSpatialTest
        (d (testCoordinate i t)) :=
  sparse_sum (testCoordinate i t) (N : ℝ)
    (spatialMultiplier i (testWeight t).toBoundedSpatialTest) d

theorem testOperator_selfadjoint (t : SmoothPairTest) (q : Fin N × Fin 3) :
    IsSelfAdjoint (testOperator i t q) :=
  sparse_selfadjoint (testCoordinate i t) (N : ℝ)
    (spatialMultiplier i (testWeight t).toBoundedSpatialTest)
    (realL2Multiplier_selfadjoint _ _ _ _) q

theorem testOperator_commute
    (U : PhotonFock →ₗᵢ[ℂ] lp (fun _ : ℕ => PhotonFock) 2)
    (t : SmoothPairTest) (q : Fin N × Fin 3)
    (v : WaveSpace (Fin N × Fin 3)) (a : ℕ) :
    KrausL2.lift volume U (testOperator i t q v) a =
      testOperator i t q (KrausL2.lift volume U v a) :=
  sparse_commute (testCoordinate i t) (N : ℝ)
    (spatialMultiplier i (testWeight t).toBoundedSpatialTest) (KrausL2.coordinate volume U a)
    (fun w => PhysicalNormalCompression.multiplier_kraus _ _ _ _ U w a) q v

theorem testOperator_adjoint_commute
    (U : PhotonFock →ₗᵢ[ℂ] lp (fun _ : ℕ => PhotonFock) 2)
    (t : SmoothPairTest) (q : Fin N × Fin 3)
    (v : WaveSpace (Fin N × Fin 3)) (a : ℕ) :
    KrausL2.lift volume U ((testOperator i t q).adjoint v) a =
      (testOperator i t q).adjoint (KrausL2.lift volume U v a) :=
  commute_adjoint (testOperator i t q) (KrausL2.coordinate volume U a)
    (testOperator_selfadjoint i t q) (fun w => testOperator_commute i U t q w a) v

private theorem test_inner_sum (t : SmoothPairTest) (u : WaveSpace (Fin N × Fin 3))
    (d : (Fin N × Fin 3) → WaveSpace (Fin N × Fin 3)) :
    (⟪u, ∑ q, testOperator i t q (d q)⟫_ℂ).re =
      (N : ℝ) * (⟪u, spatialMultiplier i (testWeight t).toBoundedSpatialTest
        (d (testCoordinate i t))⟫_ℂ).re :=
  sparse_inner (testCoordinate i t) (N : ℝ)
    (spatialMultiplier i (testWeight t).toBoundedSpatialTest) u d

/-- Density is preserved by every actual pointwise photon channel, on
all positive normal traces and without an energy restriction. -/
theorem densityTrace_channel (B : StandardNormalTraceBackground)
    (U : PhotonFock →ₗᵢ[ℂ] lp (fun _ : ℕ => PhotonFock) 2)
    (t : SpatialTest) {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (hx : x ∈ (B.realization (WaveSpace (Fin N × Fin 3))).rank.positive) :
    densityTrace i B t ((B.normal (H := WaveSpace (Fin N × Fin 3))).extend
      (KrausL2.lift (volume : Measure (SymmetricLift.Configuration N)) U) x) = densityTrace i B t x := by
  have h := (B.realization (WaveSpace (Fin N × Fin 3))).functional.electronic
    (B.normal (H := WaveSpace (Fin N × Fin 3)))
    (KrausL2.lift (volume : Measure (SymmetricLift.Configuration N)) U) (spatialMultiplier i t)
    (fun v a => PhysicalNormalCompression.multiplier_kraus _ _ _ _ U v a) hx
  exact congrArg (fun z : ℂ => (N : ℝ) * z.re) h

variable (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → PhysicalPFReference.Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ x ∂volume, ‖κ q x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

def testDerivative (t : SmoothPairTest) (q : Fin N × Fin 3)
    (u : Reference (Fin N × Fin 3) V) : WaveSpace (Fin N × Fin 3) :=
  match t with
  | .inl _ => inclusion (Fin N × Fin 3) V u
  | .inr _ => covariant (Fin N × Fin 3) V C κ hκ M hbound e q u

theorem normalTest_rankOne (t : SmoothPairTest) (u : Reference (Fin N × Fin 3) V) :
    normalTest i V C κ hκ M hbound B S e t
      ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne
        (inclusion (Fin N × Fin 3) V u)) =
      (⟪inclusion (Fin N × Fin 3) V u,
        ∑ q, testOperator i t q (testDerivative V C κ hκ M hbound e t q u)⟫_ℂ).re := by
  cases t with
  | inl t =>
    exact (congrArg (fun r : ℝ => (N : ℝ) * r)
      (boundedTrace_rankOne (B.realization (WaveSpace (Fin N × Fin 3))).functional
        (spatialMultiplier i t.toBoundedSpatialTest) (inclusion (Fin N × Fin 3) V u))).trans
      (test_inner_sum i (.inl t) (inclusion (Fin N × Fin 3) V u)
        (testDerivative V C κ hκ M hbound e (.inl t) · u)).symm
  | inr t =>
    exact (congrArg (fun r : ℝ => (N : ℝ) * r)
      (observable_rankOne (Fin N × Fin 3) V C κ hκ M hbound B S e
        (inclusion (Fin N × Fin 3) V)
        ((spatialMultiplier i t.2.toBoundedSpatialTest).comp
          (covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, t.1))) u)).trans
      (test_inner_sum i (.inr t) (inclusion (Fin N × Fin 3) V u)
        (testDerivative V C κ hκ M hbound e (.inr t) · u)).symm

theorem testObservable_rankOne (t : SmoothPairTest)
    (u : Reference (Fin N × Fin 3) V) :
    (testObservable i V C κ hκ M hbound B S e t).value
      ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne
        (inclusion (Fin N × Fin 3) V u)) =
      (⟪inclusion (Fin N × Fin 3) V u,
        ∑ q, testOperator i t q (testDerivative V C κ hκ M hbound e t q u)⟫_ℂ).re := by
  exact (testObservable_value i V C κ hκ M hbound B S e t _
    ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne_positive _)
    (control_rankOne_finite (Fin N × Fin 3) V C κ hκ M hbound B S e u)).trans
      (normalTest_rankOne i V C κ hκ M hbound B S e t u)

theorem density_testObservable_rankOne (t : SmoothSpatialTest)
    (v : WaveSpace (Fin N × Fin 3)) :
    (testObservable i V C κ hκ M hbound B S e (.inl t)).value
      ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne v) =
      (⟪v, ∑ q, testOperator i (.inl t) q v⟫_ℂ).re := by
  exact (congrArg (fun r : ℝ => (N : ℝ) * r)
    (boundedTrace_rankOne (B.realization (WaveSpace (Fin N × Fin 3))).functional
      (spatialMultiplier i t.toBoundedSpatialTest) v)).trans
    (test_inner_sum i (.inl t) v (fun _ => v)).symm

/-- The density branch has no field correction or vacuum noise. Its
graph data are constructed directly from the given channel vectors. -/
def densitySource (t : SmoothSpatialTest)
    (U : KrausIsometry (WaveSpace (Fin N × Fin 3)))
    (v : WaveSpace (Fin N × Fin 3))
    (hv : (currentControl (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation
      ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne v) < ⊤)
    (hout : (currentControl (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation
      (pure (B.realization (WaveSpace (Fin N × Fin 3))).rank U v) < ⊤) :
    TestedCurrentSource
      (A := (B.realization (WaveSpace (Fin N × Fin 3))).rank)
      (control := currentControl (Fin N × Fin 3) V C κ hκ M hbound B S e)
      (current := testObservable i V C κ hκ M hbound B S e (.inl t))
      U v (testOperator i (.inl t)) (fun _ => 0) e 0 0 where
  derivative _ := v
  field _ := 0
  noise _ := 0
  localized _ := U v
  mass_le := norm_le_sqrt_control (Fin N × Fin 3) V C κ hκ M hbound B S e v hv
  tested_field_le _ := by simp
  graph _ := by simp
  orthogonality _ _ := by simp
  output_finite := hout
  original_form := density_testObservable_rankOne i V C κ hκ M hbound B S e t v
  coordinate_form a := density_testObservable_rankOne i V C κ hκ M hbound B S e t (U v a)

end GptLean.PhysicalPFLocalization
