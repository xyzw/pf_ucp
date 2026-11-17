import GptLean.PhysicalPFCurrentEvaluation

/-!
Uniform bounds for every bounded current approximant. The positive
appended graph forms control their own truncations. Their reference
source sums are bounded by the actual mass and PF energy. Isometric
trace pullback gives the identical estimate for the hard current.
-/

noncomputable section

namespace GptLean.PhysicalPFCurrentBounds

open MeasureTheory Filter Topology PhysicalFock PhysicalPFReference
  PhysicalNormalTrace PhysicalPFSource PhysicalPFVacuumEnergy PhysicalPFCurrentEvaluation
  PhysicalGraphForms RemovalState
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section Generic

private theorem tsum_norm_sq_map_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) (u : ℕ → E) (hu : Summable (fun n => ‖u n‖ ^ 2)) :
    (∑' n, ‖L (u n)‖ ^ 2) ≤ ‖L‖ ^ 2 * ∑' n, ‖u n‖ ^ 2 := by
  have hs : Summable (fun n => ‖L (u n)‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ (hu.mul_left (‖L‖ ^ 2))
    intro n
    exact (pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm (u n)) 2).trans_eq (mul_pow _ _ _)
  calc
    _ ≤ ∑' n, ‖L‖ ^ 2 * ‖u n‖ ^ 2 :=
      Summable.tsum_le_tsum (fun n =>
        (pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm (u n)) 2).trans_eq (mul_pow _ _ _))
        hs (hu.mul_left (‖L‖ ^ 2))
    _ = _ := tsum_mul_left

variable {E H K F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  (G : CoerciveGraph E H K)

def graphCurrentCoefficient (L R : E →L[ℂ] F) : ℝ :=
  (‖G.appendOutput (L + R)‖ ^ 2 + ‖G.appendOutput (L - R)‖ ^ 2) / 4

theorem graphCurrentCoefficient_nonneg (L R : E →L[ℂ] F) :
    0 ≤ graphCurrentCoefficient G L R := by
  unfold graphCurrentCoefficient
  positivity

variable [CompleteSpace E] [CompleteSpace H] [CompleteSpace K] [CompleteSpace F]
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)

theorem crossObservable_source_bound (L R : E →L[ℂ] F)
    (energy : PositiveForm (B.traceData (H := H)))
    (hsource : ∀ x ∈ (B.traceData (H := H)).positive, energy.expectation x < ⊤ →
      ∃ u : ℕ → E, HasSum (fun n => (B.realization H).rank.rankOne (G.value (u n))) x ∧
        Summable (fun n => ‖u n‖ ^ 2))
    {x : B.Trace H} (hx : x ∈ (B.traceData (H := H)).positive)
    (u : ℕ → E)
    (hu : HasSum (fun n => (B.realization H).rank.rankOne (G.value (u n))) x)
    (hs : Summable (fun n => ‖u n‖ ^ 2)) (n : ℕ) :
    ‖(G.crossObservable_of_source B S L R energy hsource).approximation n x‖ ≤
      graphCurrentCoefficient G L R * ∑' j, ‖u j‖ ^ 2 := by
  let Ep := (G.append (L + R)).normalForm B S
  let Em := (G.append (L - R)).normalForm B S
  have hpf : Ep.expectation x < ⊤ := (G.append (L + R)).normalForm_source_finite B S hu hs
  have hmf : Em.expectation x < ⊤ := (G.append (L - R)).normalForm_source_finite B S hu hs
  have hp := truncation_le_toReal Ep hx hpf n
  have hm := truncation_le_toReal Em hx hmf n
  have hp0 := Ep.nonneg n x hx
  have hm0 := Em.nonneg n x hx
  have hps := (G.append (L + R)).normalForm_source_hasSum B S hu
    (CoerciveGraph.summable_norm_sq_map (G.appendOutput (L + R)) u hs)
  have hms := (G.append (L - R)).normalForm_source_hasSum B S hu
    (CoerciveGraph.summable_norm_sq_map (G.appendOutput (L - R)) u hs)
  have hpb : (Ep.expectation x).toReal ≤ ‖G.appendOutput (L + R)‖ ^ 2 * ∑' j, ‖u j‖ ^ 2 := by
    rw [← hps.tsum_eq]
    exact tsum_norm_sq_map_le _ u hs
  have hmb : (Em.expectation x).toReal ≤ ‖G.appendOutput (L - R)‖ ^ 2 * ∑' j, ‖u j‖ ^ 2 := by
    rw [← hms.tsum_eq]
    exact tsum_norm_sq_map_le _ u hs
  change ‖(1 / 4 : ℝ) * Ep.truncation n x - (1 / 4 : ℝ) * Em.truncation n x‖ ≤ _
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  unfold graphCurrentCoefficient
  constructor <;> nlinarith

end Generic

attribute [local irreducible] PhysicalPFReference.normalEnergy

section Physical

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (k : I → Position I → WeightedPhotonKernel)
  (hk : ∀ i, AEStronglyMeasurable (k i) volume)
  (M : ℝ) (hM : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (e : ℝ)

theorem source_norm_sum_le {x : B.Trace (WaveSpace I)} (s : Source I V B x)
    (he : (normalEnergy I V C k hk M hM B S e).expectation x < ⊤) :
    (∑' n, ‖s.vector n‖ ^ 2) ≤
      (formComparisonConstant I C k hk M hM e * (1 + Real.sqrt 2)) ^ 2 *
        ((B.realization (WaveSpace I)).rank.trace x +
          ((normalEnergy I V C k hk M hM B S e).expectation x).toReal) := by
  have hm := s.mass_hasSum
  have hE := s.energy_hasSum C k hk M hM S e he
  have hs := s.reference_summable C k hk M hM S e he
  have h := Summable.tsum_le_tsum
    (fun n => reference_norm_sq_le I V C k hk M hM e (s.vector n)) hs
    ((hm.summable.add hE.summable).mul_left
      ((formComparisonConstant I C k hk M hM e * (1 + Real.sqrt 2)) ^ 2))
  simpa only [tsum_mul_left, hm.summable.tsum_add hE.summable, hm.tsum_eq, hE.tsum_eq] using h

def observableCoefficient {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (L R : Reference I V →L[ℂ] F) : ℝ :=
  graphCurrentCoefficient (coerciveGraph I V C k hk M hM e) L R *
    (formComparisonConstant I C k hk M hM e * (1 + Real.sqrt 2)) ^ 2

set_option backward.isDefEq.respectTransparency.types true in
theorem observableCoefficient_nonneg {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (L R : Reference I V →L[ℂ] F) :
    0 ≤ observableCoefficient I V C k hk M hM e L R := by
  unfold observableCoefficient
  exact mul_nonneg (graphCurrentCoefficient_nonneg
    (E := Reference I V) (H := WaveSpace I) (K := EnergyOutput I) (F := F)
    (coerciveGraph I V C k hk M hM e) L R) (sq_nonneg _)

set_option backward.isDefEq.respectTransparency.types true in
theorem observable_approximation_bound {F : Type} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (L R : Reference I V →L[ℂ] F)
    (n : ℕ) (x : B.Trace (WaveSpace I))
    (hx : x ∈ (B.traceData (H := WaveSpace I)).positive)
    (he : (normalEnergy I V C k hk M hM B S e).expectation x < ⊤) :
    ‖(observable I V C k hk M hM B S e L R).approximation n x‖ ≤
      observableCoefficient I V C k hk M hM e L R *
        ((B.traceData (H := WaveSpace I)).trace x +
          ((normalEnergy I V C k hk M hM B S e).expectation x).toReal) := by
  have hx' : x ∈ (B.realization (WaveSpace I)).rank.positive := hx
  have hsource : Nonempty (Source I V B x) :=
    source_exists I V C k hk M hM B S e (x := x) hx' he
  obtain ⟨s⟩ := hsource
  have h := crossObservable_source_bound
    (E := Reference I V) (H := WaveSpace I) (K := EnergyOutput I) (F := F)
    (coerciveGraph I V C k hk M hM e) B S L R
    (normalEnergy I V C k hk M hM B S e)
    (reference_source_summable I V C k hk M hM B S e) hx s.vector s.hasSum
    (s.reference_summable C k hk M hM S e he) n
  exact h.trans ((mul_le_mul_of_nonneg_left (source_norm_sum_le I V C k hk M hM B S e s he)
    (graphCurrentCoefficient_nonneg
      (E := Reference I V) (H := WaveSpace I) (K := EnergyOutput I) (F := F)
      (coerciveGraph I V C k hk M hM e) L R)).trans_eq (mul_assoc _ _ _).symm)

def testedCurrentCoefficient (a : Position I → ℝ) (ha : AEStronglyMeasurable a volume)
    (A : ℝ) (hA : ∀ᵐ x ∂volume, |a x| ≤ A) (i : I) : ℝ :=
  observableCoefficient I V C k hk M hM e (inclusion I V)
    ((PhotonLocalization.realL2Multiplier a ha A hA).comp (covariant I V C k hk M hM e i))

theorem testedCurrentCoefficient_nonneg (a : Position I → ℝ)
    (ha : AEStronglyMeasurable a volume) (A : ℝ)
    (hA : ∀ᵐ x ∂volume, |a x| ≤ A) (i : I) :
    0 ≤ testedCurrentCoefficient I V C k hk M hM e a ha A hA i :=
  observableCoefficient_nonneg I V C k hk M hM e _ _

theorem testedCurrent_approximation_bound (a : Position I → ℝ)
    (ha : AEStronglyMeasurable a volume) (A : ℝ)
    (hA : ∀ᵐ x ∂volume, |a x| ≤ A) (i : I)
    (n : ℕ) (x : B.Trace (WaveSpace I))
    (hx : x ∈ (B.traceData (H := WaveSpace I)).positive)
    (he : (normalEnergy I V C k hk M hM B S e).expectation x < ⊤) :
    ‖(testedCurrent I V C k hk M hM B S e a ha A hA i).approximation n x‖ ≤
      testedCurrentCoefficient I V C k hk M hM e a ha A hA i *
        ((B.traceData (H := WaveSpace I)).trace x +
          ((normalEnergy I V C k hk M hM B S e).expectation x).toReal) :=
  observable_approximation_bound I V C k hk M hM B S e _ _ n x hx he

end Physical

section Pullback

variable {H K : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem pullback_approximation_bound (B : StandardNormalTraceBackground)
    (J : H →ₗᵢ[ℂ] K) (E : PositiveForm (B.traceData (H := K)))
    (O : FormObservable E) (c : ℝ)
    (hO : ∀ n x, x ∈ (B.traceData (H := K)).positive → E.expectation x < ⊤ →
      ‖O.approximation n x‖ ≤ c * ((B.traceData (H := K)).trace x + (E.expectation x).toReal))
    (n : ℕ) (x : B.Trace H) (hx : x ∈ (B.traceData (H := H)).positive)
    (he : (pullbackForm B J.toContinuousLinearMap E).expectation x < ⊤) :
    ‖(pullbackObservable B J.toContinuousLinearMap E O).approximation n x‖ ≤
      c * ((B.traceData (H := H)).trace x +
        ((pullbackForm B J.toContinuousLinearMap E).expectation x).toReal) := by
  have h := hO n (B.push J.toContinuousLinearMap x) (B.push_positive J.toContinuousLinearMap hx) he
  have hm := B.push_trace_isometry J hx
  change (B.traceData (H := K)).trace (B.push J.toContinuousLinearMap x) =
    (B.traceData (H := H)).trace x at hm
  rw [hm] at h
  exact h

end Pullback

section Hard

attribute [local instance] PhysicalPFCurrentEvaluation.currentPhotonDirectInner
  PhysicalPFCurrentEvaluation.currentHardDirectInner
attribute [local irreducible] PositiveForm.expectation pullbackObservable pullbackForm
  PhysicalPFVacuumInsertion.insertion testedCurrent


variable {Test : Type} (N : ℕ) (c : ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (h : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hh : ∀ i, AEStronglyMeasurable (h i) volume)
  (M : ℝ) (hM : ∀ i, ∀ᵐ x ∂volume, ‖h i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (BF : StandardSymmetricFockExponential) (κ e : ℝ)
  (weight : Test → Position (Fin N × Fin 3) → ℝ)
  (hw : ∀ t, AEStronglyMeasurable (weight t) volume)
  (A : Test → ℝ) (hA : ∀ t, ∀ᵐ x ∂volume, |weight t x| ≤ A t)
  (direction : Test → Fin N × Fin 3)

set_option backward.isDefEq.respectTransparency.types true in
set_option diagnostics true in
theorem hardTestedCurrent_approximation_bound (t : Test) (n : ℕ)
    (x : B.Trace (Lp (generatedFockSubspace (hardOnePhoton κ)) 2
      (volume : Measure (Position (Fin N × Fin 3)))))
    (hx : x ∈ (B.traceData (H := Lp (generatedFockSubspace (hardOnePhoton κ)) 2
      (volume : Measure (Position (Fin N × Fin 3))))).positive)
    (he : (hardEnergy (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
      C h hh M hM B S BF κ e).expectation x < ⊤) :
    ‖(hardTestedCurrent N c C h hh M hM B S BF κ e weight hw A hA direction t).approximation n x‖ ≤
      testedCurrentCoefficient (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
        C h hh M hM e (weight t) (hw t) (A t) (hA t) (direction t) *
      ((B.traceData (H := Lp (generatedFockSubspace (hardOnePhoton κ)) 2
          (volume : Measure (Position (Fin N × Fin 3))))).trace x +
        ((hardEnergy (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
          C h hh M hM B S BF κ e).expectation x).toReal) := by
  unfold hardTestedCurrent
  unfold hardEnergy at he ⊢
  exact pullback_approximation_bound
    (H := Lp (generatedFockSubspace (hardOnePhoton κ)) 2
      (volume : Measure (Position (Fin N × Fin 3))))
    (K := WaveSpace (Fin N × Fin 3)) B (PhysicalPFVacuumInsertion.insertion volume BF κ)
    (normalEnergy (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
      C h hh M hM B S e)
    (testedCurrent (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
      C h hh M hM B S e (weight t) (hw t) (A t) (hA t) (direction t))
    (testedCurrentCoefficient (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
      C h hh M hM e (weight t) (hw t) (A t) (hA t) (direction t))
    (testedCurrent_approximation_bound (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
      C h hh M hM B S e (weight t) (hw t) (A t) (hA t) (direction t)) n x hx he

end Hard

end GptLean.PhysicalPFCurrentBounds
