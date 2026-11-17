import GptLean.PhysicalPFPairSeries
import GptLean.PhysicalPFPurePair
import GptLean.PhysicalPFSupportedSource

/-!
Pure spectral ensembles for the actual Pauli--Fierz constrained-search
models and every article potential. The source pair series converges in
the full density-current Banach space, so the potential term follows by
continuity of its actual dual pairing. No relative potential approximation
or spectral-ensemble conclusion is an input.
-/

noncomputable section

namespace GptLean.PhysicalPFSpectral

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace PhysicalClosedForms
  PhysicalPFSource PhysicalPFPairSeries PhysicalNormalStates PhysicalNormalSpectral
  PhotonLocalizationChannel
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

attribute [local irreducible] normalEnergy

private theorem sourcePure_pair_of_normalize
    {H T Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
    [AddCommGroup Y] [Module ℝ Y]
    {R : Gaussian.RankOneData H T} {normal : NormalTraceData R}
    {F : NormalFunctionalData R}
    (E : RemovalState.PositiveForm (positiveTrace normal F)) (P : H →L[ℂ] H)
    (D : Pure E P → Y) (p₀ : Pure E P) (v : H) (hP : P v = v)
    (hE : E.expectation (R.rankOne v) < ⊤) (y : Y)
    (hzero : v = 0 → y = 0)
    (hnormalize : ∀ hv : v ≠ 0,
      D (normalize E P v hP hE hv) = (‖v‖⁻¹) ^ 2 • y) :
    ‖v‖ ^ 2 • D (sourcePure E P p₀ v hP hE) = y := by
  by_cases hv : v = 0
  · have hz : ‖v‖ ^ 2 = 0 := by
      rw [hv, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    rw [hz, zero_smul, hzero hv]
  · simp only [sourcePure, dite_eq_right hv]
    rw [hnormalize hv, smul_smul]
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hm : ‖v‖ ^ 2 * (‖v‖⁻¹) ^ 2 = 1 := by field_simp
    rw [hm, one_smul]

/-- Normalize a unit-mass positive source with one pure fallback for its
zero vectors, preserving the trace and finite form sums. -/
theorem normalized_source
    {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
    {R : Gaussian.RankOneData H T} {normal : NormalTraceData R}
    {F : NormalFunctionalData R}
    (E : RemovalState.PositiveForm (positiveTrace normal F)) (P : H →L[ℂ] H)
    {v : ℕ → H} {x : T} (hs : HasSum (fun n => R.rankOne (v n)) x)
    (hE : E.expectation x < ⊤) (hP : ∀ n, P (v n) = v n)
    (hmass : HasSum (fun n => ‖v n‖ ^ 2) 1) :
    ∃ p₀ : Pure E P,
      let p := fun n => sourcePure E P p₀ (v n) (hP n) (source_form_finite E hs hE n)
      HasSum (fun n => ‖v n‖ ^ 2 • R.rankOne (p n).val) x ∧
      HasSum (fun n => ‖v n‖ ^ 2 * (E.expectation (R.rankOne (p n).val)).toReal)
        (E.expectation x).toReal := by
  have hnz : ∃ n, v n ≠ 0 := by
    by_contra h
    push Not at h
    have hz : HasSum (fun _ : ℕ => (0 : ℝ)) 1 := by
      simpa only [h, norm_zero, zero_pow (by decide : 2 ≠ 0)] using hmass
    have hbad := hz.unique hasSum_zero
    norm_num at hbad
  obtain ⟨n₀, hn₀⟩ := hnz
  let p₀ := normalize E P (v n₀) (hP n₀) (source_form_finite E hs hE n₀) hn₀
  refine ⟨p₀, ?_, ?_⟩
  · exact hs.congr_fun (fun n => sourcePure_rankOne E P p₀ (v n) (hP n)
      (source_form_finite E hs hE n))
  · exact (source_form_hasSum E hs hE).congr_fun (fun n =>
      sourcePure_energy E P p₀ (v n) (hP n) (source_form_finite E hs hE n))

private theorem ensemble_of_sums
    {P M D A : Type*} (pure : DFT.StateModel P D) (mixed : DFT.StateModel M D)
    (pair : A → D → ℝ) (m : M) (a : A) (p : ℕ → P) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (hmass : HasSum w 1)
    (he : HasSum (fun n => w n * pure.energy (p n)) (mixed.energy m))
    (hp : HasSum (fun n => w n * pair a (pure.density (p n)))
      (pair a (mixed.density m))) :
    Nonempty (Theorem48.SpectralEnsemble pure mixed pair m a) := by
  have hs := he.add hp
  exact ⟨{ pure := p
           weight := w
           weight_nonneg := hw
           weight_summable := hmass.summable
           weight_sum := hmass.tsum_eq
           energy_summable := by simpa only [mul_add] using hs.summable
           energy_sum := by simpa only [mul_add] using hs.tsum_eq }⟩

local instance referenceComplexModule {N : ℕ}
    (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ) :
    Module ℂ (Reference (Fin N × Fin 3) V) :=
  (referenceNormedSpace (Fin N × Fin 3) V).toModule

local instance referenceComplexSMul {N : ℕ}
    (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ) :
    SMul ℂ (Reference (Fin N × Fin 3) V) :=
  (referenceComplexModule V).toSMul

local instance referenceRealSpace {N : ℕ}
    (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ) :
    NormedSpace ℝ (Reference (Fin N × Fin 3) V) :=
  NormedSpace.restrictScalars ℝ ℂ (Reference (Fin N × Fin 3) V)

local instance referenceRealModule {N : ℕ}
    (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ) :
    Module ℝ (Reference (Fin N × Fin 3) V) :=
  (referenceRealSpace V).toModule

local instance referenceRealSMul {N : ℕ}
    (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ) :
    SMul ℝ (Reference (Fin N × Fin 3) V) :=
  (referenceRealModule V).toSMul

local instance referenceRealTower {N : ℕ}
    (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ) :
    IsScalarTower ℝ ℂ (Reference (Fin N × Fin 3) V) :=
  IsScalarTower.restrictScalars ℝ ℂ (Reference (Fin N × Fin 3) V)

variable {N : ℕ} (i : Fin N) (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → PhysicalPFReference.Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ x ∂volume, ‖κ q x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

theorem vectorPair_real_smul (r : ℝ) (u : Reference (Fin N × Fin 3) V) :
    vectorPair i V C κ hκ M hbound e (r • u) =
      r ^ 2 • vectorPair i V C κ hκ M hbound e u := by
  calc
    _ = pairForm i V C κ hκ M hbound e (r • u) (r • u) :=
      (pairForm_diagonal i V C κ hκ M hbound e (r • u)).symm
    _ = r ^ 2 • pairForm i V C κ hκ M hbound e u u := by
      simp only [map_smul, smul_apply, smul_smul, pow_two]
    _ = _ := congrArg (r ^ 2 • ·) (pairForm_diagonal i V C κ hκ M hbound e u)

theorem vectorPair_zero : vectorPair i V C κ hκ M hbound e 0 = 0 := by
  exact (pairForm_diagonal i V C κ hκ M hbound e 0).symm.trans
    (by simp only [map_zero])

theorem pure_pair_eq (p : PhysicalPFStates.PureState V C κ hκ M hbound B S e)
    (u : Reference (Fin N × Fin 3) V) (hu : inclusion (Fin N × Fin 3) V u = p.val) :
    (PhysicalPFStates.pureModel i V C κ hκ M hbound B S e).density p =
      vectorPair i V C κ hκ M hbound e u := by
  have he : (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation
      ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne
        (inclusion (Fin N × Fin 3) V u)) < ⊤ := by
    rw [hu]
    exact p.property.2.2
  have h := PhysicalPFStates.pair_rankOne i V C κ hκ M hbound B S e u
    ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne_positive _) he
  change PhysicalPFStates.pair i V C κ hκ M hbound B S e
    ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne p.val) _ _ = _
  simpa only [hu, PhysicalPFStates.referencePair, vectorPair] using h

set_option backward.isDefEq.respectTransparency.types false in
theorem sourcePure_pair_weight
    (p₀ : PhysicalPFStates.PureState V C κ hκ M hbound B S e)
    (u : Reference (Fin N × Fin 3) V)
    (hP : PhysicalElectronicFermions.projection N PhotonFock
      (inclusion (Fin N × Fin 3) V u) = inclusion (Fin N × Fin 3) V u)
    (hE : (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation
      ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne
        (inclusion (Fin N × Fin 3) V u)) < ⊤) :
    ‖inclusion (Fin N × Fin 3) V u‖ ^ 2 •
      (PhysicalPFStates.pureModel i V C κ hκ M hbound B S e).density
        (sourcePure (normal := B.normal)
          (F := (B.realization (WaveSpace (Fin N × Fin 3))).functional)
          (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e)
          (PhysicalElectronicFermions.projection N PhotonFock) p₀
          (inclusion (Fin N × Fin 3) V u) hP hE) =
      vectorPair i V C κ hκ M hbound e u := by
  apply sourcePure_pair_of_normalize
    (H := WaveSpace (Fin N × Fin 3)) (T := B.Trace (WaveSpace (Fin N × Fin 3)))
    (Y := PhysicalPairSpace.Pair)
    (R := (B.realization (WaveSpace (Fin N × Fin 3))).rank)
    (normal := B.normal) (F := (B.realization (WaveSpace (Fin N × Fin 3))).functional)
    (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e)
    (PhysicalElectronicFermions.projection N PhotonFock)
    (PhysicalPFStates.pureModel i V C κ hκ M hbound B S e).density p₀
    (inclusion (Fin N × Fin 3) V u) hP hE
    (vectorPair i V C κ hκ M hbound e u)
  · intro hv
    have hu : u = 0 := inclusion_injective (Fin N × Fin 3) V
      (hv.trans (map_zero (inclusion (Fin N × Fin 3) V)).symm)
    exact (congrArg (vectorPair i V C κ hκ M hbound e) hu).trans
      (vectorPair_zero i V C κ hκ M hbound e)
  · intro hv
    have hnorm := pure_pair_eq i V C κ hκ M hbound B S e
      (normalize (normal := B.normal)
        (F := (B.realization (WaveSpace (Fin N × Fin 3))).functional)
        (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e)
        (PhysicalElectronicFermions.projection N PhotonFock)
        (inclusion (Fin N × Fin 3) V u) hP hE hv)
      ((‖inclusion (Fin N × Fin 3) V u‖⁻¹ : ℝ) • u)
      (by
        change inclusion (Fin N × Fin 3) V
          (((‖inclusion (Fin N × Fin 3) V u‖⁻¹ : ℝ) : ℂ) • u) =
            ((‖inclusion (Fin N × Fin 3) V u‖⁻¹ : ℝ) : ℂ) • inclusion (Fin N × Fin 3) V u
        exact map_smul _ _ _)
    exact hnorm.trans (vectorPair_real_smul i V C κ hκ M hbound e
      (‖inclusion (Fin N × Fin 3) V u‖⁻¹) u)

set_option backward.isDefEq.respectTransparency.types false in
theorem mixed_pair_hasSum
    (m : PhysicalPFStates.MixedState V C κ hκ M hbound B S e)
    (s : Source (Fin N × Fin 3) V B m.val.val) :
    HasSum (fun n => vectorPair i V C κ hκ M hbound e (s.vector n))
      ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).density m) := by
  have hsource := vectorPair_hasSum i V C κ hκ M hbound S e s m.val.property.2.2
  have hmatch : (PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).density m =
      s.pair C M S e i V κ hκ hbound m.val.property.2.2 :=
    PhysicalPFStates.pair_eq_source i V C κ hκ M hbound B S e
      m.val.val m.val.property.1 m.val.property.2.2 s
  exact Eq.mp (congrArg
    (fun q : PhysicalPairSpace.Pair =>
      HasSum (fun n => vectorPair i V C κ hκ M hbound e (s.vector n)) q)
    hmatch.symm) hsource

set_option backward.isDefEq.respectTransparency.types false in
theorem spectralEnsemble
    (m : PhysicalPFStates.MixedState V C κ hκ M hbound B S e)
    (a : PhysicalPairDuality.Potential) :
    Nonempty (Theorem48.SpectralEnsemble
      (P := PhysicalPFStates.PureState V C κ hκ M hbound B S e)
      (M := PhysicalPFStates.MixedState V C κ hκ M hbound B S e)
      (D := PhysicalPairSpace.Pair) (V := PhysicalPairDuality.Potential)
      (PhysicalPFStates.pureModel i V C κ hκ M hbound B S e)
      (PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e)
      (fun a p => PhysicalPairDuality.pairPotential a p) m a) := by
  let E : RemovalState.PositiveForm
      (positiveTrace (B.normal (H := WaveSpace (Fin N × Fin 3)))
        (B.realization (WaveSpace (Fin N × Fin 3))).functional) :=
    normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e
  let P := PhysicalElectronicFermions.projection N PhotonFock
  obtain ⟨s⟩ := supported_source_exists N V B C κ hκ M hbound S e
    m.val.property.1 m.val.property.2.2 m.property
  let v (n : ℕ) := inclusion (Fin N × Fin 3) V (s.vector n)
  have hP (n : ℕ) : P (v n) = v n :=
    (PhysicalElectronicFermions.projection_eq_self_iff N PhotonFock (v n)).mpr
      ((PhysicalElectronicFermions.mem_fermionicSubspace_iff N PhotonFock (v n)).mp
        (s.fermionic n))
  have hfinite (n : ℕ) := source_form_finite E s.hasSum m.val.property.2.2 n
  have hmass : HasSum (fun n => ‖v n‖ ^ 2) 1 := by
    have htrace : (B.realization (WaveSpace (Fin N × Fin 3))).rank.trace m.val.val = 1 :=
      m.val.property.2.1
    exact htrace ▸ s.toSource.mass_hasSum
  obtain ⟨p₀, _, henergy⟩ := normalized_source
    (H := WaveSpace (Fin N × Fin 3)) (T := B.Trace (WaveSpace (Fin N × Fin 3)))
    (R := (B.realization (WaveSpace (Fin N × Fin 3))).rank)
    (normal := B.normal) (F := (B.realization (WaveSpace (Fin N × Fin 3))).functional)
    E P s.hasSum m.val.property.2.2 hP hmass
  let p (n : ℕ) := sourcePure E P p₀ (v n) (hP n) (hfinite n)
  have hpair : HasSum (fun n => ‖v n‖ ^ 2 •
      (PhysicalPFStates.pureModel i V C κ hκ M hbound B S e).density (p n))
      ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).density m) := by
    exact (mixed_pair_hasSum i V C κ hκ M hbound B S e m s.toSource).congr_fun
      (fun n => sourcePure_pair_weight i V C κ hκ M hbound B S e p₀
        (s.vector n) (hP n) (hfinite n))
  exact ensemble_of_sums
    (PhysicalPFStates.pureModel i V C κ hκ M hbound B S e)
    (PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e)
    (fun a p => PhysicalPairDuality.pairPotential a p) m a p
    (fun n => ‖v n‖ ^ 2) (fun n => sq_nonneg _) hmass henergy
    (by simpa only [map_smul, smul_eq_mul] using
      (PhysicalPairDuality.pairPotential a).hasSum hpair)

end GptLean.PhysicalPFSpectral
