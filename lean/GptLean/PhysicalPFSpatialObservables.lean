import GptLean.PhysicalPFPair
import GptLean.PhysicalPFNormalObservables
import GptLean.PhysicalPairSpatialTests

/-!
Bounded density tests and form current tests on the actual normal trace
space. The spatial pair formulas are derived from every reference source.
-/

noncomputable section

namespace GptLean.PhysicalPFSource

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalSourceCoordinates PhysicalPairSpace
  PhotonLocalization PhotonLocalizationChannel RemovalState
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

section General

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  {R : Gaussian.RankOneData H T}

def boundedTrace (F : NormalFunctionalData R) (A : H →L[ℂ] H) : T →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (((ContinuousLinearMap.apply ℂ ℂ A).restrictScalars ℝ).comp F.repr)

theorem boundedTrace_rankOne (F : NormalFunctionalData R) (A : H →L[ℂ] H) (u : H) :
    boundedTrace F A (R.rankOne u) = (⟪u, A u⟫_ℂ).re := by
  change (F.repr (R.rankOne u) A).re = _
  rw [F.rankOne]

variable [CompleteSpace T] {Tr : PositiveTraceData T} {E : PositiveForm Tr}

def scaleObservable (r : ℝ) (J : FormObservable E) : FormObservable E where
  approximation n := r • J.approximation n
  value x := r * J.value x
  converges x hx he := by
    simpa only [smul_apply, smul_eq_mul] using
      (J.converges x hx he).const_mul r

def boundedObservable (A : T →L[ℝ] ℝ) : FormObservable E where
  approximation _ := A
  value := A
  converges _ _ _ := tendsto_const_nhds

end General

theorem boundedTrace_multiplier_rankOne {X H T : Type*} [MeasurableSpace X]
    {μ : Measure X} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup T] [NormedSpace ℝ T]
    {R : Gaussian.RankOneData (Lp H 2 μ) T}
    (F : NormalFunctionalData R) (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (c : ℝ) (hc : ∀ᵐ x ∂μ, |a x| ≤ c) (u : Lp H 2 μ) :
    boundedTrace F (realL2Multiplier a ha c hc) (R.rankOne u) =
      ∫ x, a x * ‖u x‖ ^ 2 ∂μ := by
  rw [boundedTrace_rankOne, multiplier_tested_inner]
  apply integral_congr_ae
  exact ae_of_all _ fun x => congrArg (fun r : ℝ => a x * r)
    (norm_sq_eq_re_inner (𝕜 := ℂ) (u x)).symm

variable {N : ℕ} (i : Fin N) (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → PhysicalPFReference.Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ x ∂volume, ‖κ q x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

def spatialMultiplier (t : SpatialTest) : WaveSpace (Fin N × Fin 3) →L[ℂ] WaveSpace (Fin N × Fin 3) :=
  realL2Multiplier (fun z => t.weight ((split i) z).1)
    (t.measurable.comp_fst.comp_measurePreserving (split_measurePreserving i)) 1
    (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using t.bounded ((split i) z).1)

def densityTrace (t : SpatialTest) : B.Trace (WaveSpace (Fin N × Fin 3)) →L[ℝ] ℝ :=
  (N : ℝ) • boundedTrace (B.realization (WaveSpace (Fin N × Fin 3))).functional
    (spatialMultiplier i t)

def densityObservable (t : SpatialTest) :
    FormObservable (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e) :=
  boundedObservable (densityTrace i B t)

def currentObservable (b : Fin 3) (t : SpatialTest) :
    FormObservable (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e) :=
  scaleObservable (N : ℝ)
    (observable (Fin N × Fin 3) V C κ hκ M hbound B S e
      (inclusion (Fin N × Fin 3) V)
      ((spatialMultiplier i t).comp (covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, b))))

variable {B}

theorem Source.densityTrace_eq {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : Source (Fin N × Fin 3) V B x)
    (he : (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation x < ⊤)
    (t : SpatialTest) :
    densityTrace i B t x = spatialDensityTest t (s.pair C M S e i V κ hκ hbound he) := by
  have h := (boundedTrace (B.realization (WaveSpace (Fin N × Fin 3))).functional
    (spatialMultiplier i t)).hasSum s.hasSum
  have hs : HasSum (fun n => ∫ z, t.weight ((split i) z).1 *
      ‖inclusion (Fin N × Fin 3) V (s.vector n) z‖ ^ 2)
      (boundedTrace (B.realization (WaveSpace (Fin N × Fin 3))).functional
        (spatialMultiplier i t) x) := h.congr_fun (fun n =>
    (boundedTrace_multiplier_rankOne (B.realization (WaveSpace (Fin N × Fin 3))).functional
      (fun z => t.weight ((split i) z).1)
      (t.measurable.comp_fst.comp_measurePreserving (split_measurePreserving i)) 1
      (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using t.bounded ((split i) z).1)
      (inclusion (Fin N × Fin 3) V (s.vector n))).symm)
  exact (congrArg (fun r : ℝ => (N : ℝ) * r) hs.tsum_eq.symm).trans
    ((s.pair_tested_density C M S e i V κ hκ hbound he t.weight t.measurable
      (ae_of_all _ t.bounded)).symm.trans (spatialDensityTest_eq t _).symm)

theorem Source.currentObservable_eq {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : Source (Fin N × Fin 3) V B x)
    (he : (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation x < ⊤)
    (b : Fin 3) (t : SpatialTest) :
    (currentObservable i V C κ hκ M hbound B S e b t).value x =
      spatialCurrentTest b t (s.pair C M S e i V κ hκ hbound he) := by
  have hs := s.tested_inner_hasSum C κ hκ M hbound S e he
    (inclusion (Fin N × Fin 3) V) (covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, b))
    (fun z => t.weight ((split i) z).1)
    (t.measurable.comp_fst.comp_measurePreserving (split_measurePreserving i)) 1
    (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using t.bounded ((split i) z).1)
  exact (congrArg (fun r : ℝ => (N : ℝ) * r) hs.tsum_eq.symm).trans
    ((s.pair_tested_current C M S e i V κ hκ hbound he b t.weight t.measurable
      (ae_of_all _ t.bounded)).symm.trans
        (spatialCurrentTest_eq b t _).symm)

end GptLean.PhysicalPFSource
