import GptLean.PhysicalRemovalObservables
import GptLean.PhysicalPFStates
import GptLean.RemovalPhysicalPair

/-!
The complete bounded electronic test family identifies the existing
physical density-current pair. One fixed electron coordinate is used
throughout, so the identities hold on every finite-form state without
requiring a symmetry premise for the removal output.
-/

noncomputable section

namespace GptLean.PhysicalRemovalPair

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace PhysicalPFSource
  PhysicalSourceCoordinates PhysicalPairSpace PhysicalPFCurrentEvaluation
  RemovalState RemovalConstraints
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable (N : ℕ) (i : Fin N)

def densityWeight (t : SpatialTest) (x : PhysicalPFReference.Position (Fin N × Fin 3)) : ℝ :=
  (N : ℝ) * t.weight ((split i) x).1

def currentWeight (t : Fin 3 × SpatialTest)
    (x : PhysicalPFReference.Position (Fin N × Fin 3)) : ℝ :=
  t.2.weight ((split i) x).1

theorem currentWeight_measurable (t : Fin 3 × SpatialTest) :
    AEStronglyMeasurable (currentWeight N i t) volume :=
  t.2.measurable.comp_fst.comp_measurePreserving (split_measurePreserving i)

theorem currentWeight_bound (t : Fin 3 × SpatialTest)
    (x : PhysicalPFReference.Position (Fin N × Fin 3)) : |currentWeight N i t x| ≤ 1 := by
  simpa only [currentWeight, Real.norm_eq_abs] using t.2.bounded ((split i) x).1

theorem densityWeight_measurable (t : SpatialTest) :
    AEStronglyMeasurable (densityWeight N i t) volume :=
  (t.measurable.comp_fst.comp_measurePreserving (split_measurePreserving i)).const_mul (N : ℝ)

theorem densityWeight_bound (t : SpatialTest)
    (x : PhysicalPFReference.Position (Fin N × Fin 3)) :
    |densityWeight N i t x| ≤ (N : ℝ) := by
  change |(N : ℝ) * t.weight ((split i) x).1| ≤ _
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
  exact (mul_le_mul_of_nonneg_left
    (show |t.weight ((split i) x).1| ≤ 1 by
      simpa only [Real.norm_eq_abs] using t.bounded ((split i) x).1)
    (Nat.cast_nonneg N)).trans_eq (mul_one _)

def direction (t : Fin 3 × SpatialTest) : Fin N × Fin 3 := (i, t.1)

variable (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (k : (Fin N × Fin 3) → PhysicalPFReference.Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hk : ∀ j, AEStronglyMeasurable (k j) volume)
  (M : ℝ) (hM : ∀ j, ∀ᵐ x ∂volume, ‖k j x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground) (e : ℝ)

def density : SpatialTest → B.Trace (WaveSpace (Fin N × Fin 3)) →L[ℝ] ℝ :=
  PhysicalRemovalObservables.densityFull N B (densityWeight N i) (densityWeight_measurable N i)
    (fun _ => (N : ℝ)) (densityWeight_bound N i)

def current (t : Fin 3 × SpatialTest) :
    FormObservable (normalEnergy (Fin N × Fin 3) V C k hk M hM B S e) :=
  testedCurrent (Fin N × Fin 3) V C k hk M hM B S e
    (currentWeight N i t) (currentWeight_measurable N i t) 1
    (ae_of_all _ (currentWeight_bound N i t)) (direction N i t)

variable {B}

private theorem integral_scaled_weight {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (c : ℝ) (a f : X → ℝ) :
    (∫ z, (c * a z) * f z ∂μ) = c * ∫ z, a z * f z ∂μ := by
  simp only [mul_assoc, integral_const_mul]

attribute [local irreducible] boundedTrace PhotonLocalization.realL2Multiplier

set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 400000 in
set_option diagnostics true in
theorem density_eq_source {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (source : Source (Fin N × Fin 3) V B x)
    (he : (normalEnergy (Fin N × Fin 3) V C k hk M hM B S e).expectation x < ⊤)
    (t : SpatialTest) :
    density N i B t x = ∫ z, t.weight z *
      densityL1 (source.pair C M S e i V k hk hM he) z := by
  have hsum := (density N i B t).hasSum source.hasSum
  have hterm (n : ℕ) : density N i B t
      ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne
        (inclusion (Fin N × Fin 3) V (source.vector n))) =
      (N : ℝ) * ∫ z, t.weight ((split i) z).1 *
        ‖inclusion (Fin N × Fin 3) V (source.vector n) z‖ ^ 2 := by
    unfold density PhysicalRemovalObservables.densityFull
    exact (boundedTrace_multiplier_rankOne
      (X := PhysicalPFReference.Position (Fin N × Fin 3)) (H := PhotonFock)
      (T := B.Trace (WaveSpace (Fin N × Fin 3)))
      (R := (B.realization (WaveSpace (Fin N × Fin 3))).rank)
      (B.realization (WaveSpace (Fin N × Fin 3))).functional
      (densityWeight N i t) (densityWeight_measurable N i t) (N : ℝ)
      (ae_of_all _ (densityWeight_bound N i t))
      (inclusion (Fin N × Fin 3) V (source.vector n))).trans
      (integral_scaled_weight volume (N : ℝ) (fun z => t.weight ((split i) z).1)
        (fun z => ‖inclusion (Fin N × Fin 3) V (source.vector n) z‖ ^ 2))
  have hs := hsum.congr_fun (fun n => (hterm n).symm)
  have heq := hs.tsum_eq
  rw [tsum_mul_left] at heq
  exact heq.symm.trans
    (source.pair_tested_density C M S e i V k hk hM he t.weight t.measurable
      (ae_of_all _ t.bounded)).symm

theorem current_eq_source {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (source : Source (Fin N × Fin 3) V B x)
    (he : (normalEnergy (Fin N × Fin 3) V C k hk M hM B S e).expectation x < ⊤)
    (b : Fin 3) (t : SpatialTest) :
    (∑ _j : Fin N, (current N i V C k hk M hM B S e (b, t)).value x) =
      ∫ z, t.weight z * currentL1 (source.pair C M S e i V k hk hM he) z b := by
  have hs := testedCurrent_source_hasSum (Fin N × Fin 3) V C k hk M hM B S e source he
    (currentWeight N i (b, t)) (currentWeight_measurable N i (b, t)) 1
    (ae_of_all _ (currentWeight_bound N i (b, t))) (i, b)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact (congrArg (fun r : ℝ => (N : ℝ) * r) hs.tsum_eq.symm).trans
    (source.pair_tested_current C M S e i V k hk hM he b t.weight t.measurable
      (ae_of_all _ t.bounded)).symm

variable (B)

/-- The tested observables recover the already constructed physical pair on every form state. -/
def pairData : PhysicalPairData (density N i B) (current N i V C k hk M hM B S e)
    (volume : Measure PhysicalPairSpace.Position) (Fin N) (Fin 3) where
  rho m := densityL1 (PhysicalPFStates.statePair i V C k hk M hM B S e m)
  currentDensity m := currentL1 (PhysicalPFStates.statePair i V C k hk M hM B S e m)
  rho_integrable _m := density_integrable _
  current_integrable _m b := current_component_integrable _ b
  densityTest := id
  currentTest _ b t := (b, t)
  density_eval m t := density_eq_source N i V C k hk M hM S e
    (PhysicalPFStates.source V C k hk M hM B S e m.val m.property.1 m.property.2.2)
    m.property.2.2 t
  current_eval m b t := current_eq_source N i V C k hk M hM S e
    (PhysicalPFStates.source V C k hk M hM B S e m.val m.property.1 m.property.2.2)
    m.property.2.2 b t

end GptLean.PhysicalRemovalPair
