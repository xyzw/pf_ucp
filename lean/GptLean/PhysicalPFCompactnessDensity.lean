import GptLean.PhysicalNormalElectronicDensity
import GptLean.PhysicalPFSupportedSource
import GptLean.PhysicalPFStates
import GptLean.PhotonLocalizationPhysicalCompactness

/-!
The density used in trace compactness agrees with the article density of
the same finite-energy fermionic normal state. Consequently convergence
of physical density-current pairs supplies electronic tightness. Neither
a density-tail estimate nor trace precompactness is an input.
-/

noncomputable section

namespace GptLean.PhysicalPFCompactnessDensity

open MeasureTheory Filter Topology PhysicalFock PhysicalPFReference PhysicalNormalTrace
open PhysicalClosedForms PhysicalPFSource PhysicalPairSpace PhotonLocalization
open PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal BoundedContinuousFunction

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option maxHeartbeats 200000

private theorem position_tail_le {N : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : (SpatialPhotonL2 (Fin N × Fin 3) H →L[ℂ]
      SpatialPhotonL2 (Fin N × Fin 3) H) →L[ℂ] ℂ)
    (ν : Measure (Fin N → ElectronicPosition)) [IsFiniteMeasure ν]
    (ρ : Lp ℝ 1 (volume : Measure ElectronicPosition))
    (htrace : ∀ f, (φ (positionObservable (K := H) f)).re = ∫ z, f z ∂ν)
    (hdensity : ElectronicDensityMeasure ν ρ) (L : ℕ) :
    (φ ((1 - (physicalElectronicFamily (N := N) L).operator (K := H)) ^ 2)).re ≤
      densityTail physicalElectronicRegion L ρ := by
  let P : ElectronicPositionTrace φ ν := physicalPositionTrace (K := H) φ ν htrace
  have hc : P.cutoff ((L : ℝ) + 1) =
      (physicalElectronicFamily (N := N) L).operator (K := H) :=
    positionObservable_cutoff (K := H) _ (by positivity)
  have h := P.tail_le ρ hdensity (L := (L : ℝ) + 1) (by positivity)
  rw [hc] at h
  exact h

variable (B : StandardNormalTraceBackground) (N : ℕ)

abbrev density : B.FullTrace N → Lp ℝ 1 (volume : Measure PhysicalPairSpace.Position) :=
  PhysicalNormalElectronicDensity.density (B.normal (H := FullHilbert N))

abbrev position : B.FullTrace N → Measure (Fin N → ElectronicPosition) :=
  PhysicalNormalElectronicDensity.position (B.normal (H := FullHilbert N))

theorem position_trace {x : B.FullTrace N}
    (hx : x ∈ (B.realization (FullHilbert N)).rank.positive)
    (f : (Fin N → ElectronicPosition) →ᵇ ℝ) :
    ((B.realization (FullHilbert N)).functional.repr x (positionObservable f)).re =
      ∫ z, f z ∂position B N x :=
  PhysicalNormalElectronicDensity.position_trace B.normal
    (B.realization (FullHilbert N)).functional hx f

theorem electronicDensityMeasure (x : B.FullTrace N) :
    ElectronicDensityMeasure (position B N x) (density B N x) :=
  PhysicalNormalElectronicDensity.electronicDensityMeasure B.normal x

theorem density_norm {x : B.FullTrace N} (hx : x ∈ B.fermionicStates N) :
    ‖density B N x‖ = N :=
  (PhysicalNormalElectronicDensity.density_norm B.normal hx.1).trans
    ((congrArg (fun r : ℝ => (N : ℝ) * r) hx.2.1).trans (mul_one _))

theorem electronic_tail {x : B.FullTrace N}
    (hx : x ∈ (B.realization (FullHilbert N)).rank.positive) (L : ℕ) :
    ((B.realization (FullHilbert N)).functional.repr x
      ((1 - (physicalElectronicFamily (N := N) L).operator (K := PhotonFock)) ^ 2)).re ≤
        densityTail physicalElectronicRegion L (density B N x) :=
  position_tail_le (N := N) (H := PhotonFock)
    ((B.realization (FullHilbert N)).functional.repr x)
    (position B N x) (density B N x) (position_trace B N hx)
    (electronicDensityMeasure B N x) L

theorem electronic_tail_lift
    (U : PhotonFock →ₗᵢ[ℂ] lp (fun _ : ℕ => PhotonFock) 2) {x : B.FullTrace N}
    (hx : x ∈ (B.realization (FullHilbert N)).rank.positive) (L : ℕ) :
    ((B.realization (FullHilbert N)).functional.repr
      (B.normal.extend (KrausL2.lift volume U) x)
      ((1 - (physicalElectronicFamily (N := N) L).operator (K := PhotonFock)) ^ 2)).re ≤
        densityTail physicalElectronicRegion L (density B N x) := by
  let y : B.FullTrace N := (B.normal (H := FullHilbert N)).extend
    (KrausL2.lift (volume : Measure (SymmetricLift.Configuration N)) U) x
  have htrace := PhysicalNormalElectronicDensity.position_trace_lift
    (N := N) (H := PhotonFock) (T := B.FullTrace N)
    (R := (B.realization (FullHilbert N)).rank)
    (B.normal (H := FullHilbert N)) (B.realization (FullHilbert N)).functional U hx
  exact position_tail_le (N := N) (H := PhotonFock)
    ((B.realization (FullHilbert N)).functional.repr y)
    (position B N x) (density B N x) htrace (electronicDensityMeasure B N x) L

variable {N}
  (i : Fin N) (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → PhysicalPFReference.Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ x ∂volume, ‖κ q x‖ ≤ M)
  (S : StandardClosedFormBackground) (e : ℝ)

theorem density_eq_pair {x : B.FullTrace N}
    (hx : x ∈ (B.realization (FullHilbert N)).rank.positive)
    (he : (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation x < ⊤)
    (hP : B.conjugation.conjugate (PhysicalElectronicFermions.projection N PhotonFock) x = x) :
    density B N x = densityL1 (PhysicalPFStates.pair i V C κ hκ M hbound B S e x hx he) := by
  obtain ⟨s⟩ := supported_source_exists N V B C κ hκ M hbound S e hx he hP
  have hp := PhysicalPFStates.pair_eq_source i V C κ hκ M hbound B S e x hx he s.toSource
  apply Lp.ext
  apply RemovalConstraints.ae_eq_of_boundedSpatialTests
    (memLp_one_iff_integrable.mp (Lp.memLp _))
    (memLp_one_iff_integrable.mp (Lp.memLp _))
  intro t
  have hleft := PhysicalNormalElectronicDensity.density_tested_fermionic B.normal
    (B.realization (FullHilbert N)).functional hx
    (fun n => inclusion (Fin N × Fin 3) V (s.vector n)) s.hasSum s.fermionic
    i t.weight t.measurable t.bounded
  have hright := s.toSource.pair_tested_density C M S e i V κ hκ hbound he
    t.weight t.measurable (ae_of_all _ t.bounded)
  have heq : (∫ z, t.weight z * densityL1
      (PhysicalPFStates.pair i V C κ hκ M hbound B S e x hx he) z) =
      ∫ z, t.weight z * densityL1 (s.toSource.pair C M S e i V κ hκ hbound he) z :=
    congrArg (fun p : PhysicalPairSpace.Pair => ∫ z, t.weight z * densityL1 p z) hp
  have hright' : (∫ z, t.weight z * densityL1 (s.toSource.pair C M S e i V κ hκ hbound he) z) =
      (N : ℝ) * ∑' n, ∫ z, t.weight (SymmetricLift.particle z i) *
        ‖inclusion (Fin N × Fin 3) V (s.vector n) z‖ ^ 2 := by
    simpa only [PhysicalSourcePair.split_fst_eq_particle] using hright
  exact hleft.trans (hright'.symm.trans heq.symm)

theorem density_tendsto_of_pair_tendsto
    (x : ℕ → B.FullTrace N)
    (hx : ∀ n, x n ∈ (B.realization (FullHilbert N)).rank.positive)
    (he : ∀ n, (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation (x n) < ⊤)
    (hP : ∀ n, B.conjugation.conjugate
      (PhysicalElectronicFermions.projection N PhotonFock) (x n) = x n)
    {p : PhysicalPairSpace.Pair}
    (hp : Tendsto (fun n => PhysicalPFStates.pair i V C κ hκ M hbound B S e
      (x n) (hx n) (he n)) atTop (𝓝 p)) :
    Tendsto (fun n => density B N (x n)) atTop (𝓝 (densityL1 p)) := by
  have h := (continuous_densityL1.tendsto p).comp hp
  exact h.congr fun n => (density_eq_pair B i V C κ hκ M hbound S e (hx n) (he n) (hP n)).symm

theorem electronicTight_of_pair_tendsto
    (x : ℕ → B.FullTrace N)
    (hx : ∀ n, x n ∈ (B.realization (FullHilbert N)).rank.positive)
    (he : ∀ n, (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation (x n) < ⊤)
    (hP : ∀ n, B.conjugation.conjugate
      (PhysicalElectronicFermions.projection N PhotonFock) (x n) = x n)
    {p : PhysicalPairSpace.Pair}
    (hp : Tendsto (fun n => PhysicalPFStates.pair i V C κ hκ M hbound B S e
      (x n) (hx n) (he n)) atTop (𝓝 p)) :
    DensityTight physicalElectronicRegion (fun n => density B N (x n)) := by
  apply densityTight_of_tendsto physicalElectronicRegion (fun _ => measurableSet_closedBall)
    (fun L K h => Metric.closedBall_subset_closedBall (by exact_mod_cast Nat.add_le_add_right h 1))
    ?_ (density_tendsto_of_pair_tendsto B i V C κ hκ M hbound S e x hx he hP hp)
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨L, hL⟩ := exists_nat_ge ‖z‖
  apply Set.mem_iUnion.mpr
  refine ⟨L, ?_⟩
  change dist z 0 ≤ (L : ℝ) + 1
  rw [dist_zero_right]
  linarith

end GptLean.PhysicalPFCompactnessDensity
