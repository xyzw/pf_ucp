import GptLean.PhysicalPFSpectral

/-!
One normalized pure ensemble realizes each actual finite-energy mixed
Pauli--Fierz state, its full density-current pair and its energy.

The countable pair series converges in the article's Banach pair space.
The same weights and vectors therefore work simultaneously for every
potential. These are conclusions obtained from the supported reference
source, rather than a spectral-pair matching hypothesis.
-/

noncomputable section

namespace GptLean.PhysicalPFSpectralPair

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace PhysicalClosedForms
  PhysicalPFSource PhysicalPFPairSeries PhysicalNormalStates PhysicalNormalSpectral
  PhysicalPFSpectral
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

attribute [local irreducible] normalEnergy

variable {N : ℕ} (i : Fin N) (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → PhysicalPFReference.Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ x ∂volume, ‖κ q x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

set_option backward.isDefEq.respectTransparency.types false in
/-- The trace state, full pair and energy are simultaneous countable
barycenters of one normalized fermionic pure family. In particular the
chosen family is independent of the external potential. -/
theorem exists_pure_ensemble
    (m : PhysicalPFStates.MixedState V C κ hκ M hbound B S e) :
    ∃ (p : ℕ → PhysicalPFStates.PureState V C κ hκ M hbound B S e) (w : ℕ → ℝ),
      (∀ n, 0 ≤ w n) ∧ HasSum w 1 ∧
      HasSum (fun n => w n •
        (B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne (p n).val) m.val.val ∧
      HasSum (fun n => w n •
        (PhysicalPFStates.pureModel i V C κ hκ M hbound B S e).density (p n))
        ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).density m) ∧
      HasSum (fun n => w n *
        (PhysicalPFStates.pureModel i V C κ hκ M hbound B S e).energy (p n))
        ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).energy m) ∧
      ∀ a : PhysicalPairDuality.Potential,
        HasSum (fun n => w n *
          ((PhysicalPFStates.pureModel i V C κ hκ M hbound B S e).energy (p n) +
            PhysicalPairDuality.pairPotential a
              ((PhysicalPFStates.pureModel i V C κ hκ M hbound B S e).density (p n))))
          ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).energy m +
            PhysicalPairDuality.pairPotential a
              ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).density m)) := by
  let E : RemovalState.PositiveForm
      (positiveTrace (B.normal (H := WaveSpace (Fin N × Fin 3)))
        (B.realization (WaveSpace (Fin N × Fin 3))).functional) :=
    normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e
  let P := PhysicalElectronicFermions.projection N PhotonFock
  let s : SupportedSource N V B m.val.val := Classical.choice
    (supported_source_exists N V B C κ hκ M hbound S e (x := m.val.val)
      m.val.property.1 m.val.property.2.2 m.property)
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
  have hdata := normalized_source
    (H := WaveSpace (Fin N × Fin 3)) (T := B.Trace (WaveSpace (Fin N × Fin 3)))
    (R := (B.realization (WaveSpace (Fin N × Fin 3))).rank)
    (normal := B.normal) (F := (B.realization (WaveSpace (Fin N × Fin 3))).functional)
    E P s.hasSum m.val.property.2.2 hP hmass
  let p₀ := Classical.choose hdata
  have htrace := (Classical.choose_spec hdata).1
  have henergyRaw := (Classical.choose_spec hdata).2
  let p (n : ℕ) := sourcePure E P p₀ (v n) (hP n) (hfinite n)
  have henergy : HasSum (fun n => ‖v n‖ ^ 2 *
      (PhysicalPFStates.pureModel i V C κ hκ M hbound B S e).energy (p n))
      ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).energy m) := henergyRaw
  have hpair : HasSum (fun n => ‖v n‖ ^ 2 •
      (PhysicalPFStates.pureModel i V C κ hκ M hbound B S e).density (p n))
      ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).density m) := by
    exact (mixed_pair_hasSum i V C κ hκ M hbound B S e m s.toSource).congr_fun (fun n =>
      sourcePure_pair_weight i V C κ hκ M hbound B S e p₀
        (s.vector n) (hP n) (hfinite n))
  refine ⟨p, (fun n => ‖v n‖ ^ 2), (fun n => sq_nonneg _), hmass,
    htrace, hpair, henergy, ?_⟩
  intro a
  have hpot := (PhysicalPairDuality.pairPotential a).hasSum hpair
  simpa only [map_smul, smul_eq_mul, mul_add] using henergy.add hpot

/-- The actual pure and mixed PF models have the same potential ground
energy. This uses the proved spectral sums and rank-one inclusion. -/
theorem ground_eq (a : PhysicalPairDuality.Potential) :
    DFT.ground (PhysicalPFStates.pureModel i V C κ hκ M hbound B S e)
      (fun a p => PhysicalPairDuality.pairPotential a p) a =
    DFT.ground (PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e)
      (fun a p => PhysicalPairDuality.pairPotential a p) a :=
  Theorem48.ground_eq_of_spectral_ensembles _ _
    (PhysicalPFStates.pureEmbedding i V C κ hκ M hbound B S e)
    (fun a p => PhysicalPairDuality.pairPotential a p)
    (PhysicalPFSpectral.spectralEnsemble i V C κ hκ M hbound B S e) a

/-- The article potential pairing yields identical pure and mixed Lieb
functionals before any constrained-search attainment result is used. -/
theorem lieb_eq (d : PhysicalPairSpace.Pair) :
    DFT.lieb (PhysicalPFStates.pureModel i V C κ hκ M hbound B S e)
      (fun a p => PhysicalPairDuality.pairPotential a p) d =
    DFT.lieb (PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e)
      (fun a p => PhysicalPairDuality.pairPotential a p) d :=
  Theorem48.lieb_eq_of_spectral_ensembles _ _
    (PhysicalPFStates.pureEmbedding i V C κ hκ M hbound B S e)
    (fun a p => PhysicalPairDuality.pairPotential a p)
    (PhysicalPFSpectral.spectralEnsemble i V C κ hκ M hbound B S e) d

end GptLean.PhysicalPFSpectralPair
