import GptLean.PhysicalAttainmentFunctionals
import GptLean.TransformationsTimeReversalFrame
import GptLean.ZeroCurrent

/-!
`prop-zero-current-density-functional` on the actual fermionic Pauli--Fierz
model with the article's polarization frame and cutoff.

The time reversal of `TransformationsTimeReversalFrame` makes the pure search
even in the combined current, for every frame. By the attainment theorem the
mixed search equals the Lieb functional, which is therefore even as well. The
mixed search is convex, because density matrices can be mixed. The
abstract statements of `ZeroCurrent` then give, for every density `ρ`:

* `zero-current-density-search`: `F_L(ρ, 0) = F̃_L(ρ, 0) = inf {Tr(H^{0,0} Γ) : ρ_Γ = ρ}`,
  and the infimum is attained at a density matrix with zero current whenever it
  is finite;
* `zero-current-scalar-dual`: `F_L(ρ, 0) = sup_v [E(v, 0) - ⟨v, ρ⟩]`, with `E(v, 0)`
  the variational ground energy of `H^{v,0}`;
* `zero-current-pure-density-search`: `F_LL(ρ, 0) = inf {⟨Ψ, H^{0,0} Ψ⟩ : ρ_Ψ = ρ}`,
  together with `F_LL(ρ, 0) = F_L(ρ, 0)`, given the exact-pair soft-photon recovery
  `many-electron-pure-approximation`. That recovery is the content of
  `thm-many-electron-soft-purification` and is an explicit hypothesis here.

The statements hold for every `ρ`. The hypothesis `√ρ ∈ H¹`, `∫ ρ = N` of the
article only ensures finiteness; that representability statement is not
formalized here.
-/

noncomputable section

namespace GptLean.PhysicalZeroCurrent

open MeasureTheory PhysicalFock PhysicalNormalTrace PhysicalClosedForms
  PhysicalPolarization PhysicalRemovalKernels PhysicalSobolevRealization
  PhysicalPhotonLocalizedNumber PhysicalPairSpace PhysicalPairDuality
  Gaussian SymmetricLift PhysicalAttainmentFunctionals TransformationsPotentials
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 800000

attribute [local irreducible] PhysicalPFReference.normalEnergy

variable {N : ℕ} (i : Fin N) (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (e : ℝ)

/-- The density-only mixed search `inf {Tr(H^{0,0} Γ) : Γ ∈ 𝒟, ρ_Γ = ρ}`. -/
def densityMixedFunctional (ρ : Density) : EReal :=
  ⨅ m : MixedState F χ C B S e (N := N),
    ⨅ (_ : ((PhysicalRemoval.model i F χ 1 C B S e).density m).1 = ρ),
      (mixedInternalEnergy F χ C B S e m : EReal)

/-- The density-only pure search `inf {⟨Ψ, H^{0,0} Ψ⟩ : Ψ ∈ 𝒬_PF, ‖Ψ‖ = 1, ρ_Ψ = ρ}`. -/
def densityPureFunctional (ρ : Density) : EReal :=
  ⨅ p : PureState F χ C B S e (N := N),
    ⨅ (_ : ((PhysicalAttainment.pureModel i F χ C B S e).density p).1 = ρ),
      (pureInternalEnergy F χ C B S e p : EReal)

theorem densityMixedFunctional_eq_search (ρ : Density) :
    densityMixedFunctional i F χ C B S e ρ =
      DFT.search (DFT.densityOnly (PhysicalRemoval.model i F χ 1 C B S e)) ρ :=
  iInf_congr fun m => iInf_congr fun _ => (mixedModel_energy_coe i F χ C B S e m).symm

theorem densityPureFunctional_eq_search (ρ : Density) :
    densityPureFunctional i F χ C B S e ρ =
      DFT.search (DFT.densityOnly (PhysicalAttainment.pureModel i F χ C B S e)) ρ :=
  iInf_congr fun p => iInf_congr fun _ => (pureModel_energy_coe i F χ C B S e p).symm

/-- **`F-time-reversal` for `F_LL`** on the article's model, for every frame. -/
theorem pureFunctional_flip (d : Pair) :
    pureFunctional i F χ C B S e (TransformationsPotentials.currentFlip d) =
      pureFunctional i F χ C B S e d :=
  TransformationsTimeReversal.search_reversal_frame F χ (LinearIsometryEquiv.refl ℝ _)
    (PhysicalRemoval.potential N 1) C e i B S d

/-- Removing the current constraint can only lower the pure search. -/
theorem densityPureFunctional_le (ρ : Density) :
    densityPureFunctional i F χ C B S e ρ ≤ pureFunctional i F χ C B S e (ρ, 0) :=
  (densityPureFunctional_eq_search i F χ C B S e ρ).trans_le
    (le_iInf₂ fun _ hp => DFT.search_le
      (DFT.densityOnly (PhysicalAttainment.pureModel i F χ C B S e)) (congrArg Prod.fst hp))

/-- The mixed search is convex. -/
theorem mixedFunctional_convex : DFT.ConvexEpigraph (mixedFunctional i F χ C B S e) :=
  DFT.mixed_search_convex _ (PhysicalPFStates.mixedModel_mixtureClosed i
    (PhysicalRemoval.potential N 1) C (full F χ N) (full_measurable F χ N) (bound F χ)
    (full_bound F χ N) B S e)

variable (BF : StandardSymmetricFockExponential) (BW : StandardWienerSegal)
  (core : CountableSpatialTestCore) (smooth : SmoothSobolevBackground)
  (C₀ : ℝ) (scaled : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C₀)
  (B₀ : TensorBackground Repair.SixTag) (B₁ : TensorMultilinearData B₀)
  {ι : Type*} (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target)
  (index : ι ↪ ℕ) (Sob : StandardHomogeneousSobolev)
  (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
  (Hardy : StandardFractionalHardy)
  (hLp : StandardFiniteDimensionalLpRepresentation) (hFM : StandardDualFenchelMoreau)

include BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **`F-time-reversal` for the mixed search** and hence for `F_L`. -/
theorem mixedFunctional_flip (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) (d : Pair) :
    mixedFunctional i F χ C B S e (TransformationsPotentials.currentFlip d) =
      mixedFunctional i F χ C B S e d := by
  obtain ⟨_, _, _, _, _, heq⟩ := unrestricted_attainment i F χ C B S e BF BW core smooth C₀
    scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM he hC₀
  exact (heq _).trans ((lieb_flip (PhysicalAttainment.pureModel i F χ C B S e)
    (pureFunctional_flip i F χ C B S e) d).trans (heq d).symm)

include BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **`prop-zero-current-density-functional`, mixed and dual parts.** For every
density `ρ`:
1. `F_L(ρ, 0) = inf {Tr(H^{0,0} Γ) : ρ_Γ = ρ}` (`zero-current-density-search`);
2. the same holds for the mixed constrained search `F̃_L(ρ, 0)`;
3. the infimum is attained at a density matrix with pair `(ρ, 0)` when finite;
4. `F_L(ρ, 0) = sup_v [E(v, 0) - ⟨v, ρ⟩]` (`zero-current-scalar-dual`). -/
theorem zero_current_density_functional (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) (ρ : Density) :
    liebFunctional i F χ C B S e (ρ, 0) = densityMixedFunctional i F χ C B S e ρ ∧
    mixedFunctional i F χ C B S e (ρ, 0) = densityMixedFunctional i F χ C B S e ρ ∧
    (densityMixedFunctional i F χ C B S e ρ < ⊤ →
      ∃ m : MixedState F χ C B S e (N := N),
        (PhysicalRemoval.model i F χ 1 C B S e).density m = (ρ, 0) ∧
        (mixedInternalEnergy F χ C B S e m : EReal) = densityMixedFunctional i F χ C B S e ρ) ∧
    liebFunctional i F χ C B S e (ρ, 0) =
      ⨆ v : ScalarPotential, shiftedGroundEnergy i F χ C B S e (v, 0) - (pairing v ρ : EReal) := by
  obtain ⟨_, _, hatt, _, _, heq⟩ := unrestricted_attainment i F χ C B S e BF BW core smooth C₀
    scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM he hC₀
  have hsym : ∀ (ρ' : Density) (j : Current),
      DFT.search (PhysicalRemoval.model i F χ 1 C B S e) (ρ', -j) =
        DFT.search (PhysicalRemoval.model i F χ 1 C B S e) (ρ', j) := fun ρ' j =>
    mixedFunctional_flip i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index Sob Rellich
      Hardy hLp hFM he hC₀ (ρ', j)
  have h₂ : mixedFunctional i F χ C B S e (ρ, 0) = densityMixedFunctional i F χ C B S e ρ :=
    (ZeroCurrent.search_zero_current _ (mixedFunctional_convex i F χ C B S e) hsym ρ).trans
      (densityMixedFunctional_eq_search i F χ C B S e ρ).symm
  refine ⟨(heq _).symm.trans h₂, h₂, fun hfin => ?_, ?_⟩
  · obtain ⟨m, hm, henergy, _, _⟩ := hatt (ρ, 0) (h₂.trans_lt hfin)
    exact ⟨m, hm, henergy.trans h₂⟩
  · exact ZeroCurrent.lieb_zero_current (PhysicalAttainment.pureModel i F χ C B S e)
      (fun a d => pairPotential a d) (fun v ρ' => pairing v ρ') (fun a j => pairing a j)
      (fun _ _ => rfl) (fun a j => map_neg (pairing a) j)
      (fun j => by rw [pairing_zero]; rfl)
      (fun ρ' j => pureFunctional_flip i F χ C B S e (ρ', j)) ρ

include BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **`prop-zero-current-density-functional`, pure part**, given the exact-pair
soft-photon recovery `many-electron-pure-approximation`:
`F_LL(ρ, 0) = inf {⟨Ψ, H^{0,0} Ψ⟩ : ρ_Ψ = ρ}` (`zero-current-pure-density-search`),
and `F_LL(ρ, 0) = F_L(ρ, 0)`. -/
theorem pure_zero_current (he : 0 ≤ e) (hC₀ : 0 ≤ C₀)
    (recovery : DFT.ExactRecovery (PhysicalAttainment.pureModel i F χ C B S e)
      (PhysicalRemoval.model i F χ 1 C B S e)) (ρ : Density) :
    pureFunctional i F χ C B S e (ρ, 0) = densityPureFunctional i F χ C B S e ρ ∧
      pureFunctional i F χ C B S e (ρ, 0) = liebFunctional i F χ C B S e (ρ, 0) := by
  obtain ⟨_, _, _, _, _, heq⟩ := unrestricted_attainment i F χ C B S e BF BW core smooth C₀
    scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM he hC₀
  have hsym : ∀ (ρ' : Density) (j : Current),
      DFT.search (PhysicalRemoval.model i F χ 1 C B S e) (ρ', -j) =
        DFT.search (PhysicalRemoval.model i F χ 1 C B S e) (ρ', j) := fun ρ' j =>
    mixedFunctional_flip i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index Sob Rellich
      Hardy hLp hFM he hC₀ (ρ', j)
  have emb := PhysicalPFStates.pureEmbedding i (PhysicalRemoval.potential N 1) C
    (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e
  exact ⟨(ZeroCurrent.pure_zero_current _ _ emb recovery (mixedFunctional_convex i F χ C B S e)
      hsym ρ).trans (densityPureFunctional_eq_search i F χ C B S e ρ).symm,
    (DFT.pure_eq_mixed _ _ emb recovery (ρ, 0)).trans (heq (ρ, 0))⟩

end GptLean.PhysicalZeroCurrent
