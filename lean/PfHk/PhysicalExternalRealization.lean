import PfHk.PhysicalExternalDomain
import PfHk.PhysicalDivergenceApproximation
import PfHk.PhysicalExternalRelativeBound

/-! The actual external Hamiltonian graph on ordinary Lp coefficients.
Multiplier membership, the distributional form expansion and infinitesimal
relative bounds are derived before the universal Kato--Rellich theorem is
applied. The conclusion identifies the actual source with the finite sum
used by the weighted perturbation estimates. -/

noncomputable section
namespace PfHk.PhysicalExternalOperator

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.SymmetricLift PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain
open PfHk.PhysicalExternalCoefficients PfHk.PhysicalExternalSource PfHk.CoordinateSobolev
open PfHk.FriedrichsDivergenceBackground PfHk.KatoRellichBackground

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [local irreducible] inclusion covariant roughMultiply HasMultiplier perturbation total term
  FreeGraph PhysicalPFReference.referenceSubspace freeHilbertGraph
  PhysicalCutoffCommutator.IsOperatorPair

variable {N : ℕ}

theorem operatorPair_iff_free_total
    (a : PfHk.PhysicalExternalCoefficients.Data N) (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (friedrichs : StandardFriedrichsDivergence) (KR : StandardKatoRellich)
    (C : CanonicalSectorCCR photonMeasure)
    (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
    (hκ : ∀ i : Fin N × Fin 3, AEStronglyMeasurable (κ i) volume)
    (M : ℝ) (hbound : ∀ i : Fin N × Fin 3, ∀ᵐ x : Configuration N ∂volume, ‖(κ i x).val‖ ≤ M)
    (e : ℝ) (hD : HaslerHerbstDomain C κ hκ M hbound e)
    (hG : HaslerHerbstGraphNorm C κ hκ M hbound e)
    (hSA : SelfAdjointGraph (freeHilbertGraph (fun _ => 0) C κ hκ M hbound e))
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (f : WaveSpace (Fin N × Fin 3))
    (hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u) :
    PhysicalCutoffCommutator.IsOperatorPair (fun _ => 0) C κ hκ M hbound e
      a.vector a.positive a.negative u hu f ↔
    ∃ (g : WaveSpace (Fin N × Fin 3)) (hg : FreeGraph C κ hκ M hbound e u g),
      f = g + total a C κ hκ M hbound e u
        (products_of_comparison a C κ hκ M hbound e u S spectral joint ((hD u).mp ⟨g, hg⟩)) := by
  let comp (v : Reference (Fin N × Fin 3) (fun _ => 0)) (g : WaveSpace (Fin N × Fin 3))
      (hg : FreePair (fun _ => 0) C κ hκ M hbound e v g) : ComparisonDomain (fun _ => 0) v :=
    (hD v).mp ⟨g, (freeGraph_iff C κ hκ M hbound e v g).mpr hg⟩
  let hmul (v : Reference (Fin N × Fin 3) (fun _ => 0)) (g : WaveSpace (Fin N × Fin 3))
      (hg : FreePair (fun _ => 0) C κ hκ M hbound e v g) :=
    a.operatorMultipliers S spectral joint C κ hκ M hbound e v (comp v g hg)
  let approx := friedrichs.resolve N a.vectorCoefficient a.divergenceCoefficient
    a.divergenceExponent a.divergenceExponent_gt_two a.vector_memLp a.divergence_memLp a.weakDivergence
  have happ (v : Reference (Fin N × Fin 3) (fun _ => 0)) (g : WaveSpace (Fin N × Fin 3))
      (hg : FreePair (fun _ => 0) C κ hκ M hbound e v g)
      (w : Reference (Fin N × Fin 3) (fun _ => 0))
      (hw : ExternalDomain (fun _ => 0) a.vector a.positive a.negative w) :
      DivergenceApproximation (fun _ => 0) a.vector a.divergence v w
        (fun i => roughMultiply (a.vector i) (inclusion (Fin N × Fin 3) (fun _ => 0) v) ((hmul v g hg).domain.vector i))
        (fun i => roughMultiply (a.vector i) (inclusion (Fin N × Fin 3) (fun _ => 0) w) (hw.vector i))
        (roughMultiply a.divergence (inclusion (Fin N × Fin 3) (fun _ => 0) v) (hmul v g hg).divergence) :=
    divergenceApproximation_of_friedrichs S spectral joint a.vectorCoefficient a.divergenceCoefficient
      a.divergenceExponent a.divergenceExponent_gt_two approx v w (comp v g hg)
      (hmul v g hg).domain.vector hw.vector (hmul v g hg).divergence
  have hex := PhysicalExternalRelativeBound.infinitesimal_perturbation
    a S spectral joint C κ hκ M hbound e hD hG (1 / 2) (by norm_num)
  let K := Classical.choose hex
  have hK := Classical.choose_spec hex
  have hrel (v : Reference (Fin N × Fin 3) (fun _ => 0)) (g : WaveSpace (Fin N × Fin 3))
      (hg : FreePair (fun _ => 0) C κ hκ M hbound e v g) :
      ‖perturbation (fun _ => 0) C κ hκ M hbound e a.vector a.positive a.negative a.divergence v
        (hmul v g hg)‖ ≤ (1 / 2 : ℝ) * ‖g‖ + K * ‖inclusion (Fin N × Fin 3) (fun _ => 0) v‖ :=
    hK.2 v g ((freeGraph_iff C κ hκ M hbound e v g).mpr hg) (hmul v g hg)
  have hcore := operatorPair_iff_free_sum (fun _ => 0) C κ hκ M hbound e
    a.vector a.positive a.negative a.divergence hmul happ KR hSA
    (1 / 2) K (by norm_num) (by norm_num) hK.1 hrel u f hu
  constructor
  · intro hf
    have he := hcore.mp hf
    let g := Classical.choose he
    have hgdata := Classical.choose_spec he
    let hg : FreePair (fun _ => 0) C κ hκ M hbound e u g := Classical.choose hgdata
    have hfg := Classical.choose_spec hgdata
    have hgraph := (freeGraph_iff C κ hκ M hbound e u g).mpr hg
    let hc := (hD u).mp ⟨g, hgraph⟩
    let P := products_of_comparison a C κ hκ M hbound e u S spectral joint hc
    have hp := perturbation_eq_total a C κ hκ M hbound e u P (hmul u g hg)
      (a.scalar_hasMultiplier S spectral joint u hc)
    exact ⟨g, hgraph, hfg.trans (congrArg (fun z : WaveSpace (Fin N × Fin 3) => g + z) hp)⟩
  · intro hf
    let g := Classical.choose hf
    have hgdata := Classical.choose_spec hf
    let hg : FreeGraph C κ hκ M hbound e u g := Classical.choose hgdata
    have hfg := Classical.choose_spec hgdata
    have hpair := (freeGraph_iff C κ hκ M hbound e u g).mp hg
    let hc := (hD u).mp ⟨g, hg⟩
    let P := products_of_comparison a C κ hκ M hbound e u S spectral joint hc
    have hp := perturbation_eq_total a C κ hκ M hbound e u P (hmul u g hpair)
      (a.scalar_hasMultiplier S spectral joint u hc)
    exact hcore.mpr ⟨g, hpair, hfg.trans (congrArg (fun z : WaveSpace (Fin N × Fin 3) => g + z) hp.symm)⟩

end PfHk.PhysicalExternalOperator
