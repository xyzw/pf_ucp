import PfHk.PauliMagneticOperatorRealization

/-! Removing the actual classical and quantum Zeeman sources from a
global Pauli weak operator pair gives each orbital weak operator pair.
All comparison-domain and magnetic multiplier witnesses are derived. -/

noncomputable section
namespace PfHk.PauliCarlemanOperatorSource

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain PfHk.PhysicalFieldRegularity
  PfHk.PauliSpin PfHk.PhysicalExternalSource PfHk.PhysicalExternalOperator
  PfHk.FriedrichsDivergenceBackground PfHk.KatoRellichBackground

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] inclusion referenceSubspace FreeGraph total
  PauliMagneticOperator.quantum PauliMagneticClassicalOperator.zeeman

private theorem subtract_sources {H : Type*} [AddCommGroup H]
    {f g a b q : H} (h : f = g + (a + b + q)) :
    f - b - q = g + a := by
  rw [h]
  abel

variable {N : ℕ}
  (a : PhysicalExternalCoefficients.Data N)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
  (B : Fin N → Fin 3 → PhysicalSourceCoordinates.Position → ℝ)
  (S : CoordinateSobolev.Data PhotonFock N)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
  (joint : CoordinateComparisonSpectral.Data spectral)
  (hD : HaslerHerbstDomain C κ hκ M hbound e)
  {p : ℝ} (hp : 2 < p)
  (hBp : ∀ n k, MemLp (B n k) (ENNReal.ofReal p) volume)
  (friedrichs : StandardFriedrichsDivergence) (KR : StandardKatoRellich)
  (hG : HaslerHerbstGraphNorm C κ hκ M hbound e)
  (hSA : SelfAdjointGraph (freeHilbertGraph (fun _ => 0) C κ hκ M hbound e))

include S spectral joint hD hp hBp friedrichs KR hG hSA in
theorem orbital_pairs
    (u : PauliReference.Ref N)
    (hu : PauliGroundState.Domain a.vector a.positive a.negative u)
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hf : PauliMagneticOperatorRealization.IsOperatorPair a C κ hκ M hbound e
      F χ hUV B u hu f) :
    ∃ hB : ∀ n k s, HasMultiplier (CoordinateSobolev.coordinateCoefficient n (B n k))
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)),
      (∀ s, ComparisonDomain (fun _ => 0) (u s)) ∧
      ∀ s, PhysicalCutoffCommutator.IsOperatorPair (fun _ => 0) C κ hκ M hbound e
        a.vector a.positive a.negative (u s) (hu s)
        (f s - PauliMagneticClassicalOperator.zeeman B u hB s -
          PauliMagneticOperator.quantum F χ hUV C e u s) := by
  have hex := (PauliMagneticOperatorRealization.operatorPair_iff_free_total
    a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp
    friedrichs KR hG hSA u hu f).mp hf
  let g := Classical.choose hex
  let hg := Classical.choose (Classical.choose_spec hex)
  have hfg := Classical.choose_spec (Classical.choose_spec hex)
  let hB := PauliMagneticOperatorRealization.magneticMultipliers
    C κ hκ M hbound e B S spectral joint hD hp hBp u g hg
  refine ⟨hB, PauliMagneticOperatorRealization.comparison
    C κ hκ M hbound e hD u g hg, ?_⟩
  intro s
  apply (PhysicalExternalOperator.operatorPair_iff_free_total a S spectral joint
    friedrichs KR C κ hκ M hbound e hD hG hSA (u s) _ (hu s)).mpr
  refine ⟨g s, hg s, ?_⟩
  have hfs := congrArg (fun v : SpinIndex N → WaveSpace (Fin N × Fin 3) => v s) hfg
  change f s = g s +
    (total a C κ hκ M hbound e (u s)
      (PauliMagneticOperatorRealization.products a C κ hκ M hbound e
        S spectral joint hD u g hg s) +
      PauliMagneticClassicalOperator.zeeman B u hB s +
      PauliMagneticOperator.quantum F χ hUV C e u s) at hfs
  exact subtract_sources hfs

end PfHk.PauliCarlemanOperatorSource

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
