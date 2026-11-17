import GptLean.PhysicalAttainmentCompactness
import GptLean.PhysicalPFMixtures
import GptLean.PhysicalPFSpectralPair
import GptLean.PhysicalPFSeed
import GptLean.PhysicalPairDuality

/-!
Attainment of the mixed constrained search on the article's actual fermionic
Pauli--Fierz model, with Coulomb coefficient one. The infrared repair and
constraint-closure inputs are supplied by the constructed physical model.
The same theorem gives a pair-independent photon-number bound for every
optimizer, norm lower semicontinuity and equality with the pure-state Lieb
functional. Only the named universal analytic backgrounds remain parameters.
-/

noncomputable section

namespace GptLean.PhysicalAttainment

open MeasureTheory PhysicalFock PhysicalNormalTrace PhysicalClosedForms
  PhysicalPolarization PhysicalRemovalKernels PhysicalSobolevRealization
  PhysicalPhotonLocalizedNumber Gaussian SymmetricLift
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true

private theorem assemble_attainment
    {P M D V Ω : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [MeasurableSpace Ω]
    (A : DFT.StateModel P D) (B : DFT.StateModel M D)
    (number : M → ℝ≥0∞) (μ : Measure Ω) [SFinite μ]
    (ω : Ω → ℝ) (w : Ω → ℝ≥0∞)
    (hI : Nonempty (AttainmentConstruction.InfraredRepairData B number μ ω w))
    (hpositive : ∀ m, 0 ≤ B.energy m)
    (hloss : ∀ d, Attainment.PhotonLossInput M (fun m => B.density m = d)
      B.energy number)
    (hclosed : Closure.BoundedConstraintClosure B number)
    (m₀ : M) (hmix : DFT.MixtureClosed B)
    (emb : DFT.PureEmbedding A B) (pair : V → D → ℝ)
    (spectral : ∀ m v, Nonempty (Theorem48.SpectralEnsemble A B pair m v))
    (fm : DFT.FenchelMoreau pair) :
    ∃ Cnumber : ℝ, 0 ≤ Cnumber ∧
      (∀ d, DFT.search B d < ⊤ → ∃ m,
        B.density m = d ∧ (B.energy m : EReal) = DFT.search B d ∧
          number m ≤ ENNReal.ofReal (Cnumber * (1 + B.energy m)) ∧ number m < ⊤) ∧
      (∀ m, (B.energy m : EReal) = DFT.search B (B.density m) →
        number m ≤ ENNReal.ofReal (Cnumber * (1 + B.energy m))) ∧
      LowerSemicontinuous (DFT.search B) ∧
      (∀ d, DFT.search B d = DFT.lieb A pair d) := by
  obtain ⟨I⟩ := hI
  have h := Theorem48.all_conclusions_of_closure A B number μ ω w I
    hpositive hloss hclosed m₀ hmix emb pair spectral fm
  refine ⟨I.numberConstant, I.numberConstant_nonneg, ?_, h.2.1, h.2.2.1, h.2.2.2⟩
  intro d hd
  obtain ⟨m, hm, he, hn⟩ := h.1 d hd
  exact ⟨m, hm, he, hn, hn.trans_lt ENNReal.ofReal_lt_top⟩

variable {N : ℕ} (i : Fin N) (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (BF : StandardSymmetricFockExponential)
  (BW : StandardWienerSegal) (e : ℝ)

/-- The actual fermionic pure-state model with the article Coulomb interaction. -/
abbrev pureModel := PhysicalPFStates.pureModel i (PhysicalRemoval.potential N 1) C
  (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e

variable (core : CountableSpatialTestCore) (smooth : SmoothSobolevBackground)
  (C₀ : ℝ) (scaled : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C₀)
  (B₀ : TensorBackground Repair.SixTag) (B₁ : TensorMultilinearData B₀)
  {ι : Type*} (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target)
  (index : ι ↪ ℕ)
  (Sob : StandardHomogeneousSobolev)
  (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
  (Hardy : StandardFractionalHardy)
  (hLp : PhysicalPairDuality.StandardFiniteDimensionalLpRepresentation)
  (hFM : PhysicalPairDuality.StandardDualFenchelMoreau)

attribute [local irreducible] PhysicalPFReference.normalEnergy

include BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- The mixed search is attained at every representable physical pair. One
constant bounds the photon number of every optimizer, independently of the
pair. The search is norm lower semicontinuous and equals the article's
pure-state Lieb functional. No finite-number condition is imposed on the
states defining the search. -/
theorem all_conclusions (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) :
    ∃ Cnumber : ℝ, 0 ≤ Cnumber ∧
      (∀ d, DFT.search (PhysicalRemoval.model i F χ 1 C B S e) d < ⊤ →
        ∃ m : PhysicalRemoval.mixedState F χ 1 C B S e (N := N),
          (PhysicalRemoval.model i F χ 1 C B S e).density m = d ∧
          ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
            DFT.search (PhysicalRemoval.model i F χ 1 C B S e) d ∧
          PhysicalRemoval.number F χ 1 C B S e m ≤
            ENNReal.ofReal (Cnumber * (1 + (PhysicalRemoval.model i F χ 1 C B S e).energy m)) ∧
          PhysicalRemoval.number F χ 1 C B S e m < ⊤) ∧
      (∀ m : PhysicalRemoval.mixedState F χ 1 C B S e (N := N),
        ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
          DFT.search (PhysicalRemoval.model i F χ 1 C B S e)
            ((PhysicalRemoval.model i F χ 1 C B S e).density m) →
        PhysicalRemoval.number F χ 1 C B S e m ≤
          ENNReal.ofReal (Cnumber * (1 + (PhysicalRemoval.model i F χ 1 C B S e).energy m))) ∧
      LowerSemicontinuous (DFT.search (PhysicalRemoval.model i F χ 1 C B S e)) ∧
      (∀ d, DFT.search (PhysicalRemoval.model i F χ 1 C B S e) d =
        DFT.lieb (pureModel i F χ C B S e)
          (fun a p => PhysicalPairDuality.pairPotential a p) d) := by
  exact assemble_attainment
    (P := PhysicalPFStates.PureState (PhysicalRemoval.potential N 1) C
      (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e)
    (M := PhysicalRemoval.mixedState F χ 1 C B S e (N := N))
    (D := PhysicalPairSpace.Pair) (V := PhysicalPairDuality.Potential) (Ω := PhotonMode)
    (pureModel i F χ C B S e) (PhysicalRemoval.model i F χ 1 C B S e)
    (PhysicalRemoval.number F χ 1 C B S e (N := N)) photonMeasure
    NormalPhoton.frequency χ.profile
    (PhysicalRemoval.infraredRepair i F χ 1 zero_le_one C B S BF BW e core smooth C₀
      scaled B₀ B₁ basis index he hC₀)
    (fun _ => ENNReal.toReal_nonneg)
    (PhysicalAttainmentCompactness.physical_photonLossInput i F χ Sob BF C B S e Rellich Hardy)
    (PhysicalAttainmentCompactness.physical_boundedConstraintClosure i F χ Sob BF C B S e
      Rellich Hardy)
    (PhysicalPFSeed.mixed N 1 zero_le_one C (full F χ N) (full_measurable F χ N)
      (bound F χ) (full_bound F χ N) B S e)
    (PhysicalPFStates.mixedModel_mixtureClosed i (PhysicalRemoval.potential N 1) C
      (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e)
    (PhysicalPFStates.pureEmbedding i (PhysicalRemoval.potential N 1) C
      (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e)
    (fun a p => PhysicalPairDuality.pairPotential a p)
    (PhysicalPFSpectral.spectralEnsemble i (PhysicalRemoval.potential N 1) C
      (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e)
    (PhysicalPairDuality.physical_fenchelMoreau hLp hFM)

end GptLean.PhysicalAttainment
