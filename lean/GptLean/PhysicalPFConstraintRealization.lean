import GptLean.PhysicalPFCompactness

/-!
The constraint realization for the actual finite-energy fermionic states.
The represented trace, physical pair, photon number and PF energy are the
same objects used by the constructed localization channel. Convergence of
the density component supplies electronic tightness through the proved
physical density identity. No physical tightness or precompactness conclusion
is an input.
-/

noncomputable section

namespace GptLean.PhysicalPFLocalization

open MeasureTheory Filter Topology PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalPFSource PhysicalPFStates PhysicalPairSpace
  PhysicalSobolevRealization PhysicalPhotonLocalizedNumber PhotonLocalizationPhysicalKernels
open PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option maxHeartbeats 400000

variable {N : ℕ} (i : Fin N)
  (F : FormFactors photonMeasure (Fin 3)) (hF : F.momentum = Prod.fst)
  (Sob : StandardHomogeneousSobolev)
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

/-- The existing physical mixed states at the model form-factor kernel. -/
abbrev modelMixedState :=
  MixedState (PhysicalCovariantKinetic.potential N) C (modelKernel F hF (N := N))
    (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
    (modelKernel_bound F hF (N := N)) B S e

/-- The actual constrained-search model on these states. -/
abbrev modelMixedModel :=
  mixedModel i (PhysicalCovariantKinetic.potential N) C (modelKernel F hF (N := N))
    (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
    (modelKernel_bound F hF (N := N)) B S e

/-- Photon number is the full physical number form on the represented trace. -/
def modelNumber (s : modelMixedState F hF C B S e (N := N)) : ℝ≥0∞ :=
  (fullNumberForm B N).expectation s.val.val

/-- Every constraint-realization field is derived on the same physical model. -/
def constraintRealization
    (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
    (Hardy : StandardFractionalHardy) :
    PhotonLoss.ConstraintRealization
      (localizationEstimates i F hF Sob BF C B S e Rellich Hardy)
      (modelMixedModel i F hF C B S e) (modelNumber F hF C B S e (N := N)) where
  repr s := s.val.val
  repr_mem s := ⟨s.val.property.1, s.val.property.2.1, s.property⟩
  energy_nonneg _ := ENNReal.toReal_nonneg
  energy_repr s := by
    exact (traceData_energy_match i BF C B S (modelKernel F hF (N := N))
      (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
      (modelKernel_bound F hF (N := N)) e s.val.property.1).trans
        (ENNReal.ofReal_toReal s.val.property.2.2.ne).symm
  number_repr _ := rfl
  realize x hx he := by
    have hphysical : (normalEnergy (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
        C (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
        (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) B S e).expectation x < ⊤ := by
      exact (traceData_energy_match i BF C B S (modelKernel F hF (N := N))
        (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
        (modelKernel_bound F hF (N := N)) e hx.1).symm.trans_lt he
    exact ⟨⟨⟨x, hx.1, hx.2.1, hphysical⟩, hx.2.2⟩, rfl⟩
  pairTest t := smoothPairTest t
  pairTest_cont t := (smoothPairTest t).continuous
  pairTest_separates := smoothPairTest_separates
  test_repr t s := normalTest_statePair i (PhysicalCovariantKinetic.potential N) C
    (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
    (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) B S e t s.val
  tight_of_converges s _ hs :=
    coarseData_electronicTight_of_pair_tendsto i F hF Sob BF C B S e Rellich Hardy s hs

include Sob BF in
/-- Bounded-energy, bounded-number closure for converging physical pairs. -/
theorem physical_boundedConstraintClosure
    (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
    (Hardy : StandardFractionalHardy) :
    Closure.BoundedConstraintClosure (modelMixedModel i F hF C B S e)
      (modelNumber F hF C B S e (N := N)) :=
  (constraintRealization i F hF Sob BF C B S e Rellich Hardy).boundedConstraintClosure

include Sob BF in
/-- Fixed-pair photon-loss compactness with the original mean-number cap. -/
theorem physical_photonLossInput
    (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
    (Hardy : StandardFractionalHardy) (p : PhysicalPairSpace.Pair) :
    Attainment.PhotonLossInput (modelMixedState F hF C B S e (N := N))
      (fun s => (modelMixedModel i F hF C B S e).density s = p)
      (modelMixedModel i F hF C B S e).energy (modelNumber F hF C B S e (N := N)) :=
  (constraintRealization i F hF Sob BF C B S e Rellich Hardy).photonLossInput p

end GptLean.PhysicalPFLocalization
