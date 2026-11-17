import GptLean.PhysicalPFTraceData
import GptLean.PhysicalPFLocalizationForms
import GptLean.PhysicalPFLocalizationSelectedSource
import GptLean.PhysicalPFLocalizationCurrentSource
import GptLean.PhysicalSobolevRealization

/-!
Actual common energy and current localization data. The photon channel,
form-factor kernels, homogeneous Sobolev realization, electronic cutoff,
kinetic source and current source all use the same physical model.
There are no support or localization-estimate hypotheses.
-/

noncomputable section
namespace GptLean.PhysicalPFLocalization

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalPFSource PhysicalPFStates
  PhysicalPairSpace PhysicalNormalTrace PhysicalClosedForms PhotonLocalization
  PhotonLocalizationFockChannel PhotonLocalizationChannel PhotonLocalizationKernelCutoffs
  PhotonLocalizationPhysicalKernels PhysicalSobolevRealization
  PhysicalSobolevRealization.StandardHomogeneousSobolev
open PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
set_option Elab.async false

variable {N : ℕ} (i : Fin N)
  (F : FormFactors photonMeasure (Fin 3)) (hF : F.momentum = Prod.fst)
  (Sob : StandardHomogeneousSobolev)
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

abbrev modelKernel := PhysicalProfiles.particleKernel F hF identification N
abbrev modelKernel_measurable := PhysicalProfiles.particleKernel_measurable F hF identification N
abbrev modelKernelBound := PhysicalProfiles.kernelBound F hF identification
abbrev modelKernel_bound := PhysicalProfiles.particleKernel_bound F hF identification N

abbrev modelTraceData := traceData i BF C B S (modelKernel F hF (N := N))
  (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) e

/-- The physical common energy data are constructed from the standard
backgrounds and actual form factors. -/
def commonEnergy : CommonChannelEnergyData
    (A := (B.realization (FullHilbert N)).rank) (Tr := B.traceData (H := FullHilbert N))
    (h := PhysicalOnePhotonFourier.PositionSpace) (V := Lp ℂ 2 photonMeasure)
    (Q := OnePhotonFormFamily) (Ω := SymmetricLift.Configuration N) (K := PhotonFock)
    (α := Fin N → Bool) (ι := Fin N × Fin 3)
    (localizationData BF C B PhysicalOnePhotonFourier.fourier N)
    (modelTraceData i F hF BF C B S e) where
  normal := B.normal
  fock := fullFactorization BF PhysicalOnePhotonFourier.fourier N
  forms := fullFormCalculus BF C B PhysicalOnePhotonFourier.fourier N
  split m := complexOnePhotonIsometry (radius m)
  positive := fun _ h => h
  states_positive := fun _ hx => hx.1
  trace_one := fun _ hx => hx.2.1
  channel := fun _ _ _ => rfl
  energy := normalEnergy (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) C
    (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
    (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) B S e
  energy_match := fun _ hx => traceData_energy_match i BF C B S
    (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
    (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) e hx
  electronic := PhysicalPFElectronicCutoff.data N (PhysicalCovariantKinetic.potential N) C
    (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
    (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) B S e
  cutoff_match := fun _ _ _ => rfl
  multiplier_contraction := fun l v => PhysicalElectronicScalars.multiplier_contraction N (H := PhotonFock) l
    (PhysicalElectronicScalars.selected N) v
  cutoff_commute l m v a := (PhysicalNormalCompression.multiplier_kraus (H := PhotonFock)
    (μ := (volume : Measure (SymmetricLift.Configuration N)))
    (PhysicalElectronicScalars.weight N l (PhysicalElectronicScalars.selected N))
    (PhysicalElectronicScalars.differentiable N l (PhysicalElectronicScalars.selected N)).continuous.aestronglyMeasurable
    1 (ae_of_all _ (PhysicalElectronicScalars.abs_le_one N l (PhysicalElectronicScalars.selected N)))
    ((photonFactorization BF).factor (physicalSplit m)) v a).symm
  kinetic := PhysicalPFDecomposition.kinetic N B S C
    (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
    (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) e
  potential := potentialPart N B
  control := physicalControl F hF identification C B S N e
  radiation := PhysicalFock.radiationFamily
  truncation := finiteFamily PhysicalFock.radiationFamily
  radiationFamily := physicalRadiationFamily Sob.background identification
  modes := radiationLocalizationModes physicalRadiationCoordinates
  truncation_value := radiationLocalization_truncation physicalRadiationCoordinates
  radiation_duality m k u hu := radiationLocalization_duality physicalRadiationCoordinates
    Sob.background identification Sob.fourier_compatibility rfl k m u hu
  potential_operator := potentialOperator N
  potential_trace := potential_trace N B
  potential_commute m := potential_commute N BF (complexOnePhotonIsometry (radius m))
  comparison := 1
  comparison_nonneg := zero_le_one
  reference_bound x hx he := by
    apply le_of_eq
    simpa only [one_mul, physicalControl] using (currentControl_expectation (Fin N × Fin 3)
      (PhysicalCovariantKinetic.potential N) C (modelKernel F hF (N := N))
      (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
      (modelKernel_bound F hF (N := N)) B S e hx he)
  kinetic_le_control := fun _ hx => kinetic_le_control C (modelKernelBound F hF) B S e N
    (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
    (modelKernel_bound F hF (N := N)) hx
  potential_le_control := fun b _ hx => potential_le_control N B S C
    (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
    (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) e b hx
  radiation_le_control := fun _ hx => calculus_radiation_le_control N B S BF C
    (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
    (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) e hx
  full_form := fun _ hx he => full_form N B S BF C
    (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
    (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) e hx he
  truncated_form := fun k x _ hk hp hr => truncated_form N B S BF C
    (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
    (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) e k x hk hp hr
  charge := e
  epsilon l m := PhysicalProfiles.cutoffError F identification Sob.background (2 * (l + 1)) m
  epsilon_nonneg l m := PhysicalProfiles.cutoffError_nonneg F identification Sob.background (2 * (l + 1)) m
  epsilon_zero l := PhysicalProfiles.cutoffError_zero F identification Sob.background (2 * (l + 1))
  fieldConstant _ := 3
  derivativeConstant _ := derivativeConstant N
  fieldConstant_nonneg _ := by norm_num
  derivativeConstant_nonneg _ := derivativeConstant_nonneg N
  kinetic_source l m v hv := selectedKineticSource N F hF identification Sob.background
    Sob.fourier_compatibility BF C B S e l m v hv

/-- Actual density/current data on the identical physical channel. -/
def commonCurrent : CommonChannelCurrentData (commonEnergy i F hF Sob BF C B S e) where
  control _ := physicalControl F hF identification C B S N e
  current := testObservable i (PhysicalCovariantKinetic.potential N) C
    (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
    (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) B S e
  approximation := testRelativeApproximation i (PhysicalCovariantKinetic.potential N) C
    (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
    (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) B S e
  test_match := fun t x hx he => (testObservable_value i (PhysicalCovariantKinetic.potential N) C
    (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
    (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) B S e t x hx he).symm
  comparison _ := 1
  comparison_nonneg _ := zero_le_one
  reference_bound _ x hx he := (commonEnergy i F hF Sob BF C B S e).reference_bound x hx he
  testOperator := testOperator i
  test_commute t m q v a := testOperator_commute i
    ((photonFactorization BF).factor (physicalSplit m)) t q v a
  test_adjoint_commute t m q v a := testOperator_adjoint_commute i
    ((photonFactorization BF).factor (physicalSplit m)) t q v a
  weight := testWeightConstant i
  weight_nonneg := testWeightConstant_nonneg i
  epsilon := testEpsilon F identification Sob.background
  epsilon_nonneg := testEpsilon_nonneg F identification Sob.background
  epsilon_zero := testEpsilon_zero F identification Sob.background
  fieldConstant := testFieldConstant
  fieldConstant_nonneg := testFieldConstant_nonneg
  source := test_source_exists i F hF identification Sob.background Sob.fourier_compatibility BF C B S e

end GptLean.PhysicalPFLocalization
