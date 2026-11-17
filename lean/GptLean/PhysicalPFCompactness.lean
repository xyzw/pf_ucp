import GptLean.PhysicalGraphChannel
import GptLean.PhysicalLocalCompactness
import GptLean.PhysicalPFLocalizationCommon

/-!
Coarse localization data for the actual physical model. Local compactness
uses the constructed supported free graph and its finite-rank projections.
The original electronic density supplies tightness, while fractional Hardy
supplies finite localized photon number from radiation energy. No original
photon-number bound or physical precompactness statement is assumed.
-/

noncomputable section
namespace GptLean.PhysicalPFLocalization

open MeasureTheory Filter Topology PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhotonLocalization PhotonLocalizationPhysicalKernels
  PhotonLocalizationKernelCutoffs PhysicalSobolevRealization
  PhysicalSobolevRealization.StandardHomogeneousSobolev
  PhysicalPhotonLocalizedNumber
open PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option maxHeartbeats 200000

private theorem normalized_two_bounds {a b c : ℝ≥0∞} {A B E t : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hab : a ≤ ENNReal.ofReal A * b)
    (hbc : b ≤ ENNReal.ofReal B * (c + ENNReal.ofReal t))
    (ht : t = 1) (hc : c ≤ ENNReal.ofReal E) :
    a ≤ ENNReal.ofReal (A * B * (max E 0 + 1)) := by
  apply (hab.trans (mul_le_mul_right hbc _)).trans
  rw [ht, ENNReal.ofReal_mul (mul_nonneg hA hB), ENNReal.ofReal_mul hA,
    mul_assoc, ENNReal.ofReal_add (le_max_right E 0) zero_le_one]
  exact mul_le_mul_right (mul_le_mul_right
    (add_le_add (hc.trans (ENNReal.ofReal_le_ofReal (le_max_left E 0))) le_rfl) _) _

private theorem scaled_energy_bound {a b c : ℝ≥0∞} {A E : ℝ}
    (hA : 0 ≤ A) (hab : a ≤ ENNReal.ofReal A * b)
    (hbc : b ≤ c) (hc : c ≤ ENNReal.ofReal E) :
    a ≤ ENNReal.ofReal (A * max E 0) := by
  apply (hab.trans (mul_le_mul_right
    ((hbc.trans hc).trans (ENNReal.ofReal_le_ofReal (le_max_left E 0))) _)).trans_eq
  exact (ENNReal.ofReal_mul hA).symm

variable {N : ℕ} (i : Fin N)
  (F : FormFactors photonMeasure (Fin 3)) (hF : F.momentum = Prod.fst)
  (Sob : StandardHomogeneousSobolev)
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

def compactnessFreeBound (E : ℝ) : ℝ :=
  radiationMultiplierConstant Sob.background *
    PhysicalPFComparison.forwardConstant N 1 C (modelKernel F hF (N := N))
      (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
      (modelKernel_bound F hF (N := N)) e * (max E 0 + 1)

theorem compactnessFreeBound_nonneg (E : ℝ) :
    0 ≤ compactnessFreeBound F hF Sob C e (N := N) E := by
  exact mul_nonneg (mul_nonneg (radiationMultiplierConstant_pos Sob.background).le
    (PhysicalPFComparison.forwardConstant_pos N 1 C (modelKernel F hF (N := N))
      (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
      (modelKernel_bound F hF (N := N)) e).le)
    (add_nonneg (le_max_right E 0) zero_le_one)

theorem localized_free_bound (E : ℝ) (m : ℕ) {x : B.FullTrace N}
    (hx : x ∈ (localizationData BF C B PhysicalOnePhotonFourier.fourier N).states)
    (hE : (modelTraceData i F hF BF C B S e).energy x ≤ ENNReal.ofReal E) :
    (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) B S).expectation
      (B.normal.extend (physicalKraus BF N m) x) ≤
        ENNReal.ofReal (compactnessFreeBound F hF Sob C e (N := N) E) := by
  have hm := traceData_energy_match i BF C B S (modelKernel F hF (N := N))
    (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
    (modelKernel_bound F hF (N := N)) e hx.1
  have ho := free_channel_bound Sob.background identification Sob.fourier_compatibility
    BF C B N S m hx.1
  have hi := PhysicalPFComparison.normal_free_le_pf_add_mass N 1 C
    (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
    (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) B S e hx.1
  exact normalized_two_bounds (radiationMultiplierConstant_pos Sob.background).le
    (PhysicalPFComparison.forwardConstant_pos N 1 C (modelKernel F hF (N := N))
      (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
      (modelKernel_bound F hF (N := N)) e).le ho hi hx.2.1 (hm.symm.le.trans hE)

theorem localized_number_bound (Hardy : StandardFractionalHardy)
    (E : ℝ) (m : ℕ) {x : B.FullTrace N}
    (hx : x ∈ (localizationData BF C B PhysicalOnePhotonFourier.fourier N).states)
    (hE : (modelTraceData i F hF BF C B S e).energy x ≤ ENNReal.ofReal E) :
    (fullNumberForm B N).expectation (B.normal.extend (physicalKraus BF N m) x) ≤
      ENNReal.ofReal (numberConstant Hardy m * max E 0) := by
  have hm := traceData_energy_match i BF C B S (modelKernel F hF (N := N))
    (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
    (modelKernel_bound F hF (N := N)) e hx.1
  have hn := localized_number_le Hardy BF C B N m hx.1
  have hr := PhysicalPFRadiation.normalRadiation_le (Fin N × Fin 3)
    (PhysicalCovariantKinetic.potential N) C (modelKernel F hF (N := N))
    (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
    (modelKernel_bound F hF (N := N)) B S e hx.1
  exact scaled_energy_bound (numberConstant_pos Hardy m).le hn hr (hm.symm.le.trans hE)

def compactnessRoughBound (E : ℝ) : ℝ :=
  roughConstant Sob.background C N (modelKernel F hF (N := N))
    (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
    (modelKernel_bound F hF (N := N)) e * (max E 0 + 1)

theorem localized_rough_bound (E : ℝ) (m : ℕ) {x : B.FullTrace N}
    (hx : x ∈ (localizationData BF C B PhysicalOnePhotonFourier.fourier N).states)
    (hE : (modelTraceData i F hF BF C B S e).energy x ≤ ENNReal.ofReal E) :
    (modelTraceData i F hF BF C B S e).energy
      ((localizationData BF C B PhysicalOnePhotonFourier.fourier N).localize m x) ≤
        ENNReal.ofReal (compactnessRoughBound F hF Sob C e (N := N) E) := by
  have hi := traceData_energy_match i BF C B S (modelKernel F hF (N := N))
    (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
    (modelKernel_bound F hF (N := N)) e hx.1
  have ho := traceData_energy_match i BF C B S (modelKernel F hF (N := N))
    (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
    (modelKernel_bound F hF (N := N)) e
    (B.normal.positive (physicalKraus BF N m) hx.1)
  exact ho.le.trans (normalized_energy_bound Sob.background identification
    Sob.fourier_compatibility BF C B N S (modelKernel F hF (N := N))
    (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
    (modelKernel_bound F hF (N := N)) e m hx.1 hx.2.1 E (hi.symm.le.trans hE))

include Sob in
/-- Trace-norm local precompactness on the actual common physical channel. -/
theorem physical_localized_totallyBounded
    (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
    (Hardy : StandardFractionalHardy)
    (x : ℕ → B.FullTrace N) (E : ℝ)
    (hx : ∀ n, x n ∈ (localizationData BF C B PhysicalOnePhotonFourier.fourier N).states)
    (hE : ∀ n, (modelTraceData i F hF BF C B S e).energy (x n) ≤ ENNReal.ofReal E)
    {ρ : Lp ℝ 1 (volume : Measure ElectronicPosition)}
    (hρ : Tendsto (fun n => PhysicalPFCompactnessDensity.density B N (x n)) atTop (𝓝 ρ))
    (m : ℕ) :
    TotallyBounded (Set.range fun n =>
      (localizationData BF C B PhysicalOnePhotonFourier.fourier N).localize m (x n)) := by
  apply PhysicalGraphCompactness.channelSources_totallyBounded BF B S N m
    (fun L M => PhysicalLocalCompactness.supportValue_totallyBounded Rellich N
      (radius m) L M (radius_pos m).le) x
    (fun n => ⟨(hx n).1, (hx n).2.1⟩)
    (compactnessFreeBound_nonneg F hF Sob C e (N := N) E)
    (mul_nonneg (numberConstant_pos Hardy m).le (le_max_right E 0))
    (fun n => localized_free_bound i F hF Sob BF C B S e E m (hx n) (hE n))
    (fun n => localized_number_bound i F hF BF C B S e Hardy E m (hx n) (hE n)) hρ

/-- The compactness and rough fields are both constructed on the item-one model. -/
def coarseData (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
    (Hardy : StandardFractionalHardy) : CoarseData
      (localizationData BF C B PhysicalOnePhotonFourier.fourier N)
      (modelTraceData i F hF BF C B S e) where
  electronicTight x := ∃ ρ, Tendsto
    (fun n => PhysicalPFCompactnessDensity.density B N (x n)) atTop (𝓝 ρ)
  precompact x E hx hE htight m := by
    obtain ⟨ρ, hρ⟩ := htight
    exact physical_localized_totallyBounded i F hF Sob BF C B S e
      Rellich Hardy x E hx hE hρ m
  rough := compactnessRoughBound F hF Sob C e (N := N)
  rough_bound E m x hx hE := localized_rough_bound i F hF Sob BF C B S e E m hx hE

@[simp] theorem coarseData_electronicTight
    (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
    (Hardy : StandardFractionalHardy) (x : ℕ → B.FullTrace N) :
    (coarseData i F hF Sob BF C B S e Rellich Hardy).electronicTight x ↔
      ∃ ρ, Tendsto (fun n => PhysicalPFCompactnessDensity.density B N (x n)) atTop (𝓝 ρ) :=
  Iff.rfl

/-- Convergence of the actual finite-energy fermionic pairs supplies the
electronic tightness used by the coarse localization data. -/
theorem coarseData_electronicTight_of_pair_tendsto
    (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
    (Hardy : StandardFractionalHardy)
    (x : ℕ → PhysicalPFStates.MixedState (PhysicalCovariantKinetic.potential N) C
      (modelKernel F hF (N := N)) (modelKernel_measurable F hF (N := N))
      (modelKernelBound F hF) (modelKernel_bound F hF (N := N)) B S e)
    {p : PhysicalPairSpace.Pair}
    (hp : Tendsto (fun n => PhysicalPFStates.mixedPair i
      (PhysicalCovariantKinetic.potential N) C (modelKernel F hF (N := N))
      (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
      (modelKernel_bound F hF (N := N)) B S e (x n)) atTop (𝓝 p)) :
    (coarseData i F hF Sob BF C B S e Rellich Hardy).electronicTight
      (fun n => (x n).val.val) := by
  apply (coarseData_electronicTight i F hF Sob BF C B S e Rellich Hardy _).mpr
  refine ⟨PhysicalPairSpace.densityL1 p, ?_⟩
  exact PhysicalPFCompactnessDensity.density_tendsto_of_pair_tendsto B i
    (PhysicalCovariantKinetic.potential N) C (modelKernel F hF (N := N))
    (modelKernel_measurable F hF (N := N)) (modelKernelBound F hF)
    (modelKernel_bound F hF (N := N)) S e (fun n => (x n).val.val)
    (fun n => (x n).val.property.1) (fun n => (x n).val.property.2.2)
    (fun n => (x n).property) hp

/-- The complete localization-estimate interface on the same physical model. -/
def localizationEstimates
    (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
    (Hardy : StandardFractionalHardy) : PhotonLoss.LocalizationEstimates
      (localizationData BF C B PhysicalOnePhotonFourier.fourier N)
      (modelTraceData i F hF BF C B S e) :=
  localizationEstimates_of_commonChannel
    (coarseData i F hF Sob BF C B S e Rellich Hardy)
    (commonEnergy i F hF Sob BF C B S e)
    (commonCurrent i F hF Sob BF C B S e)

end GptLean.PhysicalPFLocalization
