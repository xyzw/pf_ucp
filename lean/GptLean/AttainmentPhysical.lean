import GptLean.Theorem48
import GptLean.PhotonLocalizationStateRealization
import GptLean.PhotonLocalizationStateRestriction
import GptLean.RemovalPhysicalConclusion

/-!
Attainment on the finite-energy part of the physical ambient state set.

This is an integration endpoint. It consumes the optimized exact-removal
conclusion, so a common-model application must supply that conclusion
from `lattice_physical_removal_optimized`, including the fermionic fixed
point and the same density, current, energy and photon moments. The
localization estimates must likewise come from the same Fock channel.
Neither obligation is reclassified as universal background here.

The endpoint removes the old requirement to pass a `LocalizedOutput`
again after optimization. It also constructs the state realization,
rather than assuming realization of a finite-energy trace-norm limit.
-/

namespace GptLean.InfraredRepair

open MeasureTheory
open scoped ENNReal

variable {State Pair Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} {ω : Ω → ℝ} {w : Ω → ℝ≥0∞}

/-- The already optimized physical removal output supplies the complete
infrared repair interface. The common cutoff and constants are chosen
from the actual infrared profile inside the proof. -/
theorem exists_data_of_optimized
    {A : DFT.StateModel State Pair} {number : State → ℝ≥0∞}
    (P : InfraredMoments A number μ ω w)
    {C e : ℝ} (hC : 0 ≤ C) (he : 0 ≤ e)
    (hremoval : ∀ s κ, 0 < κ → κ ≤ 1 → ∃ r,
      A.density r = A.density s ∧
      A.energy r ≤ A.energy s - P.softEnergy s κ +
        C * SoftPurification.removalError e κ
          (Real.sqrt (CutoffProfile.asq μ ω w κ))
          (Real.sqrt (CutoffProfile.bsq μ ω w κ)) (P.softEnergy s κ) ∧
      number r ≤ ENNReal.ofReal (P.hardNumber s κ)) :
    Nonempty (AttainmentConstruction.InfraredRepairData A number μ ω w) := by
  obtain ⟨κ₀, G, hκ₀, hκ₀1, hG, hgain⟩ := exists_profile_gain
    P.dispersion_measurable P.dispersion_positive P.weighted_finite hC he
  refine ⟨{
    κ₀ := κ₀
    C := G
    κ₀_pos := hκ₀
    C_nonneg := hG
    dispersion_measurable := P.dispersion_measurable
    dispersion_positive := P.dispersion_positive
    cutoff_measurable := P.cutoff_measurable
    cutoff_finite := P.cutoff_finite
    weighted_finite := P.weighted_finite
    photonDensity := P.photonDensity
    hardNumber := P.hardNumber
    softEnergy := P.softEnergy
    radiationEnergy := P.radiationEnergy
    moments := P.moments
    radiation_le := P.radiation_le
    number_eq := P.number_eq
    repair := ?_ }⟩
  intro s κ hκ hκK
  obtain ⟨r, hpair, henergy, hnumber⟩ := hremoval s κ hκ (hκK.trans hκ₀1)
  have hs : 0 ≤ P.softEnergy s κ := by
    rw [(P.moments s).Esoft_eq]
    exact ENNReal.toReal_nonneg
  exact ⟨r, hpair, hgain κ (A.energy s) (A.energy r) (P.softEnergy s κ)
    hκ hκK hs henergy, hnumber⟩

end GptLean.InfraredRepair

namespace GptLean.RemovalConstraints

open MeasureTheory
open scoped ENNReal

variable {X T DensityTest CurrentTest Particle Direction Pair Marginal Ω : Type*}
  [MeasurableSpace X] [MeasurableSpace Ω] {ν : Measure X} {μ : Measure Ω}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {Tr : RemovalState.PositiveTraceData T} {E : RemovalState.PositiveForm Tr}
  [Fintype Particle] [Fintype Direction]
  {density : DensityTest → T →L[ℝ] ℝ}
  {current : CurrentTest → RemovalState.FormObservable E}
  {ω : Ω → ℝ} {w : Ω → ℝ≥0∞}

omit [CompleteSpace T] in
/-- Direct bridge from the physical optimized-removal conclusion to the
infrared repair data. The state model and photon moments must use the
same normal operators as the physical pair. Density and current
identification and the vacuum/hard-marginal number identity are stated
separately from the already proved removal estimate. -/
theorem PhysicalPairData.infraredRepair_of_optimized
    (P : PhysicalPairData density current ν Particle Direction)
    (A : DFT.StateModel E.State Pair) (number : E.State → ℝ≥0∞)
    (moments : InfraredRepair.InfraredMoments A number μ ω w)
    (henergy : ∀ s, A.energy s = (E.expectation s.val).toReal)
    (hpair : ∀ s r, P.rho r =ᵐ[ν] P.rho s →
      P.currentDensity r =ᵐ[ν] P.currentDensity s → A.density r = A.density s)
    (marginal : ℝ → E.State → Marginal) (target : E.State → ℝ → Marginal)
    (soft : ℝ → RemovalState.PositiveForm Tr)
    (hmarginal : ∀ s κ r, 0 < κ → marginal κ r = target s κ →
      (soft κ).expectation r.val = 0 →
      number r ≤ ENNReal.ofReal (moments.hardNumber s κ))
    {C e : ℝ} (hC : 0 ≤ C) (he : 0 ≤ e)
    (hremoval : ∀ s κ, 0 < κ → κ ≤ 1 → ∃ r,
      PhysicalRemovalConclusion P s r (marginal κ) (target s κ) (soft κ)
        (moments.softEnergy s κ)
        (C * SoftPurification.removalError e κ
          (Real.sqrt (CutoffProfile.asq μ ω w κ))
          (Real.sqrt (CutoffProfile.bsq μ ω w κ)) (moments.softEnergy s κ))) :
    Nonempty (AttainmentConstruction.InfraredRepairData A number μ ω w) := by
  apply InfraredRepair.exists_data_of_optimized moments hC he
  intro s κ hκ hκ1
  obtain ⟨r, hr⟩ := hremoval s κ hκ hκ1
  refine ⟨r, hpair s r hr.density_eq hr.current_eq, ?_,
    hmarginal s κ r hκ hr.marginal_eq hr.soft_zero⟩
  simpa only [henergy] using hr.energy_bound

end GptLean.RemovalConstraints

namespace GptLean.AttainmentPhysical

open MeasureTheory Filter Topology
open scoped ENNReal

variable {X Test Pair Pure Potential Ω Ωdensity : Type*}
  [NormedAddCommGroup X] [CompleteSpace X]
  [NormedAddCommGroup Pair] [NormedSpace ℝ Pair]
  [MeasurableSpace Ω] [MeasurableSpace Ωdensity]

/-- All attainment conclusions on the actual finite-energy ambient
states, including any closed invariant sector imposed on `D.states`.

The two article-specific inputs remain visibly named. `J` must be the
proved localization estimates of the same channel, and `hremoval` must
be the optimized removal theorem for those states. The theorem assumes
no independent trace-to-state realization or closure statement. -/
theorem all_conclusions_of_optimized_removal
    (D : PhotonLoss.LocalizationData X) (T : PhotonLoss.TraceData D Test)
    (J : PhotonLoss.LocalizationEstimates D T)
    (pair : PhotonLoss.FiniteEnergyState D T → Pair)
    (pairTest : Test → Pair → ℝ)
    (hcontinuous : ∀ t, Continuous (pairTest t))
    (hseparates : ∀ d d', (∀ t, pairTest t d = pairTest t d') → d = d')
    (htest : ∀ t s, T.test t s.val = pairTest t (pair s))
    (μdensity : Measure Ωdensity)
    (density : X → Lp ℝ 1 μdensity)
    (densityComponent : Pair → Lp ℝ 1 μdensity)
    (hcomponent : Continuous densityComponent)
    (hdensity : ∀ s, density s.val = densityComponent (pair s))
    (htight : J.electronicTight = fun u =>
      ∃ ρ, Tendsto (fun n => density (u n)) atTop (𝓝 ρ))
    (μ : Measure Ω) [SFinite μ] (ω : Ω → ℝ) (w : Ω → ℝ≥0∞)
    (moments : InfraredRepair.InfraredMoments (PhotonLoss.finiteEnergyModel D T pair)
      (fun s => T.number s.val) μ ω w)
    {C e : ℝ} (hC : 0 ≤ C) (he : 0 ≤ e)
    (hremoval : ∀ (s : PhotonLoss.FiniteEnergyState D T) κ,
      0 < κ → κ ≤ 1 → ∃ r : PhotonLoss.FiniteEnergyState D T,
        pair r = pair s ∧
        (T.energy r.val).toReal ≤ (T.energy s.val).toReal - moments.softEnergy s κ +
          C * SoftPurification.removalError e κ
            (Real.sqrt (CutoffProfile.asq μ ω w κ))
            (Real.sqrt (CutoffProfile.bsq μ ω w κ)) (moments.softEnergy s κ) ∧
        T.number r.val ≤ ENNReal.ofReal (moments.hardNumber s κ))
    (A : DFT.StateModel Pure Pair)
    (m₀ : PhotonLoss.FiniteEnergyState D T)
    (hmix : DFT.MixtureClosed (PhotonLoss.finiteEnergyModel D T pair))
    (emb : DFT.PureEmbedding A (PhotonLoss.finiteEnergyModel D T pair))
    (duality : Potential → Pair → ℝ)
    (spectral : ∀ m v, Nonempty (Theorem48.SpectralEnsemble A
      (PhotonLoss.finiteEnergyModel D T pair) duality m v))
    (fm : DFT.FenchelMoreau duality) :
    ∃ Cnumber : ℝ, 0 ≤ Cnumber ∧
      (∀ d, DFT.search (PhotonLoss.finiteEnergyModel D T pair) d < ⊤ → ∃ m,
        pair m = d ∧
        ((T.energy m.val).toReal : EReal) =
          DFT.search (PhotonLoss.finiteEnergyModel D T pair) d ∧
        T.number m.val ≤ ENNReal.ofReal (Cnumber * (1 + (T.energy m.val).toReal)) ∧
        T.number m.val < ⊤) ∧
      (∀ m, ((T.energy m.val).toReal : EReal) =
          DFT.search (PhotonLoss.finiteEnergyModel D T pair) (pair m) →
        T.number m.val ≤ ENNReal.ofReal (Cnumber * (1 + (T.energy m.val).toReal))) ∧
      LowerSemicontinuous (DFT.search (PhotonLoss.finiteEnergyModel D T pair)) ∧
      (∀ d, DFT.search (PhotonLoss.finiteEnergyModel D T pair) d = DFT.lieb A duality d) := by
  obtain ⟨I⟩ := InfraredRepair.exists_data_of_optimized moments hC he hremoval
  let realization := PhotonLoss.ConstraintRealization.ofFiniteEnergyStates D T J pair
    pairTest hcontinuous hseparates htest density densityComponent hcomponent hdensity htight
  exact ⟨I.numberConstant, I.numberConstant_nonneg,
    Theorem48.all_conclusions A (PhotonLoss.finiteEnergyModel D T pair)
      (fun s => T.number s.val) μ ω w I D T J realization m₀ hmix emb duality spectral fm⟩

end GptLean.AttainmentPhysical
