import GptLean.PhysicalRemovalInput
import GptLean.PhysicalPFRadiation

/-!
Infrared removal on the actual fermionic Pauli--Fierz normal states.
The output preserves the physical density-current pair and has the actual
hard-channel photon marginal, zero soft energy and exactly the original
hard photon number. It satisfies the optimized energy estimate. Only
universal analytic backgrounds remain as theorem parameters.
-/

noncomputable section
namespace GptLean.PhysicalRemoval

open MeasureTheory Filter PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalGaussianCoordinates PhysicalPolarization
  PhysicalPFSource PhysicalPFStates PhysicalRemovalKernels PhysicalRemovalMarginal
  PhysicalPhotonMarginal PhysicalPairSpace PhysicalNormalStates
  Gaussian SymmetricLift RemovalEnergy
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] PhysicalPolarization.softPhotonHardNormedAddCommGroup
  PhysicalPolarization.softPhotonHardRealNormedSpace

variable {N : ℕ} (i : Fin N) (F : Frame) (χ : ArticleCutoff)
  (c : ℝ) (hc : 0 ≤ c) (C : CanonicalSectorCCR photonMeasure)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)
  (BF : StandardSymmetricFockExponential) (BW : StandardWienerSegal) (e : ℝ)

abbrev mixedState := PhysicalPFStates.MixedState (potential N c) C (full F χ N)
  (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e

abbrev physicalPair := PhysicalPFStates.mixedPair i (potential N c) C (full F χ N)
  (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e

abbrev model := PhysicalPFStates.mixedModel i (potential N c) C (full F χ N)
  (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e

def number (s : mixedState F χ c C B S e (N := N)) : ℝ≥0∞ :=
  (NormalPhoton.numberForm B.normal (B.realization PhotonFock).functional).expectation
    (marginal B (volume : Measure (Configuration N)) s.val.val)

def softEnergy (s : mixedState F χ c C B S e (N := N)) (κ : ℝ) : ℝ≥0∞ :=
  (NormalPhoton.softEnergyForm B.normal (B.realization PhotonFock).functional κ).expectation
    (marginal B (volume : Measure (Configuration N)) s.val.val)

def hardNumber (s : mixedState F χ c C B S e (N := N)) (κ : ℝ) : ℝ≥0∞ :=
  (NormalPhoton.hardNumberForm B.normal (B.realization PhotonFock).functional κ).expectation
    (marginal B (volume : Measure (Configuration N)) s.val.val)

def moments : InfraredRepair.InfraredMoments (model i F χ c C B S e)
    (number F χ c C B S e) photonMeasure NormalPhoton.frequency χ.profile :=
  PhysicalPFRadiation.infraredMoments (Fin N × Fin 3) (potential N c) C
    (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e
    (PhysicalElectronicFermions.projection N PhotonFock) (physicalPair i F χ c C B S e)
    χ.profile χ.profile_measurable χ.profile_total_lt_top χ.profile_inversefrequency_lt_top

variable (core : CountableSpatialTestCore) (smooth : SmoothSobolevBackground)
  (C₀ : ℝ) (scaled : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C₀)
  (B₀ : TensorBackground Repair.SixTag) (B₁ : TensorMultilinearData B₀)
  {ι : Type*} (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target) (index : ι ↪ ℕ)

include hc BF BW core smooth scaled B₀ B₁ basis index in
set_option backward.isDefEq.respectTransparency.types true in
set_option diagnostics true in
set_option maxHeartbeats 800000 in
/-- One output satisfies all physical constraints and the optimized estimate. -/
theorem optimized (he : 0 ≤ e) (hC₀ : 0 ≤ C₀)
    (s : mixedState F χ c C B S e (N := N)) (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ r : mixedState F χ c C B S e (N := N),
      physicalPair i F χ c C B S e r = physicalPair i F χ c C B S e s ∧
      (model i F χ c C B S e).energy r ≤ (model i F χ c C B S e).energy s -
        (softEnergy F χ c C B S e s κ).toReal +
        (3 * latticeRemovalConstant N C₀) * SoftPurification.removalError e κ
          (χ.removalA κ) (χ.removalB κ) (softEnergy F χ c C B S e s κ).toReal ∧
      number F χ c C B S e r = hardNumber F χ c C B S e s κ ∧
      softEnergy F χ c C B S e r κ = 0 ∧
      marginal B (volume : Measure (Configuration N)) r.val.val =
        hardTargetTrace BF κ B volume s.val.val ∧
      number F χ c C B S e r ≤ ENNReal.ofReal (1 / κ) *
        (NormalPhoton.radiationForm B.normal (B.realization PhotonFock).functional).expectation
          (marginal B (volume : Measure (Configuration N)) s.val.val) := by
  let W := F.scalarRealization κ BW
  have hs : s.val.val ∈ B.fermionicStates N :=
    ⟨s.val.property.1, s.val.property.2.1, s.property⟩
  have hsource : ∃ source : Source (Fin N × Fin 3) (potential N c) B s.val.val, ∀ n,
      Repair.HasElectronicCharacter (fun π => permuteConfiguration π)
        (PhysicalElectronicFermions.signCharacter N)
        (inclusion (Fin N × Fin 3) (potential N c) (source.vector n)) :=
    fermionic_source_exists N (potential N c) C
      (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e
      (x := s.val.val) hs s.val.property.2.2
  obtain ⟨source, hcharacter⟩ := hsource
  let L := latticeInput i F χ c hc C B S BF e κ hκ.le W core smooth C₀ scaled B₀ B₁
    basis index s.val source hcharacter
  have hremoval := AttainmentPhysicalRemoval.LatticeRemovalInput.optimized
    (Q := W.space.Q) (Ω := PhotonMode) (G := DerivativeLabel)
    (Ho := PhotonFock) (H := HardPhotonFock κ)
    (Hr := WithLp 2 (PhotonFock × PhotonFock))
    (F := WithLp 2 (HardPhotonFock κ × HardPhotonFock κ))
    (T := B.Trace (Lp (HardPhotonFock κ) 2 (volume : Measure (Configuration N))))
    (Hfull := WaveSpace (Fin N × Fin 3))
    (Tfull := B.Trace (WaveSpace (Fin N × Fin 3)))
    (Marginal := PhysicalRemovalMarginal.Marginal)
    (HardMarginal := PhysicalRemovalMarginal.Marginal)
    (DensityTest := SpatialTest) (CurrentTest := Fin 3 × SpatialTest) (ι := ι)
    (Qv := W.space.Q) (Hv := PhotonFock) (Kv := HardPhotonFock κ) (Gv := DerivativeLabel)
    (μ := W.space.measure) (ν := photonMeasure) (μv := W.space.measure)
    (X := FieldSpace) (ρMeasure := (volume : Measure FieldSpace)) (N := N)
    (Trfull := B.traceData (H := WaveSpace (Fin N × Fin 3)))
    (Efull := fullEnergy F χ c C B S e) (m := s.val)
    (compression := B.fermionicCompression N)
    (k := κ) (e := e) (C := C₀) (acut := χ.removalA κ) (bcut := χ.removalB κ)
    L he hC₀ hκ hκ1
  obtain ⟨r, hr, hfixed⟩ := hremoval
  let output : mixedState F χ c C B S e (N := N) := ⟨r, hfixed⟩
  have hn : number F χ c C B S e output = hardNumber F χ c C B S e s κ :=
    number_eq_of_gaussianHardTarget (X := Configuration N) B volume BF C κ
      (x := s.val.val) (y := r.val) s.val.property.1 r.property.1 hr.marginal_eq
  refine ⟨output, ?_, hr.energy_bound, hn, hr.soft_zero, ?_, ?_⟩
  · exact pair_ext_ae hr.density_eq hr.current_eq
  · exact photonCoordinates_positive_injective B
      (x := marginal B (volume : Measure (Configuration N)) r.val)
      (y := hardTargetTrace BF κ B volume s.val.val)
      (marginal_positive B volume (x := r.val) r.property.1)
      (hardTargetTrace_positive BF κ B volume (x := s.val.val) s.val.property.1)
      hr.marginal_eq
  · exact hn.le.trans (hardNumber_le_radiation B κ hκ
      (x := marginal B (volume : Measure (Configuration N)) s.val.val)
      (marginal_positive B volume (x := s.val.val) s.val.property.1))

include hc BF BW core smooth scaled B₀ B₁ basis index in
set_option backward.isDefEq.respectTransparency.types true in
set_option diagnostics true in
/-- The attainment infrared-repair interface is derived from the physical
construction for every positive cutoff. Gaussian probability spaces and
hard Fock fibers may depend on that cutoff. -/
theorem infraredRepair (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) :
    Nonempty (AttainmentConstruction.InfraredRepairData (model i F χ c C B S e)
      (number F χ c C B S e) photonMeasure NormalPhoton.frequency χ.profile) := by
  apply InfraredRepair.exists_data_of_optimized (moments i F χ c C B S e)
    (show 0 ≤ 3 * latticeRemovalConstant N C₀ from
      mul_nonneg (by norm_num) (latticeRemovalConstant_nonneg N C₀)) he
  intro s κ hκ hκ1
  obtain ⟨r, hp, he', hn, _⟩ := optimized i F χ c hc C B S BF BW e core smooth C₀ scaled B₀ B₁
    basis index he hC₀ s κ hκ hκ1
  refine ⟨r, hp, he', ?_⟩
  have hmoment := NormalPhoton.density_hardNumber B.normal
    (B.realization PhotonFock).functional κ (marginal B volume s.val.val)
    (marginal_positive B volume s.val.property.1)
  exact hn.le.trans ((hmoment.trans
    ((moments i F χ c C B S e).ofReal_hardNumber_eq s hκ).symm).le)

end GptLean.PhysicalRemoval
