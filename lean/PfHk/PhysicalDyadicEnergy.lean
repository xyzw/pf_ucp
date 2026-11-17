import PfHk.PhysicalFreeCarleman

/-! Actual globally integrable radial energies for annularly supported
vectors in the free Pauli–Fierz operator domain. -/

noncomputable section
namespace PfHk.PhysicalDyadicEnergy

open MeasureTheory Set GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain
  PfHk.CenteredPhysicalReference PfHk.PhysicalCarlemanInput
  PfHk.CarlemanSpatialDensity PfHk.PhysicalFreeCarleman

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

local instance dyadicEnergyPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PfHk.PhysicalFreeCarleman.finalFreeCarlemanRealInner

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFReference.covariant
  PhysicalPFReference.radiation PhysicalPFReference.referenceSubspace FreeGraph

variable {I : Type} [Fintype I] [DecidableEq I]

def centeredAnnulus (O : Position I) (ρ R : ℝ) : Set (Position I) :=
  Metric.closedBall O R \ Metric.ball O ρ

theorem centeredAnnulus_compact (O : Position I) (ρ R : ℝ) :
    IsCompact (centeredAnnulus O ρ R) :=
  (isCompact_closedBall O R).diff Metric.isOpen_ball

theorem centeredAnnulus_dist {O : Position I} {ρ R : ℝ} {X : Position I}
    (hX : X ∈ centeredAnnulus O ρ R) : ρ ≤ dist X O ∧ dist X O ≤ R := by
  simpa only [centeredAnnulus, mem_diff, Metric.mem_closedBall, Metric.mem_ball,
    not_lt, and_comm] using hX

def centeredMassWeight (O : Position I) (τ α : ℝ) (X : Position I) : ℝ :=
  massWeight τ α (X - O)

def centeredKineticWeight (O : Position I) (τ α : ℝ) (X : Position I) : ℝ :=
  kineticWeight τ α (X - O)

def centeredRadiationWeight (O : Position I) (τ α : ℝ) (X : Position I) : ℝ :=
  radiationWeight τ α (X - O)

def centeredSourceWeight (O : Position I) (τ α : ℝ) (X : Position I) : ℝ :=
  sourceWeight τ α (X - O)

theorem centered_weights_continuousOn (O : Position I) (τ α : ℝ)
    {ρ R : ℝ} (hρ : 0 < ρ) (hR : R < 1) :
    ContinuousOn (centeredMassWeight O τ α) (centeredAnnulus O ρ R) ∧
      ContinuousOn (centeredKineticWeight O τ α) (centeredAnnulus O ρ R) ∧
      ContinuousOn (centeredRadiationWeight O τ α) (centeredAnnulus O ρ R) ∧
      ContinuousOn (centeredSourceWeight O τ α) (centeredAnnulus O ρ R) := by
  have h (X : Position I) (hx : X ∈ centeredAnnulus O ρ R) :=
    weights_continuousAt τ α
      (show 0 < ‖X - O‖ by rw [← dist_eq_norm]; exact hρ.trans_le (centeredAnnulus_dist hx).1)
      (show ‖X - O‖ < 1 by rw [← dist_eq_norm]; exact (centeredAnnulus_dist hx).2.trans_lt hR)
  have hc (X : Position I) : ContinuousAt (fun Y : Position I => Y - O) X :=
    continuous_id.continuousAt.sub continuousAt_const
  exact ⟨fun X hx => ((h X hx).1.comp (f := fun Y : Position I => Y - O) (hc X)).continuousWithinAt,
    fun X hx => ((h X hx).2.1.comp (f := fun Y : Position I => Y - O) (hc X)).continuousWithinAt,
    fun X hx => ((h X hx).2.2.1.comp (f := fun Y : Position I => Y - O) (hc X)).continuousWithinAt,
    fun X hx => ((h X hx).2.2.2.comp (f := fun Y : Position I => Y - O) (hc X)).continuousWithinAt⟩

theorem centered_annular_mul_integrable (O : Position I) (ρ R : ℝ)
    (w q : Position I → ℝ) (hw : ContinuousOn w (centeredAnnulus O ρ R))
    (hq : Integrable q) (hs : ∀ᵐ X ∂volume, X ∉ centeredAnnulus O ρ R → q X = 0) :
    Integrable (fun X => w X * q X) := by
  have hA := centeredAnnulus_compact O ρ R
  have hi : IntegrableOn (fun X => w X * q X) (centeredAnnulus O ρ R) :=
    IntegrableOn.continuousOn_mul hw hq.integrableOn hA
  apply ((integrable_indicator_iff hA.measurableSet).mpr hi).congr
  filter_upwards [hs] with X hX
  by_cases hx : X ∈ centeredAnnulus O ρ R
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, hX hx, mul_zero]

theorem centered_weights_nonneg {O : Position I} {τ α ρ R : ℝ}
    (hτ : 0 ≤ τ) (hα : 0 < α) (hρ : 0 < ρ) (hR : R < 1)
    {X : Position I} (hX : X ∈ centeredAnnulus O ρ R) :
    0 ≤ centeredMassWeight O τ α X ∧ 0 ≤ centeredKineticWeight O τ α X ∧
      0 ≤ centeredRadiationWeight O τ α X ∧ 0 ≤ centeredSourceWeight O τ α X := by
  apply CarlemanWeightedL2.weights_nonneg hτ hα hρ hR
  simpa only [centeredAnnulus, annulus, Metric.mem_closedBall, Metric.mem_ball, mem_diff,
    dist_zero_right, ← dist_eq_norm] using hX

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)

def massEnergy (O : Configuration N) (τ α : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (X : Configuration N) : ℝ :=
  centeredMassWeight O τ α X * ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2

def kineticEnergy (O : Configuration N) (τ α : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (X : Configuration N) : ℝ :=
  centeredKineticWeight O τ α X * (∑ j, ‖covariant (Fin N × Fin 3) (fun _ => 0)
    C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0) (profileBound F χ)
      (profile_bound (N := N) F χ 0) e j u X‖ ^ 2)

def radiationEnergy (O : Configuration N) (τ α : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (X : Configuration N) : ℝ :=
  centeredRadiationWeight O τ α X *
    ‖radiation (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2

def sourceEnergy (O : Configuration N) (τ α : ℝ)
    (f : WaveSpace (Fin N × Fin 3)) (X : Configuration N) : ℝ :=
  centeredSourceWeight O τ α X * ‖f X‖ ^ 2

theorem density_eq_energies (O : Configuration N) (τ α : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (X : Configuration N) :
    centeredOperatorDensity F χ C e O τ α u X =
      massEnergy O τ α u X + kineticEnergy F χ C e O τ α u X +
        radiationEnergy O τ α u X := by
  simp only [centeredOperatorDensity, centeredDensity, massEnergy, kineticEnergy,
    radiationEnergy, centeredMassWeight, centeredKineticWeight, centeredRadiationWeight,
    massWeight, kineticWeight, radiationWeight, ← dist_eq_norm]
  ring

theorem source_eq_energy (O : Configuration N) (τ α : ℝ)
    (f : WaveSpace (Fin N × Fin 3)) (X : Configuration N) :
    centeredSource O τ α (fun Y => ‖f Y‖ ^ 2) X = sourceEnergy O τ α f X := by
  simp only [sourceEnergy, centeredSourceWeight, sourceWeight, centeredSource, ← dist_eq_norm]

/-- Annular support of the wave function supplies support of every form
coordinate and of the actual free operator source. -/
theorem supported_coordinates
    (hcore : AnnularCoreApproximation C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
      (profileBound F χ) (profile_bound (N := N) F χ 0) e)
    {u : Reference (Fin N × Fin 3) (fun _ => 0)} {f : WaveSpace (Fin N × Fin 3)}
    {O : Configuration N} {R : ℝ}
    (hu : FreeGraph C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
      (profileBound F χ) (profile_bound (N := N) F χ 0) e u f)
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R) :
    ∃ ρ R' : ℝ, 0 < ρ ∧ R' < R ∧
      (∀ᵐ X ∂volume, X ∉ centeredAnnulus O ρ R' →
        inclusion (Fin N × Fin 3) (fun _ => 0) u X = 0) ∧
      (∀ j, ∀ᵐ X ∂volume, X ∉ centeredAnnulus O ρ R' →
        covariant (Fin N × Fin 3) (fun _ => 0) C (profile (N := N) F χ 0)
          (profile_measurable (N := N) F χ 0) (profileBound F χ) (profile_bound (N := N) F χ 0) e j u X = 0) ∧
      (∀ᵐ X ∂volume, X ∉ centeredAnnulus O ρ R' →
        radiation (Fin N × Fin 3) (fun _ => 0) u X = 0) ∧
      (∀ᵐ X ∂volume, X ∉ centeredAnnulus O ρ R' → f X = 0) := by
  obtain ⟨ρ, R', hρ, hρR, hR, hsupp⟩ := hsupp
  let K := centeredAnnulus O ρ R'
  let s := {X : Configuration N | ρ / 2 < dist X O ∧ dist X O < (R' + R) / 2}
  have hK : IsCompact K := centeredAnnulus_compact O ρ R'
  have hs : IsOpen s := (isOpen_lt continuous_const (continuous_id.dist continuous_const)).inter
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const)
  have hKs : K ⊆ s := by
    intro X hX
    have hdist := centeredAnnulus_dist hX
    exact ⟨by linarith, by linarith⟩
  have hKsupport : ∀ᵐ X ∂volume, X ∉ K → inclusion (Fin N × Fin 3) (fun _ => 0) u X = 0 := by
    filter_upwards [hsupp] with X hX hnot
    apply hX
    by_cases hlo : dist X O < ρ
    · exact Or.inl hlo
    · right
      by_contra! hhi
      exact hnot ⟨hhi, hlo⟩
  have hcoordinates := centered_freeGraph_supported F χ 0 C e hcore hu hK hs hKs hKsupport
  have hsA : s ⊆ centeredAnnulus O (ρ / 2) ((R' + R) / 2) := by
    intro X hX
    exact ⟨hX.2.le, not_lt.mpr hX.1.le⟩
  have hKA := hKs.trans hsA
  exact ⟨ρ / 2, (R' + R) / 2, half_pos hρ, by linarith,
    hKsupport.mono (fun X hX hnot => hX (fun hx => hnot (hKA hx))),
    fun j => (hcoordinates.1 j).mono (fun X hX hnot => hX (fun hx => hnot (hsA hx))),
    hcoordinates.2.1.mono (fun X hX hnot => hX (fun hx => hnot (hsA hx))),
    hcoordinates.2.2.mono (fun X hX hnot => hX (fun hx => hnot (hsA hx)))⟩

def positiveMassWeight (O : Position I) (τ α : ℝ) (X : Position I) : ℝ :=
  max 0 (centeredMassWeight O τ α X)

def positiveKineticWeight (O : Position I) (τ α : ℝ) (X : Position I) : ℝ :=
  max 0 (centeredKineticWeight O τ α X)

def positiveMassEnergy (O : Configuration N) (τ α : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (X : Configuration N) : ℝ :=
  positiveMassWeight O τ α X * ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2

def positiveKineticEnergy (O : Configuration N) (τ α : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (X : Configuration N) : ℝ :=
  positiveKineticWeight O τ α X * (∑ j, ‖covariant (Fin N × Fin 3) (fun _ => 0)
    C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0) (profileBound F χ)
      (profile_bound (N := N) F χ 0) e j u X‖ ^ 2)

structure EnergyData (O : Configuration N) (R τ α : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (f : WaveSpace (Fin N × Fin 3)) : Prop where
  mass_integrable : Integrable (massEnergy O τ α u)
  kinetic_integrable : Integrable (kineticEnergy F χ C e O τ α u)
  radiation_integrable : Integrable (radiationEnergy O τ α u)
  source_integrable : Integrable (sourceEnergy O τ α f)
  mass_nonneg : ∀ᵐ X ∂volume, 0 ≤ massEnergy O τ α u X
  kinetic_nonneg : ∀ᵐ X ∂volume, 0 ≤ kineticEnergy F χ C e O τ α u X
  radiation_nonneg : ∀ᵐ X ∂volume, 0 ≤ radiationEnergy O τ α u X
  mass_supported : ∀ᵐ X ∂volume, X ∉ Metric.ball O R → massEnergy O τ α u X = 0
  kinetic_supported : ∀ᵐ X ∂volume, X ∉ Metric.ball O R → kineticEnergy F χ C e O τ α u X = 0
  radiation_supported : ∀ᵐ X ∂volume, X ∉ Metric.ball O R → radiationEnergy O τ α u X = 0
  source_supported : ∀ᵐ X ∂volume, X ∉ Metric.ball O R → sourceEnergy O τ α f X = 0
  positive_mass_eq : positiveMassEnergy O τ α u =ᵐ[volume] massEnergy O τ α u
  positive_kinetic_eq : positiveKineticEnergy F χ C e O τ α u =ᵐ[volume]
    kineticEnergy F χ C e O τ α u

theorem energy_data
    (hcore : AnnularCoreApproximation C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
      (profileBound F χ) (profile_bound (N := N) F χ 0) e)
    {u : Reference (Fin N × Fin 3) (fun _ => 0)} {f : WaveSpace (Fin N × Fin 3)}
    {O : Configuration N} {R τ α : ℝ} (hR : R < 1) (hτ : 0 ≤ τ) (hα : 0 < α)
    (hu : FreeGraph C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
      (profileBound F χ) (profile_bound (N := N) F χ 0) e u f)
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R) :
    EnergyData F χ C e O R τ α u f := by
  obtain ⟨ρ, R', hρ, hR', hm, hD, hQ, hf⟩ := supported_coordinates F χ C e hcore hu hsupp
  have hsmall := hR'.trans hR
  have hw := centered_weights_continuousOn O τ α hρ hsmall
  have hm0 : ∀ᵐ X ∂volume, X ∉ centeredAnnulus O ρ R' →
      ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2 = 0 :=
    hm.mono (fun X hx hn => by rw [hx hn]; simp)
  have hQ0 : ∀ᵐ X ∂volume, X ∉ centeredAnnulus O ρ R' →
      ‖radiation (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2 = 0 :=
    hQ.mono (fun X hx hn => by rw [hx hn]; simp)
  have hf0 : ∀ᵐ X ∂volume, X ∉ centeredAnnulus O ρ R' → ‖f X‖ ^ 2 = 0 :=
    hf.mono (fun X hx hn => by rw [hx hn]; simp)
  have hD0 : ∀ᵐ X ∂volume, X ∉ centeredAnnulus O ρ R' →
      (∑ j, ‖covariant (Fin N × Fin 3) (fun _ => 0) C (profile (N := N) F χ 0)
        (profile_measurable (N := N) F χ 0) (profileBound F χ) (profile_bound (N := N) F χ 0) e j u X‖ ^ 2) = 0 := by
    filter_upwards [Filter.eventually_all.mpr hD] with X hx hn
    simp only [hx _ hn, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
  have hsub : centeredAnnulus O ρ R' ⊆ Metric.ball O R :=
    fun X hx => (centeredAnnulus_dist hx).2.trans_lt hR'
  have hweight (X : Configuration N) (hx : X ∈ centeredAnnulus O ρ R') :=
    centered_weights_nonneg hτ hα hρ hsmall hx
  refine ⟨centered_annular_mul_integrable O ρ R' _ _ hw.1
      (Lp.memLp (inclusion (Fin N × Fin 3) (fun _ => 0) u)).norm.integrable_sq hm0,
    centered_annular_mul_integrable O ρ R' _ _ hw.2.1
      (integrable_finsetSum Finset.univ fun j _ => (Lp.memLp (covariant (Fin N × Fin 3)
        (fun _ => 0) C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0) (profileBound F χ)
          (profile_bound (N := N) F χ 0) e j u)).norm.integrable_sq) hD0,
    centered_annular_mul_integrable O ρ R' _ _ hw.2.2.1
      (Lp.memLp (radiation (Fin N × Fin 3) (fun _ => 0) u)).norm.integrable_sq hQ0,
    centered_annular_mul_integrable O ρ R' _ _ hw.2.2.2 (Lp.memLp f).norm.integrable_sq hf0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hm0] with X hx
    by_cases hX : X ∈ centeredAnnulus O ρ R'
    · exact mul_nonneg (hweight X hX).1 (sq_nonneg _)
    · simp only [massEnergy, hx hX, mul_zero, le_refl]
  · filter_upwards [hD0] with X hx
    by_cases hX : X ∈ centeredAnnulus O ρ R'
    · exact mul_nonneg (hweight X hX).2.1 (Finset.sum_nonneg fun j _ => sq_nonneg _)
    · simp only [kineticEnergy, hx hX, mul_zero, le_refl]
  · filter_upwards [hQ0] with X hx
    by_cases hX : X ∈ centeredAnnulus O ρ R'
    · exact mul_nonneg (hweight X hX).2.2.1 (sq_nonneg _)
    · simp only [radiationEnergy, hx hX, mul_zero, le_refl]
  · exact hm0.mono (fun X hx hn => by simp only [massEnergy, hx (fun h => hn (hsub h)), mul_zero])
  · exact hD0.mono (fun X hx hn => by simp only [kineticEnergy, hx (fun h => hn (hsub h)), mul_zero])
  · exact hQ0.mono (fun X hx hn => by simp only [radiationEnergy, hx (fun h => hn (hsub h)), mul_zero])
  · exact hf0.mono (fun X hx hn => by simp only [sourceEnergy, hx (fun h => hn (hsub h)), mul_zero])
  · filter_upwards [hm0] with X hx
    by_cases hX : X ∈ centeredAnnulus O ρ R'
    · simp only [positiveMassEnergy, positiveMassWeight, massEnergy,
        max_eq_right (hweight X hX).1]
    · simp only [positiveMassEnergy, massEnergy, hx hX, mul_zero]
  · filter_upwards [hD0] with X hx
    by_cases hX : X ∈ centeredAnnulus O ρ R'
    · simp only [positiveKineticEnergy, positiveKineticWeight, kineticEnergy,
        max_eq_right (hweight X hX).2.1]
    · simp only [positiveKineticEnergy, kineticEnergy, hx hX, mul_zero]

structure EnergyEstimate (O : Configuration N) (R τ α : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (f : WaveSpace (Fin N × Fin 3))
    : Prop extends EnergyData F χ C e O R τ α u f where
  mass_bound : (∫ X, positiveMassEnergy O τ α u X) ≤ 64 * ∫ X, sourceEnergy O τ α f X
  kinetic_bound : (∫ X, positiveKineticEnergy F χ C e O τ α u X) ≤
    64 * ∫ X, sourceEnergy O τ α f X

theorem energy_estimate_of_ball
    (hcore : AnnularCoreApproximation C (profile (N := N) F χ 0)
      (profile_measurable (N := N) F χ 0) (profileBound F χ) (profile_bound (N := N) F χ 0) e)
    {u : Reference (Fin N × Fin 3) (fun _ => 0)} {f : WaveSpace (Fin N × Fin 3)}
    {O : Configuration N} {R τ α : ℝ} (hR : R < 1) (hτ : 0 ≤ τ) (hα : 0 < α)
    (hu : FreeGraph C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
      (profileBound F χ) (profile_bound (N := N) F χ 0) e u f)
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R)
    (hball : (∫ X in Metric.ball O R, centeredOperatorDensity F χ C e O τ α u X) ≤
      64 * ∫ X in Metric.ball O R, centeredSource O τ α (fun Y => ‖f Y‖ ^ 2) X) :
    EnergyEstimate F χ C e O R τ α u f := by
  have hd := energy_data F χ C e hcore hR hτ hα hu hsupp
  have hdI : Integrable (centeredOperatorDensity F χ C e O τ α u) := by
    apply ((hd.mass_integrable.add hd.kinetic_integrable).add hd.radiation_integrable).congr
    exact ae_of_all _ fun X => (density_eq_energies F χ C e O τ α u X).symm
  have hdS : ∀ᵐ X ∂volume, X ∉ Metric.ball O R →
      centeredOperatorDensity F χ C e O τ α u X = 0 := by
    filter_upwards [hd.mass_supported, hd.kinetic_supported, hd.radiation_supported]
      with X hm hk hq hn
    rw [density_eq_energies, hm hn, hk hn, hq hn]
    norm_num
  have hsball : (∫ X in Metric.ball O R,
      centeredSource O τ α (fun Y => ‖f Y‖ ^ 2) X) = ∫ X, sourceEnergy O τ α f X :=
    (integral_congr_ae (ae_of_all _ fun X => source_eq_energy O τ α f X)).trans
      (setIntegral_eq_integral_of_ae_compl_eq_zero hd.source_supported)
  have hglobal : (∫ X, centeredOperatorDensity F χ C e O τ α u X) ≤
      64 * ∫ X, sourceEnergy O τ α f X := by
    rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hdS, ← hsball]
    exact hball
  refine ⟨hd, ?_, ?_⟩
  · rw [integral_congr_ae hd.positive_mass_eq]
    apply (integral_mono_ae hd.mass_integrable hdI ?_).trans hglobal
    filter_upwards [hd.kinetic_nonneg, hd.radiation_nonneg] with X hk hq
    rw [density_eq_energies]
    linarith
  · rw [integral_congr_ae hd.positive_kinetic_eq]
    apply (integral_mono_ae hd.kinetic_integrable hdI ?_).trans hglobal
    filter_upwards [hd.mass_nonneg, hd.radiation_nonneg] with X hm hq
    rw [density_eq_energies]
    linarith

open PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.SphereCoreGeometry
  PfHk.OrdinaryPolarSobolevChart

theorem exists_uniform_energy_estimate (hUV : CarlemanUV χ)
    (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
    (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
    (S : StandardPolarSobolevCharts N) (L : StandardLogPolarCalculus (Fin N × Fin 3))
    (hN : 0 < Fintype.card (Fin N × Fin 3))
    (D : WeylCoreReference.StandardWeylFormCoreDensity W B)
    (A : ∀ O : Configuration N, AnnularCoreApproximation C (profile F χ O)
      (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e)
    (α : ℝ) (hα : 0 < α) :
    ∃ r₀ τ₀ : ℝ, 0 < r₀ ∧ r₀ < Real.exp (-2) ∧ 1 ≤ τ₀ ∧
      ∀ τ : ℝ, τ₀ ≤ τ → ∀ (O : Configuration N) (R : ℝ), 0 < R → R ≤ r₀ →
      ∀ (u : Reference (Fin N × Fin 3) (fun _ => 0)) (f : WaveSpace (Fin N × Fin 3)),
      FreeGraph C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
        (profileBound F χ) (profile_bound (N := N) F χ 0) e u f →
      AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R →
      EnergyEstimate F χ C e O R τ α u f := by
  have hex := exists_uniform_estimate (N := N) F χ hUV e C W B P G S L hN D A α hα
  let r₀ := Classical.choose hex
  let τ₀ := Classical.choose (Classical.choose_spec hex)
  have h := Classical.choose_spec (Classical.choose_spec hex)
  refine ⟨r₀, τ₀, h.1, h.2.1, h.2.2.1, ?_⟩
  intro τ hτ O R hRpos hR u f hu hsupp
  apply energy_estimate_of_ball F χ C e (A 0)
    (hR.trans_lt (h.2.1.trans (Real.exp_lt_one_iff.mpr (by norm_num))))
    (show 0 ≤ τ from zero_le_one.trans (h.2.2.1.trans hτ)) hα hu hsupp
  exact h.2.2.2 τ hτ O R hRpos hR u f hu hsupp

end PfHk.PhysicalDyadicEnergy
