import GptLean.PhysicalSourceTests
import GptLean.PhotonLocalizationPosition
import GptLean.RemovalPhysicalPair
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Electronic position measures and one-particle densities of actual L2 vectors.
The density sums all particle marginals, so it applies without symmetry or
finite kinetic energy. The marginal identity is proved by the actual Fubini
maps, and the electronic cutoff tail is consequently a theorem.
-/

noncomputable section

namespace GptLean.PhysicalElectronicDensity

open MeasureTheory PhysicalSourceCoordinates PhysicalSourceMarginal PhysicalSourcePair
open PhotonLocalization
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

abbrev Wave := ElectronicH1Space.L2 H (Fin N × Fin 3)

private theorem square_integrable {X K : Type*} [MeasurableSpace X]
    [NormedAddCommGroup K] (μ : Measure X) (u : Lp K 2 μ) :
    Integrable (fun x => ‖u x‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)

private theorem aeStronglyMeasurable_change_borel {X K : Type*}
    [TopologicalSpace X] [TopologicalSpace K]
    {m m' m₀ : MeasurableSpace X} [@BorelSpace X _ m] [@BorelSpace X _ m']
    {μ : Measure[m₀] X} {f : X → K} (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m'] f μ := by
  apply hf.mono
  exact le_of_eq ((@BorelSpace.measurable_eq X _ m _).trans
    (@BorelSpace.measurable_eq X _ m' _).symm)

/-- Sum of the actual marginal source norms, with no selected particle. -/
def densityFunction (u : Wave (N := N) (H := H)) (x : PhysicalPairSpace.Position) : ℝ :=
  ∑ i : Fin N, ‖particleMap i u x‖ ^ 2

theorem densityFunction_nonneg (u : Wave (N := N) (H := H)) (x) :
    0 ≤ densityFunction u x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem densityFunction_integrable (u : Wave (N := N) (H := H)) :
    Integrable (densityFunction u) volume :=
  integrable_finsetSum _ fun i _ => square_integrable volume (particleMap i u)

def density (u : Wave (N := N) (H := H)) : Lp ℝ 1 (volume : Measure PhysicalPairSpace.Position) :=
  (memLp_one_iff_integrable.mpr (densityFunction_integrable u)).toLp (densityFunction u)

theorem density_ae (u : Wave (N := N) (H := H)) :
    (density u : PhysicalPairSpace.Position → ℝ) =ᵐ[volume] densityFunction u :=
  (memLp_one_iff_integrable.mpr (densityFunction_integrable u)).coeFn_toLp

theorem density_nonneg (u : Wave (N := N) (H := H)) :
    ∀ᵐ x ∂volume, 0 ≤ density u x := by
  filter_upwards [density_ae u] with x hx
  exact hx.symm ▸ densityFunction_nonneg u x

theorem density_norm_ae (u : Wave (N := N) (H := H)) :
    (fun x => ‖density u x‖) =ᵐ[volume] densityFunction u := by
  filter_upwards [density_ae u] with x hx
  rw [hx, Real.norm_eq_abs, abs_of_nonneg (densityFunction_nonneg u x)]

theorem particle_test_measurable (i : Fin N) (f : PhysicalPairSpace.Position → ℝ)
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun z : Configuration N => f (SymmetricLift.particle z i)) volume := by
  have h := hf.comp_fst.comp_measurePreserving (split_measurePreserving i)
  have h' := aeStronglyMeasurable_change_borel
    (m' := WithLp.measurableSpace 2 (Fin N × Fin 3 → ℝ)) h
  have he : ((fun p : PhysicalSourceCoordinates.Position × Spectator i => f p.1) ∘ split i) =
      (fun z : Configuration N => f (SymmetricLift.particle z i)) := by
    funext z
    exact congrArg f (split_fst_eq_particle i z)
  exact he ▸ h'

omit [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H] in
theorem particle_test_integrable (u : Wave (N := N) (H := H))
    (i : Fin N) (f : PhysicalPairSpace.Position → ℝ)
    (hf : AEStronglyMeasurable f volume) {c : ℝ} (hc : ∀ x, ‖f x‖ ≤ c) :
    Integrable (fun z : Configuration N => f (SymmetricLift.particle z i) * ‖u z‖ ^ 2) :=
  (square_integrable volume u).bdd_mul (particle_test_measurable i f hf)
    (ae_of_all _ fun z => hc (SymmetricLift.particle z i))

theorem density_tested (u : Wave (N := N) (H := H))
    (f : PhysicalPairSpace.Position → ℝ) (hf : AEStronglyMeasurable f volume)
    {c : ℝ} (hc : ∀ x, ‖f x‖ ≤ c) :
    (∫ x, f x * density u x) =
      ∫ z, (∑ i : Fin N, f (SymmetricLift.particle z i)) * ‖u z‖ ^ 2 := by
  have hleft (i : Fin N) : Integrable (fun x => f x * ‖particleMap i u x‖ ^ 2) :=
    (square_integrable volume (particleMap i u)).bdd_mul hf
      (ae_of_all _ hc)
  have hright (i : Fin N) : Integrable
      (fun z => f (SymmetricLift.particle z i) * ‖u z‖ ^ 2) :=
    particle_test_integrable u i f hf hc
  calc
    _ = ∫ x, ∑ i : Fin N, f x * ‖particleMap i u x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [density_ae u] with x hx
      rw [hx, densityFunction, Finset.mul_sum]
    _ = ∑ i : Fin N, ∫ x, f x * ‖particleMap i u x‖ ^ 2 :=
      integral_finsetSum _ (fun i _ => hleft i)
    _ = ∑ i : Fin N, ∫ z, f (SymmetricLift.particle z i) * ‖u z‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [split_fst_eq_particle] using
        particleMap_tested_norm_sq i u f hf (ae_of_all _ hc)
    _ = _ := by
      rw [← integral_finsetSum _ (fun i _ => hright i)]
      congr 1
      funext z
      exact (Finset.sum_mul _ _ _).symm

/-- The full configuration probability measure before changing coordinates. -/
def configurationMeasure (u : Wave (N := N) (H := H)) : Measure (Configuration N) :=
  volume.withDensity (fun z => ENNReal.ofReal (‖u z‖ ^ 2))

instance configurationMeasure_finite (u : Wave (N := N) (H := H)) :
    IsFiniteMeasure (configurationMeasure u) :=
  isFiniteMeasure_withDensity_ofReal (square_integrable volume u).2

omit [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H] in
theorem configurationMeasure_integral (u : Wave (N := N) (H := H))
    (f : Configuration N → ℝ) :
    (∫ z, f z ∂configurationMeasure u) = ∫ z, f z * ‖u z‖ ^ 2 := by
  have hm : AEMeasurable (fun z => ENNReal.ofReal (‖u z‖ ^ 2)) volume :=
    ((Lp.aestronglyMeasurable u).norm.pow 2).aemeasurable.ennreal_ofReal
  have h := integral_withDensity_eq_integral_toReal_smul₀ hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) f
  simpa only [configurationMeasure, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul,
    mul_comm] using h

/-- Position spectral measure in the same coordinates as the cutoff calculus. -/
def positionMeasure (u : Wave (N := N) (H := H)) :
    Measure (Fin N → ElectronicPosition) :=
  (configurationMeasure u).map electronicPositions

instance positionMeasure_finite (u : Wave (N := N) (H := H)) :
    IsFiniteMeasure (positionMeasure u) := by
  unfold positionMeasure
  infer_instance

omit [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H] in
theorem positionMeasure_integral (u : Wave (N := N) (H := H))
    (f : (Fin N → ElectronicPosition) → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂positionMeasure u) =
      ∫ z, f (electronicPositions z) * ‖u z‖ ^ 2 := by
  rw [positionMeasure, integral_map electronicPositions.continuous.measurable.aemeasurable
    hf.aestronglyMeasurable]
  exact configurationMeasure_integral u _

theorem electronicDensityMeasure (u : Wave (N := N) (H := H)) :
    ElectronicDensityMeasure (positionMeasure u) (density u) where
  test f hf hb := by
    obtain ⟨c, hc⟩ := hb
    have hm : Measurable (fun z : Fin N → ElectronicPosition => ∑ i, f (z i)) :=
      Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply i)
    calc
      _ = ∫ z, (∑ i : Fin N, f (electronicPositions z i)) * ‖u z‖ ^ 2 :=
        positionMeasure_integral u _ hm
      _ = ∫ x, f x * density u x := (density_tested u f hf.aestronglyMeasurable hc).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [density_nonneg u] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg hx]

theorem density_integral (u : Wave (N := N) (H := H)) :
    (∫ x, density u x) = (N : ℝ) * ‖u‖ ^ 2 := by
  have h := density_tested u (fun _ => 1) aestronglyMeasurable_const (c := 1) (by simp)
  have hn := Repair.toL2_norm_sq (Lp.memLp u)
  simp only [Lp.toLp_coeFn] at hn
  simpa only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, integral_const_mul, ← hn] using h

theorem density_norm (u : Wave (N := N) (H := H)) :
    ‖density u‖ = (N : ℝ) * ‖u‖ ^ 2 := by
  rw [L1.norm_eq_integral_norm]
  exact (integral_congr_ae (by
    filter_upwards [density_nonneg u] with x hx
    exact Real.norm_of_nonneg hx)).trans (density_integral u)

theorem density_eq_of_configuration_ae
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [TopologicalSpace.SeparableSpace K]
    (u : Wave (N := N) (H := H)) (v : Wave (N := N) (H := K))
    (h : (fun z => ‖u z‖ ^ 2) =ᵐ[volume] fun z => ‖v z‖ ^ 2) :
    density u = density v := by
  apply Lp.ext
  apply RemovalConstraints.ae_eq_of_boundedSpatialTests
    (memLp_one_iff_integrable.mp (Lp.memLp _))
    (memLp_one_iff_integrable.mp (Lp.memLp _))
  intro t
  exact (density_tested u t.weight t.measurable t.bounded).trans
    ((integral_congr_ae (h.mono fun z hz => congrArg
      (fun r : ℝ => (∑ i : Fin N, t.weight (SymmetricLift.particle z i)) * r) hz)).trans
        (density_tested v t.weight t.measurable t.bounded).symm)

end GptLean.PhysicalElectronicDensity
