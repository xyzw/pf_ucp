import GptLean.PhysicalElectronicDensity
import GptLean.PhysicalEnsembleObservables
import GptLean.PhysicalNormalTrace
import GptLean.PhysicalFockKrausL2
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
The position measure and summed one-particle density of a positive normal
trace. They are constructed from its actual countable spectral ensemble.
The multiplication trace formula and independence of the density from the
decomposition are derived, rather than supplied as position-calculus assumptions.
-/

noncomputable section

namespace GptLean.PhysicalNormalElectronicDensity

open MeasureTheory PhotonLocalization PhotonLocalizationChannel
open PhysicalEnsembleSource PhysicalElectronicDensity PhysicalSourceCoordinates
open scoped ENNReal BoundedContinuousFunction

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

private instance fiberSeparable (H : Type*) [NormedAddCommGroup H]
    [TopologicalSpace.SeparableSpace H] : TopologicalSpace.SeparableSpace (Fiber H) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  infer_instance

variable {N : ℕ} {H T : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData (Wave (N := N) (H := H)) T}
  (normal : NormalTraceData R)

def vectors (x : T) (hx : x ∈ R.positive) : ℕ → Wave (N := N) (H := H) :=
  Classical.choose (normal.positive_decomposition x hx)

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] [CompleteSpace T] in
theorem vectors_hasSum (x : T) (hx : x ∈ R.positive) :
    HasSum (fun n => R.rankOne (vectors normal x hx n)) x :=
  Classical.choose_spec (normal.positive_decomposition x hx)

def sourceOfPositive (x : T) (hx : x ∈ R.positive) :
    Wave (N := N) (H := Fiber H) :=
  ensemble (vectors normal x hx) (spectral_mass_hasSum (vectors_hasSum normal x hx)).summable

/-- Zero is used off the positive cone solely to define an ambient map. -/
def source (x : T) : Wave (N := N) (H := Fiber H) := by
  classical
  exact if hx : x ∈ R.positive then sourceOfPositive normal x hx else 0

omit [CompleteSpace H] [CompleteSpace T] in
theorem source_eq (x : T) (hx : x ∈ R.positive) :
    source normal x = sourceOfPositive normal x hx := by
  classical
  exact dite_eq_left hx

def density (x : T) : Lp ℝ 1 (volume : Measure PhysicalPairSpace.Position) :=
  PhysicalElectronicDensity.density (source normal x)

def position (x : T) : Measure (Fin N → ElectronicPosition) :=
  positionMeasure (source normal x)

instance position_finite (x : T) : IsFiniteMeasure (position normal x) :=
  positionMeasure_finite _

omit [CompleteSpace H] [CompleteSpace T] in
theorem electronicDensityMeasure (x : T) :
    ElectronicDensityMeasure (position normal x) (density normal x) :=
  PhysicalElectronicDensity.electronicDensityMeasure _

omit [CompleteSpace T] in
theorem density_eq_spectral (F : NormalFunctionalData R) {x : T}
    (hx : x ∈ R.positive) (v : ℕ → Wave (N := N) (H := H))
    (hv : HasSum (fun n => R.rankOne (v n)) x) :
    density normal x = PhysicalElectronicDensity.density
      (ensemble v (spectral_mass_hasSum hv).summable) := by
  apply density_eq_of_configuration_ae
  rw [source_eq normal x hx]
  exact ensemble_density_independent F (vectors_hasSum normal x hx) hv

omit [CompleteSpace H] [CompleteSpace T] in
theorem source_norm_sq {x : T} (hx : x ∈ R.positive) :
    ‖source normal x‖ ^ 2 = R.trace x := by
  rw [source_eq normal x hx]
  exact (ensemble_norm_sq _ _).trans (spectral_mass_hasSum (vectors_hasSum normal x hx)).tsum_eq

omit [CompleteSpace H] [CompleteSpace T] in
theorem density_norm {x : T} (hx : x ∈ R.positive) :
    ‖density normal x‖ = (N : ℝ) * R.trace x :=
  (PhysicalElectronicDensity.density_norm _).trans
    (congrArg (fun r : ℝ => (N : ℝ) * r) (source_norm_sq normal hx))

omit [CompleteSpace T] in
theorem position_trace (F : NormalFunctionalData R) {x : T}
    (hx : x ∈ R.positive) (f : (Fin N → ElectronicPosition) →ᵇ ℝ) :
    (F.repr x (positionObservable f)).re = ∫ z, f z ∂position normal x := by
  have h := ensemble_scalar_trace F (vectors_hasSum normal x hx)
    (fun z => f (electronicPositions z))
    (f.continuous.comp electronicPositions.continuous).aestronglyMeasurable
    (C := ‖f‖) (ae_of_all _ fun z => f.norm_coe_le_norm (electronicPositions z))
  have hm := positionMeasure_integral (source normal x) f f.continuous.measurable
  have he : (∫ z, f (electronicPositions z) * ‖source normal x z‖ ^ 2) =
      ∫ z, f (electronicPositions z) * ‖sourceOfPositive normal x hx z‖ ^ 2 :=
    congrArg (fun u : Wave (N := N) (H := Fiber H) =>
      ∫ z, f (electronicPositions z) * ‖u z‖ ^ 2) (source_eq normal x hx)
  exact h.trans (he.symm.trans hm.symm)

/-- Any actual fiber Kraus isometry preserves the same position measure. -/
theorem position_trace_lift (F : NormalFunctionalData R)
    (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => H) 2) {x : T}
    (hx : x ∈ R.positive) (f : (Fin N → ElectronicPosition) →ᵇ ℝ) :
    (F.repr (normal.extend (PhysicalFock.KrausL2.lift volume U) x)
      (positionObservable f)).re = ∫ z, f z ∂position normal x := by
  have hcomm (v : Wave (N := N) (H := H)) (a : ℕ) :
      PhysicalFock.KrausL2.lift volume U (positionObservable f v) a =
        positionObservable f (PhysicalFock.KrausL2.lift volume U v a) := by
    let A := (lp.evalCLM ℂ (fun _ : ℕ => H) 2 a).comp U.toContinuousLinearMap
    exact (congrArg (fun P : Wave (N := N) (H := H) →L[ℂ] Wave (N := N) (H := H) => P v)
      (realL2Multiplier_commute_compLpL (fun z => f (electronicPositions z))
        (f.continuous.comp electronicPositions.continuous).aestronglyMeasurable
        ‖f‖ (ae_of_all _ fun z => f.norm_coe_le_norm (electronicPositions z)) A).eq).symm
  have he := F.electronic normal (PhysicalFock.KrausL2.lift volume U) (positionObservable f)
    hcomm hx
  exact (congrArg Complex.re he).trans (position_trace normal F hx f)

omit [CompleteSpace T] in
/-- Fermionic symmetry reduces the summed marginal to any selected particle. -/
theorem density_tested_fermionic (F : NormalFunctionalData R) {x : T}
    (hx : x ∈ R.positive) (v : ℕ → Wave (N := N) (H := H))
    (hv : HasSum (fun n => R.rankOne (v n)) x)
    (hfermion : ∀ n, v n ∈ PhysicalElectronicFermions.fermionicSubspace N H)
    (i : Fin N) (f : PhysicalPairSpace.Position → ℝ) (hf : AEStronglyMeasurable f volume)
    {c : ℝ} (hc : ∀ z, ‖f z‖ ≤ c) :
    (∫ z, f z * density normal x z) =
      (N : ℝ) * ∑' n, ∫ z, f (SymmetricLift.particle z i) * ‖v n z‖ ^ 2 := by
  let a : Configuration N → ℝ := fun z => ∑ j : Fin N, f (SymmetricLift.particle z j)
  have ha : AEStronglyMeasurable a volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun j _ => particle_test_measurable j f hf
  have hb : ∀ z, ‖a z‖ ≤ (N : ℝ) * c := by
    intro z
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => hc _).trans_eq (by simp))
  have hs := ensemble_tested_mass_hasSum v (spectral_mass_hasSum hv).summable
    a ha (ae_of_all _ hb)
  have he := density_eq_spectral normal F hx v hv
  calc
    _ = ∫ z, a z * ‖ensemble v (spectral_mass_hasSum hv).summable z‖ ^ 2 := by
      rw [he]
      exact density_tested _ f hf hc
    _ = ∑' n, ∫ z, a z * ‖v n z‖ ^ 2 := hs.tsum_eq.symm
    _ = ∑' n, (N : ℝ) * ∫ z, f (SymmetricLift.particle z i) * ‖v n z‖ ^ 2 := by
      apply tsum_congr
      intro n
      simp_rw [a, Finset.sum_mul]
      rw [integral_finsetSum _ (fun j _ => particle_test_integrable (v n) j f hf hc)]
      simp_rw [PhysicalElectronicFermions.density_particle_integral_eq N H
        ⟨v n, hfermion n⟩ _ i f]
      simp
    _ = _ := tsum_mul_left

end GptLean.PhysicalNormalElectronicDensity
