import GptLean.PhysicalWeightedDensity
import GptLean.PhysicalPFCompactnessDensity
import Mathlib.Algebra.Order.Chebyshev

/-!
The density second moment controls the actual configuration and total
dipole moments of every normal spectral source. The identities apply to
unbounded position weights and prove finiteness before taking real sums.
-/

noncomputable section
namespace GptLean.PhysicalDipoleMoment

open MeasureTheory PhysicalElectronicDensity PhysicalEnsembleSource
  PhysicalSourceCoordinates SymmetricLift PhysicalPFReference PhysicalFock
  PhysicalNormalTrace PhysicalClosedForms PhysicalPFSource
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

def FiniteSecondMoment (d : PhysicalPairSpace.Pair) : Prop :=
  Integrable (fun y => ‖y‖ ^ 2 * PhysicalPairSpace.densityL1 d y) volume

def secondMoment (d : PhysicalPairSpace.Pair) : ℝ :=
  ∫ y, ‖y‖ ^ 2 * PhysicalPairSpace.densityL1 d y

def totalPosition {N : ℕ} (x : SymmetricLift.Configuration N) : PhysicalPairSpace.Position :=
  ∑ i : Fin N, particle x i

def configurationWeight {N : ℕ} (x : SymmetricLift.Configuration N) : ℝ :=
  ∑ i : Fin N, ‖particle x i‖ ^ 2

theorem totalPosition_continuous {N : ℕ} : Continuous (totalPosition (N := N)) := by
  change Continuous (fun x => ∑ i : Fin N, particleLinear i x)
  exact continuous_finsetSum _ fun i _ => (particleLinear i).continuous_of_finiteDimensional

theorem configurationWeight_continuous {N : ℕ} :
    Continuous (configurationWeight (N := N)) := by
  change Continuous (fun x => ∑ i : Fin N, ‖particleLinear i x‖ ^ 2)
  exact continuous_finsetSum _ fun i _ =>
    (particleLinear i).continuous_of_finiteDimensional.norm.pow 2

theorem configurationWeight_nonneg {N : ℕ} (x : SymmetricLift.Configuration N) :
    0 ≤ configurationWeight x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem totalPosition_sq_le {N : ℕ} (x : SymmetricLift.Configuration N) :
    ‖totalPosition x‖ ^ 2 ≤ (N : ℝ) * configurationWeight x := by
  calc
    _ ≤ (∑ i : Fin N, ‖particle x i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      simpa only [Finset.card_univ, Fintype.card_fin, configurationWeight] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun i : Fin N => ‖particle x i‖))

section Vectors

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

def vectorMoment (u : Wave (N := N) (H := H)) : ℝ :=
  ∫ x, ‖totalPosition x‖ ^ 2 * ‖u x‖ ^ 2

omit [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem vectorMoment_nonneg (u : Wave (N := N) (H := H)) : 0 ≤ vectorMoment u :=
  integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

omit [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem vectorMoment_integrable (u : Wave (N := N) (H := H))
    (hu : Integrable (fun x => configurationWeight x * ‖u x‖ ^ 2)) :
    Integrable (fun x => ‖totalPosition x‖ ^ 2 * ‖u x‖ ^ 2) := by
  apply (hu.const_mul (N : ℝ)).mono'
    ((totalPosition_continuous.norm.pow 2).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable u).norm.pow 2))
  filter_upwards [] with x
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact (mul_le_mul_of_nonneg_right (totalPosition_sq_le x) (sq_nonneg _)).trans_eq
    (mul_assoc _ _ _)

theorem vectorMoment_le (u : Wave (N := N) (H := H))
    (hu : Integrable (fun x => configurationWeight x * ‖u x‖ ^ 2)) :
    vectorMoment u ≤ (N : ℝ) * ∫ x, configurationWeight x * ‖u x‖ ^ 2 := by
  rw [← integral_const_mul]
  apply integral_mono (vectorMoment_integrable u hu) (hu.const_mul (N : ℝ))
  intro x
  exact (mul_le_mul_of_nonneg_right (totalPosition_sq_le x) (sq_nonneg _)).trans_eq
    (mul_assoc _ _ _)

theorem ensemble_moments (v : ℕ → Wave (N := N) (H := H))
    (hv : Summable (fun n => ‖v n‖ ^ 2))
    (hρ : Integrable (fun y => ‖y‖ ^ 2 * density (ensemble v hv) y)) :
    (∀ n, Integrable (fun x => configurationWeight x * ‖v n x‖ ^ 2)) ∧
      HasSum (fun n => ∫ x, configurationWeight x * ‖v n x‖ ^ 2)
        (∫ y, ‖y‖ ^ 2 * density (ensemble v hv) y) ∧
      (∀ n, Integrable (fun x => ‖totalPosition x‖ ^ 2 * ‖v n x‖ ^ 2)) ∧
      Summable (fun n => vectorMoment (v n)) ∧
      (∑' n, vectorMoment (v n)) ≤ (N : ℝ) *
        ∫ y, ‖y‖ ^ 2 * density (ensemble v hv) y := by
  have h := PhysicalWeightedDensity.ensemble_density_weighted v hv
    (fun y => ‖y‖ ^ 2) (continuous_norm.pow 2).aestronglyMeasurable
    (fun _ => sq_nonneg _) hρ
  have hb (n : ℕ) := vectorMoment_le (v n) (h.1 n)
  have hs := Summable.of_nonneg_of_le (fun n => vectorMoment_nonneg (v n)) hb
    (h.2.summable.mul_left (N : ℝ))
  refine ⟨h.1, h.2, fun n => vectorMoment_integrable (v n) (h.1 n), hs, ?_⟩
  exact (hs.tsum_le_tsum hb (h.2.summable.mul_left (N : ℝ))).trans_eq
    (by simpa only [tsum_mul_left, configurationWeight] using
      congrArg (fun t : ℝ => (N : ℝ) * t) h.2.tsum_eq)

end Vectors

section Normal

attribute [local irreducible] PhysicalPFReference.normalEnergy PhysicalPFStates.pair

variable {N : ℕ} (i : Fin N) (V : Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (k : Fin N × Fin 3 → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hk : ∀ q, AEStronglyMeasurable (k q) volume)
  (M : ℝ) (hM : ∀ q, ∀ᵐ x ∂volume, ‖k q x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

/-- The actual pair moment supplies all spectral position integrals and
their exact sum, hence the summable total-dipole bound. -/
theorem normal_source_moments
    (m : PhysicalPFStates.MixedState V C k hk M hM B S e)
    (s : Source (Fin N × Fin 3) V B m.val.val)
    (hρ : FiniteSecondMoment ((PhysicalPFStates.mixedModel i V C k hk M hM B S e).density m)) :
    (∀ n, Integrable (fun x => configurationWeight x *
      ‖inclusion (Fin N × Fin 3) V (s.vector n) x‖ ^ 2)) ∧
      HasSum (fun n => ∫ x, configurationWeight x *
        ‖inclusion (Fin N × Fin 3) V (s.vector n) x‖ ^ 2)
        (secondMoment ((PhysicalPFStates.mixedModel i V C k hk M hM B S e).density m)) ∧
      (∀ n, Integrable (fun x => ‖totalPosition x‖ ^ 2 *
        ‖inclusion (Fin N × Fin 3) V (s.vector n) x‖ ^ 2)) ∧
      Summable (fun n => vectorMoment (inclusion (Fin N × Fin 3) V (s.vector n))) ∧
      (∑' n, vectorMoment (inclusion (Fin N × Fin 3) V (s.vector n))) ≤ (N : ℝ) *
        secondMoment ((PhysicalPFStates.mixedModel i V C k hk M hM B S e).density m) := by
  let v := fun n => inclusion (Fin N × Fin 3) V (s.vector n)
  have hd := PhysicalNormalElectronicDensity.density_eq_spectral B.normal
    (B.realization (WaveSpace (Fin N × Fin 3))).functional m.val.property.1 v s.hasSum
  have hp : PhysicalNormalElectronicDensity.density B.normal m.val.val =
      PhysicalPairSpace.densityL1
        ((PhysicalPFStates.mixedModel i V C k hk M hM B S e).density m) :=
    PhysicalPFCompactnessDensity.density_eq_pair B i V C k hk M hM S e
      m.val.property.1 m.val.property.2.2 m.property
  have he := hd.symm.trans hp
  have hi : Integrable (fun y => ‖y‖ ^ 2 * density (ensemble v s.mass_hasSum.summable) y) := by
    simpa only [he, FiniteSecondMoment] using hρ
  have h := ensemble_moments v s.mass_hasSum.summable hi
  simpa only [he, secondMoment] using h

end Normal
end GptLean.PhysicalDipoleMoment
