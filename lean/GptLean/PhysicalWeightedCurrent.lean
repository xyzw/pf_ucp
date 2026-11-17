import GptLean.PhysicalWeightedCurrentCore
import GptLean.PhysicalPFPair
import GptLean.PhysicalNormalElectronicDensity

/-!
Physical current tests for unbounded velocities with integrable squared
density weight. The current integral and its spectral source series are
identified from the actual coordinate marginal and ensemble.
-/

noncomputable section
namespace GptLean.PhysicalWeightedCurrentCore

open MeasureTheory Filter ElectronicH1Space PhysicalPairSpace PhysicalPairRealization
  PhysicalSourceCoordinates PhysicalSourceMarginal PhysicalSourcePair PhysicalEnsembleSource
  PhysicalEnsembleH1
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- The actual one-particle current agrees with an integrable weighted
configuration current. -/
theorem tested_current_ofWaveFunction (i : Fin N) (u : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) (b : Fin 3)
    (a : PhysicalPairSpace.Position → ℝ)
    (hi : Integrable (fun z => a (SymmetricLift.particle z i) *
      (inner ℂ (value u z) (d b z)).re)) :
    Integrable (fun x => a x * currentL1 (ofWaveFunction i u d) x b) ∧
      (∫ x, a x * currentL1 (ofWaveFunction i u d) x b) =
      (N : ℝ) * ∫ z, a (SymmetricLift.particle z i) * (inner ℂ (value u z) (d b z)).re := by
  have hp := particleMap_tested_re_inner i (value u) (d b) a hi
  have he : (fun x => a x * currentL1 (ofWaveFunction i u d) x b) =ᵐ[volume]
      fun x => (N : ℝ) * (a x * (inner ℂ (particleMap i (value u) x)
        (particleMap i (d b) x)).re) := by
    filter_upwards [current_ofSource_ae N (particleMap i (value u))
      (fun c => particleMap i (d c)) (Lp.memLp _) (particleSource_memLp_six i u)
      (fun _ => Lp.memLp _)] with x hx
    have hscalar := congrArg (fun j : PhysicalPairSpace.Vector => a x * j b) hx
    change a x * currentL1 (ofWaveFunction i u d) x b =
      a x * ((N : ℝ) * (inner ℂ (particleMap i (value u) x) (particleMap i (d b) x)).re)
      at hscalar
    exact hscalar.trans (mul_left_comm _ _ _)
  refine ⟨(hp.1.const_mul (N : ℝ)).congr he.symm, ?_⟩
  exact (integral_congr_ae he).trans ((integral_const_mul _ _).trans
    (congrArg (fun r : ℝ => (N : ℝ) * r) hp.2))

/-- Unbounded one-particle tests of the actual ensemble pair equal the
source series. The density-weighted square condition is sufficient. -/
theorem tested_current_ofEnsemble (i : Fin N) (v : ℕ → H1 H (Fin N × Fin 3))
    (hv : Summable (fun n => ‖value (v n)‖ ^ 2))
    (hd : ∀ b, Summable (fun n => ‖derivative b (v n)‖ ^ 2))
    (d : Fin 3 → ℕ → L2 H (Fin N × Fin 3))
    (hcov : ∀ b, Summable (fun n => ‖d b n‖ ^ 2)) (b : Fin 3)
    (a : PhysicalPairSpace.Position → ℝ) (ha : AEStronglyMeasurable a volume)
    (hi : Integrable (fun y => a y ^ 2 *
      PhysicalElectronicDensity.density (ensemble (fun n => value (v n)) hv) y)) :
    Integrable (fun y => a y * currentL1 (ofEnsemble i v hv hd d hcov) y b) ∧
      HasSum (fun n => (N : ℝ) * ∫ z, a (SymmetricLift.particle z i) *
        (inner ℂ (value (v n) z) (d b n z)).re)
        (∫ y, a y * currentL1 (ofEnsemble i v hv hd d hcov) y b) := by
  have hdensity := PhysicalWeightedDensity.density_weighted
    (ensemble (fun n => value (v n)) hv) (fun y => a y ^ 2) (ha.pow 2)
    (fun y => sq_nonneg _) hi
  have ham := PhysicalElectronicDensity.particle_test_measurable i a ha
  have hi' : Integrable (fun z => a (SymmetricLift.particle z i) ^ 2 *
      ‖ensemble (fun n => value (v n)) hv z‖ ^ 2) := by
    apply hdensity.1.mono' ((ham.pow 2).mul
      ((Lp.aestronglyMeasurable (ensemble (fun n => value (v n)) hv)).norm.pow 2))
    filter_upwards [] with z
    change ‖a (SymmetricLift.particle z i) ^ 2 *
      ‖ensemble (fun n => value (v n)) hv z‖ ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => sq_nonneg (a (SymmetricLift.particle z j)))
        (Finset.mem_univ i)) (sq_nonneg _)
  have hc := weighted_re_inner_integrable (ensemble (fun n => value (v n)) hv)
    (ensemble (d b) (hcov b)) (fun z => a (SymmetricLift.particle z i)) ham hi'
  have hp := PhysicalWeightedCurrentCore.tested_current_ofWaveFunction i (ensembleH1 v hv hd)
    (fun c => ensemble (d c) (hcov c)) b a hc
  have hs := PhysicalWeightedCurrentCore.ensemble_tested_re_inner_hasSum (fun n => value (v n)) (d b) hv (hcov b)
    (fun z => a (SymmetricLift.particle z i)) ham hi'
  refine ⟨hp.1, ?_⟩
  have hsum := hs.mul_left (N : ℝ)
  exact (congrArg (fun r : ℝ => HasSum (fun n => (N : ℝ) * ∫ z,
    a (SymmetricLift.particle z i) * (inner ℂ (value (v n) z) (d b n z)).re) r) hp.2).mpr hsum

end GptLean.PhysicalWeightedCurrentCore

namespace GptLean.PhysicalPFSource

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalSourceCoordinates PhysicalPairSpace
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true

variable {N : ℕ} (C : CanonicalSectorCCR photonMeasure)
  (M : ℝ) (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)
  (i : Fin N) (W : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (k : (Fin N × Fin 3) → PhysicalPFReference.Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hk : ∀ b, AEStronglyMeasurable (k b) volume)
  (hb : ∀ b, ∀ᵐ z ∂volume, ‖k b z‖ ≤ M)

variable {B}

/-- Exact current work against an unbounded velocity test on an actual
finite-energy normal source. -/
theorem Source.pair_tested_current_weighted {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : Source (Fin N × Fin 3) W B x)
    (hx : x ∈ (B.realization (WaveSpace (Fin N × Fin 3))).rank.positive)
    (he : (normalEnergy (Fin N × Fin 3) W C k hk M hb B S e).expectation x < ⊤)
    (b : Fin 3) (a : PhysicalPairSpace.Position → ℝ) (ha : AEStronglyMeasurable a volume)
    (hi : Integrable (fun y => a y ^ 2 * PhysicalNormalElectronicDensity.density B.normal x y)) :
    Integrable (fun y => a y * currentL1 (s.pair C M S e i W k hk hb he) y b) ∧
      HasSum (fun n => (N : ℝ) * ∫ z, a (SymmetricLift.particle z i) *
        (inner ℂ (inclusion (Fin N × Fin 3) W (s.vector n) z)
          (covariant (Fin N × Fin 3) W C k hk M hb e (i, b) (s.vector n) z)).re)
        (∫ y, a y * currentL1 (s.pair C M S e i W k hk hb he) y b) := by
  have hdensity := PhysicalNormalElectronicDensity.density_eq_spectral B.normal
    (B.realization (WaveSpace (Fin N × Fin 3))).functional hx
    (fun n => inclusion (Fin N × Fin 3) W (s.vector n)) s.hasSum
  have hi' : Integrable (fun y => a y ^ 2 * PhysicalElectronicDensity.density
      (PhysicalEnsembleSource.ensemble (fun n => inclusion (Fin N × Fin 3) W (s.vector n))
        s.mass_hasSum.summable) y) := by
    simpa only [hdensity] using hi
  exact PhysicalWeightedCurrentCore.tested_current_ofEnsemble i
    (fun n => ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) W (s.vector n)))
    s.mass_hasSum.summable
    (fun q => s.operator_summable C k hk M hb S e he (ordinary (Fin N × Fin 3) W q))
    (fun c n => covariant (Fin N × Fin 3) W C k hk M hb e (i, c) (s.vector n))
    (fun c => s.operator_summable C k hk M hb S e he
      (covariant (Fin N × Fin 3) W C k hk M hb e (i, c))) b a ha hi'

end GptLean.PhysicalPFSource
