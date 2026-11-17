import PfHk.PhysicalZeroCouplingCounterexample
import PfHk.CounterexampleRegularity

/-! The full zero-coupling counterexample. An explicit normalized physical
state is the unique ground state up to phase for the whole family, with
identical density/current data and pairwise gauge-inequivalent potentials. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.PhysicalZeroCouplingCounterexample

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalGroundState
  GptLean.PhysicalPolarization GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms
  GptLean.PhysicalPairSpace PfHk.PhysicalFermionicCoefficients

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

local instance endpointPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  CounterexampleSpectral.photonRealInner

/-- `prop-zero-coupling-counterexample`, including uniqueness, the explicit
wave and data, all stated density moments, local coefficient regularity,
and gauge inequivalence of the actual potential classes. Standard radial
and spherical-harmonic calculus and the inherited Fock background remain
explicit inputs. None assumes a counterexample ground-state conclusion. -/
theorem counterexample (F : Frame) (χ : ArticleCutoff)
    (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
    (S : StandardClosedFormBackground)
    (D : CounterexampleSpectral.StandardSphericalDecomposition)
    (O : CounterexampleSpectral.StandardRadialWeakODE (E := PhotonFock))
    (BF : StandardSymmetricFockExponential) (Z : ℝ) (hZ : 0 < Z) :
    ∃ p : State F χ C B S 0 (N := 1),
      (p.val =ᵐ[volume] fun X =>
        (HydrogenOrbital.orbital Z (SymmetricLift.particle X 0) : ℂ) • PhysicalFullVacuum.vacuum) ∧
      (∀ t : ℝ, |t| < 1 →
        IsGroundState (0 : Fin 1) F χ C B S 0 (potentials Z t) p ∧
        shiftedEnergy (0 : Fin 1) F χ C B S 0 (potentials Z t) p = -(Z ^ 2 / 2) ∧
        ∀ q : State F χ C B S 0 (N := 1),
          IsGroundState (0 : Fin 1) F χ C B S 0 (potentials Z t) q →
          ∃ c : ℂ, ‖c‖ = 1 ∧ q.val = c • p.val) ∧
      (densityL1 ((model (0 : Fin 1) F χ C B S 0).density p) =ᵐ[volume]
        HydrogenOrbital.density Z) ∧
      (currentL1 ((model (0 : Fin 1) F χ C B S 0).density p) =ᵐ[volume] 0) ∧
      (∀ α : ℝ, α < 2 * Z → Integrable (fun x => Real.exp (α * ‖x‖) *
        densityL1 ((model (0 : Fin 1) F χ C B S 0).density p) x) volume) ∧
      (∀ t : ℝ, Nonempty (Regularity (CounterexamplePotentials.vector t)
        (CounterexamplePotentials.scalar Z t))) ∧
      (∀ s t : ℝ, s ≠ t →
        ¬ ((CounterexamplePotentials.vector s).val =ᵐ[volume]
          (CounterexamplePotentials.vector t).val) ∧
        ¬ CounterexampleMagneticField.IsDistributionalGradient
          (fun x => (CounterexamplePotentials.vector t).val x -
            (CounterexamplePotentials.vector s).val x) ∧
        ∀ x, CounterexampleField.curl (CounterexampleField.vectorPotential s) x ≠
          CounterexampleField.curl (CounterexampleField.vectorPotential t) x) := by
  refine ⟨CounterexampleVacuumState.state F χ C B S Z hZ,
    CounterexampleVacuumState.reference_value_ae Z hZ, ?_,
    state_density F χ C B S Z hZ, state_current F χ C B S Z hZ,
    (fun α hα => state_exponential_moment F χ C B S Z hZ hα),
    (fun t => ⟨CounterexamplePotentials.regularity Z t⟩), ?_⟩
  · intro t ht
    exact ⟨ground_state F χ C B S D Z hZ ht, state_energy F χ C B S Z hZ t,
      fun q hq => unique_ground_state F χ C B S D O BF Z hZ ht q hq⟩
  · intro s t hst
    exact ⟨CounterexamplePotentials.vector_not_ae_eq hst,
      CounterexamplePotentials.not_distributional_gauge_equivalent hst,
      CounterexampleMagneticField.distinct_curls_at hst⟩

end PfHk.PhysicalZeroCouplingCounterexample

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
