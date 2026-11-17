import PfHk.PhysicalShiftedFormEnergyFubini

/-! Integrable tests of the actual physical particle pair. -/

noncomputable section
namespace PfHk.PhysicalParticleFubini

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift GptLean.PhysicalPairSpace GptLean.PhysicalPFParticle
open scoped InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable {N : ℕ} (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M)
  (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)

theorem density (i : Fin N) (e : ℝ) (u : Reference (Fin N × Fin 3) V)
    (hu : inclusion (Fin N × Fin 3) V u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
    (f : PhysicalPairSpace.Position → ℝ)
    (hi : ∀ n : Fin N, Integrable (fun X => f (particle X n) *
      ‖inclusion (Fin N × Fin 3) V u X‖ ^ 2) volume) :
    (∫ x, f x * densityL1 (PhysicalPFParticle.pair (N := N) C K hK M hM V i e u) x) =
      ∫ X, (∑ n : Fin N, f (particle X n)) *
        ‖inclusion (Fin N × Fin 3) V u X‖ ^ 2 :=
  PhysicalShiftedFormEnergyFubini.fermionic_density (N := N) (H := PhotonFock)
    i (electronic (Fin N × Fin 3) V u) hu
    (fun b => covariant (Fin N × Fin 3) V C (particleKernel K)
      (particleKernel_measurable K hK) M (particleKernel_bound K M hM) e (i, b) u) f hi

theorem current (i : Fin N) (e : ℝ) (u : Reference (Fin N × Fin 3) V)
    (hu : inclusion (Fin N × Fin 3) V u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
    (b : Fin 3) (f : PhysicalPairSpace.Position → ℝ)
    (hi : ∀ n : Fin N, Integrable (fun X => f (particle X n) *
      (⟪inclusion (Fin N × Fin 3) V u X,
        covariant (Fin N × Fin 3) V C (particleKernel K)
          (particleKernel_measurable K hK) M (particleKernel_bound K M hM) e (n, b) u X⟫_ℂ).re)
      volume) :
    (∫ x, f x * currentL1 (PhysicalPFParticle.pair (N := N) C K hK M hM V i e u) x b) =
      ∫ X, ∑ n : Fin N, f (particle X n) *
        (⟪inclusion (Fin N × Fin 3) V u X,
          covariant (Fin N × Fin 3) V C (particleKernel K)
            (particleKernel_measurable K hK) M (particleKernel_bound K M hM) e (n, b) u X⟫_ℂ).re :=
  PhysicalShiftedFormEnergyFubini.fermionic_current (N := N) (H := PhotonFock)
    i (electronic (Fin N × Fin 3) V u) hu
    (fun q => covariant (Fin N × Fin 3) V C (particleKernel K)
      (particleKernel_measurable K hK) M (particleKernel_bound K M hM) e q u)
    (covariant_covariance C K hK M hM V e u hu) b f hi

end PfHk.PhysicalParticleFubini
