import GptLean.PhysicalPFReference
import GptLean.PhysicalFermionicPair
import GptLean.PhysicalFockFieldPermutation
import GptLean.PhysicalFockSeparable

/-!
The common reference form with fields evaluated at actual particle
positions. Fermionic covariance of its covariant derivatives follows
from the proved weak-derivative and field permutation identities. The
resulting marginal pair therefore represents the summed particle tests.
-/

noncomputable section

namespace GptLean.PhysicalPFParticle

open MeasureTheory PhysicalFock PhysicalPFReference SymmetricLift
  PhysicalPairSpace PhysicalSourcePair

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable {N : ℕ} (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M)

def particleKernel (q : Fin N × Fin 3) (x : Configuration N) : WeightedPhotonKernel :=
  K (q.2, particle x q.1)

include hK in
theorem particleKernel_measurable (q : Fin N × Fin 3) :
    AEStronglyMeasurable (particleKernel K q) volume :=
  (hK.comp (continuous_const.prodMk
    (particleLinear q.1).continuous_of_finiteDimensional)).aestronglyMeasurable

include hM in
theorem particleKernel_bound (q : Fin N × Fin 3) :
    ∀ᵐ x ∂volume, ‖particleKernel K q x‖ ≤ M :=
  ae_of_all _ fun x => hM (q.2, particle x q.1)

variable (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)

theorem field_particle (q : Fin N × Fin 3) (u : Reference (Fin N × Fin 3) V) :
    field (Fin N × Fin 3) V C (particleKernel K) (particleKernel_measurable K hK)
      M (particleKernel_bound K M hM) q u =
      particleField C K hK M hM q.1 q.2 (radiationSource (Fin N × Fin 3) V u) := rfl

private theorem covariance_smul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (c : ℂ) (d : Fin N × Fin 3 → PhysicalElectronicFermions.FullSpace N H)
    (hd : ∀ (π : Equiv.Perm (Fin N)) (i : Fin N) (a : Fin 3),
      ∀ᵐ x ∂volume, d (i, a) (permuteConfiguration π x) =
        PhysicalElectronicFermions.signCharacter N π • d (π.symm i, a) x)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (a : Fin 3) :
    ∀ᵐ x ∂volume, (c • d (i, a) : PhysicalElectronicFermions.FullSpace N H)
        (permuteConfiguration π x) = PhysicalElectronicFermions.signCharacter N π •
        (c • d (π.symm i, a) : PhysicalElectronicFermions.FullSpace N H) x := by
  have hp := (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_smul c (d (i, a)))
  filter_upwards [hp, Lp.coeFn_smul c (d (π.symm i, a)), hd π i a] with x hp hs hd
  simp only [Function.comp_apply, Pi.smul_apply] at hp hs
  rw [hp, hd, hs, smul_comm c (PhysicalElectronicFermions.signCharacter N π)]

theorem covariant_covariance (e : ℝ) (u : Reference (Fin N × Fin 3) V)
    (hu : inclusion (Fin N × Fin 3) V u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (a : Fin 3) :
    ∀ᵐ x ∂volume,
      (covariant (Fin N × Fin 3) V C (particleKernel K) (particleKernel_measurable K hK)
        M (particleKernel_bound K M hM) e (i, a) u) (permuteConfiguration π x) =
      PhysicalElectronicFermions.signCharacter N π •
        (covariant (Fin N × Fin 3) V C (particleKernel K) (particleKernel_measurable K hK)
          M (particleKernel_bound K M hM) e (π.symm i, a) u) x := by
  have hr : spatialRadiationInclusion volume (radiationSource (Fin N × Fin 3) V u) ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock :=
    (congrArg (fun v : WaveSpace (Fin N × Fin 3) =>
      v ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
      (radiation_matches (Fin N × Fin 3) V u)).mpr hu
  have hf := covariance_smul (-(e : ℂ))
    (fun q => particleField C K hK M hM q.1 q.2 (radiationSource (Fin N × Fin 3) V u))
    (particleField_covariance C K hK M hM (radiationSource (Fin N × Fin 3) V u) hr)
  have h := PhysicalFermionicPair.covariance_add
    (fun q => (-Complex.I) • ordinary (Fin N × Fin 3) V q u)
    (fun q => (-(e : ℂ)) • particleField C K hK M hM q.1 q.2
      (radiationSource (Fin N × Fin 3) V u))
    (PhysicalFermionicPair.scaled_derivative_covariance (-Complex.I)
      (electronic (Fin N × Fin 3) V u) hu) hf π i a
  change ∀ᵐ x ∂volume,
    ((-Complex.I) • ordinary (Fin N × Fin 3) V (i, a) u -
      (e : ℂ) • particleField C K hK M hM i a (radiationSource (Fin N × Fin 3) V u))
        (permuteConfiguration π x) =
    PhysicalElectronicFermions.signCharacter N π •
      ((-Complex.I) • ordinary (Fin N × Fin 3) V (π.symm i, a) u -
        (e : ℂ) • particleField C K hK M hM (π.symm i) a
          (radiationSource (Fin N × Fin 3) V u)) x
  simpa only [sub_eq_add_neg, neg_smul] using h

/-- The physical combined-current pair for a vector on the common domain. -/
def pair (i : Fin N) (e : ℝ) (u : Reference (Fin N × Fin 3) V) : Pair :=
  ofWaveFunction i (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
    (fun a => covariant (Fin N × Fin 3) V C (particleKernel K)
      (particleKernel_measurable K hK) M (particleKernel_bound K M hM) e (i, a) u)

theorem pair_tested_current (i : Fin N) (e : ℝ) (u : Reference (Fin N × Fin 3) V)
    (hu : inclusion (Fin N × Fin 3) V u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
    (a : Fin 3) (f : PhysicalPairSpace.Position → ℝ) (hf : Measurable f)
    {b : ℝ} (hb : ∀ x, ‖f x‖ ≤ b) :
    (∫ x, f x * currentL1 (pair C K hK M hM V i e u) x a) =
      ∫ z, ∑ j : Fin N, f (particle z j) * PhysicalPairIntegrability.currentComponent
        (inclusion (Fin N × Fin 3) V u z)
        ((covariant (Fin N × Fin 3) V C (particleKernel K) (particleKernel_measurable K hK)
          M (particleKernel_bound K M hM) e (j, a) u) z) :=
  PhysicalFermionicPair.tested_current i (electronic (Fin N × Fin 3) V u) hu
    (fun q => covariant (Fin N × Fin 3) V C (particleKernel K) (particleKernel_measurable K hK)
      M (particleKernel_bound K M hM) e q u)
    (covariant_covariance C K hK M hM V e u hu) a f hf hb

theorem pair_tested_density (i : Fin N) (e : ℝ) (u : Reference (Fin N × Fin 3) V)
    (hu : inclusion (Fin N × Fin 3) V u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
    (f : PhysicalPairSpace.Position → ℝ) (hf : Measurable f)
    {b : ℝ} (hb : ∀ x, ‖f x‖ ≤ b) :
    (∫ x, f x * densityL1 (pair C K hK M hM V i e u) x) =
      ∫ z, (∑ j : Fin N, f (particle z j)) * ‖inclusion (Fin N × Fin 3) V u z‖ ^ 2 :=
  PhysicalFermionicPair.tested_density i (electronic (Fin N × Fin 3) V u) hu
    (fun a => covariant (Fin N × Fin 3) V C (particleKernel K) (particleKernel_measurable K hK)
      M (particleKernel_bound K M hM) e (i, a) u) f hf hb

end GptLean.PhysicalPFParticle
