import PfHk.PhysicalShiftedScalarEnergy

/-! The literal external form energy equals the paper's shifted pair energy.
All unbounded multiplier and marginal identities are derived in the imports.
This module assembles those equalities without unfolding physical coordinates
inside the remaining scalar algebra. -/

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

noncomputable section
namespace PfHk.PhysicalShiftedFormEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPairSpace GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
open scoped ENNReal InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

attribute [local irreducible] inclusion covariant radiation potential roughMultiply
  PhysicalPFReference.referenceSubspace PhysicalReferenceCoulombEquiv.equiv
  scalarSum squareSum magneticSum externalEnergy energy

private theorem shift_reorder (s m a : ℝ) :
    (s + (1 / 2 : ℝ) * a) + m = s + m + (1 / 2 : ℝ) * a := by ring

private theorem energy_regroup (r s m a : ℝ) :
    r + s + m + (1 / 2 : ℝ) * a = r + (s + m + (1 / 2 : ℝ) * a) := by ring

variable {N : ℕ} (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M) (e : ℝ)

set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := N) K
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := N) K hK
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := N) K M hM

theorem shifted_pairing (i : Fin N) (A : VectorPotential) (v w : ScalarPotential)
    (hshift : (w.val : PhysicalSourceCoordinates.Position → ℝ) =ᵐ[volume]
      fun x => v.val x + (1 / 2 : ℝ) * ∑ b : Fin 3, A.val x b ^ 2)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : inclusion (Fin N × Fin 3) (fun _ => 0) u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    pairPotential (w, A) (PhysicalPFParticle.pair (N := N) C K hK M hM (fun _ => 0) i e u) =
      scalarSum (N := N) v u + magneticSum (N := N) C K hK M hM e A u +
        (1 / 2 : ℝ) * squareSum (N := N) A u := by
  have hp := congrArg₂ (fun a b : ℝ => a + b)
    (pairing_scalar (N := N) C K hK M hM e i w u hu)
    (pairing_vector (N := N) C K hK M hM e i A u hu)
  have hparts := (pairPotential_eq_parts w A
    (PhysicalPFParticle.pair (N := N) C K hK M hM (fun _ => 0) i e u)).trans hp
  exact hparts.trans ((congrArg (fun r : ℝ => r + magneticSum (N := N) C K hK M hM e A u)
    (scalarSum_shift (N := N) A v w hshift u)).trans
      (shift_reorder (scalarSum (N := N) v u)
        (magneticSum (N := N) C K hK M hM e A u) (squareSum (N := N) A u)))

theorem external_energy_eq_shifted_pair (i : Fin N) (A : VectorPotential) (v w : ScalarPotential)
    (hshift : (w.val : PhysicalSourceCoordinates.Position → ℝ) =ᵐ[volume]
      fun x => v.val x + (1 / 2 : ℝ) * ∑ b : Fin 3, A.val x b ^ 2)
    (c : ℝ) (hc : 0 ≤ c) (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : inclusion (Fin N × Fin 3) (fun _ => 0) u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    externalEnergy (I := Fin N × Fin 3) (fun _ => 0) C κP hκP M hbP e
      (vector A) (positive v c) (negative v c) u (externalDomain A v c hc u) =
      energy (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X)
        C κP hκP M hbP e (PhysicalReferenceCoulombEquiv.equiv (N := N) c hc u) +
      pairPotential (w, A) (PhysicalPFParticle.pair (N := N) C K hK M hM (fun _ => 0) i e u) := by
  let r := energy (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X)
    C κP hκP M hbP e (PhysicalReferenceCoulombEquiv.equiv (N := N) c hc u)
  exact (external_energy_expansion (N := N) C K hK M hM e A v c hc u).trans
    ((energy_regroup r (scalarSum (N := N) v u)
      (magneticSum (N := N) C K hK M hM e A u) (squareSum (N := N) A u)).trans
        (congrArg (fun s : ℝ => r + s)
          (shifted_pairing (N := N) C K hK M hM e i A v w hshift u hu).symm))

theorem pair_equiv (i : Fin N) (c : ℝ) (hc : 0 ≤ c)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    PhysicalPFParticle.pair (N := N) C K hK M hM
      (fun X => c * PhysicalCoulombH1.potential N X) i e
        (PhysicalReferenceCoulombEquiv.equiv (N := N) c hc u) =
      PhysicalPFParticle.pair (N := N) C K hK M hM (fun _ => 0) i e u := by
  apply congrArg₂ (fun (q : ElectronicGraph (Fin N × Fin 3))
    (d : Fin 3 → WaveSpace (Fin N × Fin 3)) => PhysicalSourcePair.ofWaveFunction i
      (ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Fin N × Fin 3) q) d)
    (PhysicalReferenceCoulombEquiv.electronic_equiv (N := N) c hc u)
  funext b
  exact PhysicalReferenceCoulombEquiv.covariant_equiv (N := N) C κP hκP M hbP c hc e u (i, b)

end PfHk.PhysicalShiftedFormEnergy

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
