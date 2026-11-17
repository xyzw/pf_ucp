import PfHk.PhysicalFermionicAverage

/-! The finite reference antisymmetrizer is the restriction of the existing
orthogonal fermionic projection on the physical L2 wave space. Thus that
projection preserves the actual common reference form domain. -/

noncomputable section
namespace PfHk.PhysicalFermionicProjection

open GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PhysicalFermionicAverage PfHk.PhysicalReferencePermutation
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

attribute [local irreducible] inclusion PhysicalPFReference.referenceSubspace
  PhysicalReferencePermutation.permutation

variable {N : ℕ}

local instance referenceAddCommGroup : AddCommGroup (Ref N) :=
  PhysicalFermionicAverage.referenceAddCommGroup

local instance referenceModule : Module ℂ (Ref N) :=
  PhysicalFermionicAverage.referenceModule

def waveAction (π : Perm N) : WaveSpace (Fin N × Fin 3) →ₗ[ℂ]
    WaveSpace (Fin N × Fin 3) := (pull (Q := PhotonFock) π).toLinearMap

def waveTwisted (π : Perm N) : WaveSpace (Fin N × Fin 3) →ₗ[ℂ]
    WaveSpace (Fin N × Fin 3) :=
  SignTwistedReduction.twist (G := Perm N) (Q := WaveSpace (Fin N × Fin 3))
    (waveAction (N := N)) (sign (N := N)) π

def waveAverage : WaveSpace (Fin N × Fin 3) →ₗ[ℂ] WaveSpace (Fin N × Fin 3) :=
  FiniteFormReduction.average (G := Perm N) (Q := WaveSpace (Fin N × Fin 3))
    (waveTwisted (N := N))

theorem waveTwisted_mul (π σ : Perm N) (u : WaveSpace (Fin N × Fin 3)) :
    waveTwisted (N := N) π (waveTwisted (N := N) σ u) =
      waveTwisted (N := N) (σ * π) u :=
  SignTwistedReduction.twist_mul (G := Perm N) (Q := WaveSpace (Fin N × Fin 3))
    (waveAction (N := N)) (sign (N := N))
    (fun π σ u => pull_pull π σ u) (sign_mul (N := N)) π σ u

theorem wave_fixed_iff (u : WaveSpace (Fin N × Fin 3)) :
    u ∈ FiniteFormReduction.fixed (G := Perm N) (Q := WaveSpace (Fin N × Fin 3))
      (waveTwisted (N := N)) ↔
      u ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock :=
  SignTwistedReduction.fixed_iff (G := Perm N) (Q := WaveSpace (Fin N × Fin 3))
    (waveAction (N := N)) (sign (N := N)) (sign_square (N := N)) u

theorem waveAverage_mem (u : WaveSpace (Fin N × Fin 3)) :
    waveAverage (N := N) u ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock :=
  (wave_fixed_iff _).mp
    (FiniteFormReduction.average_fixed (G := Perm N) (Q := WaveSpace (Fin N × Fin 3))
      (waveTwisted (N := N)) (waveTwisted_mul (N := N)) u)

theorem wave_mass_average {u : WaveSpace (Fin N × Fin 3)}
    (hu : u ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
    (v : WaveSpace (Fin N × Fin 3)) : ⟪waveAverage (N := N) v, u⟫_ℂ = ⟪v, u⟫_ℂ :=
  FiniteFormReduction.mass_average (G := Perm N) (Q := WaveSpace (Fin N × Fin 3))
    (H := WaveSpace (Fin N × Fin 3)) (waveTwisted (N := N)) (LinearMap.id :
    WaveSpace (Fin N × Fin 3) →ₗ[ℂ] WaveSpace (Fin N × Fin 3))
    (SignTwistedReduction.mass_invariant (G := Perm N) (Q := WaveSpace (Fin N × Fin 3))
      (H := WaveSpace (Fin N × Fin 3)) (waveAction (N := N)) (sign (N := N))
      (sign_square (N := N)) (sign_star (N := N))
      LinearMap.id (fun π v w => (pull (Q := PhotonFock) π).inner_map_map v w))
    ((wave_fixed_iff u).mpr hu) v

theorem waveAverage_eq_projection (u : WaveSpace (Fin N × Fin 3)) :
    waveAverage (N := N) u = PhysicalElectronicFermions.projection N PhotonFock u := by
  symm
  apply (PhysicalElectronicFermions.fermionicSubspace N PhotonFock).eq_starProjection_of_mem_of_inner_eq_zero
    (waveAverage_mem u)
  intro w hw
  exact (inner_sub_left u (waveAverage u) w).trans
    ((congrArg (fun z : ℂ => ⟪u, w⟫_ℂ - z) (wave_mass_average hw u)).trans
      (sub_self _))

private theorem average_intertwines {G Q Q' : Type*} [Group G] [Fintype G]
    [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q']
    (ρ : G → Q →ₗ[ℂ] Q) (σ : G → Q' →ₗ[ℂ] Q') (L : Q →ₗ[ℂ] Q')
    (h : ∀ g v, L (ρ g v) = σ g (L v)) (v : Q) :
    L (FiniteFormReduction.average ρ v) = FiniteFormReduction.average σ (L v) := by
  simp only [FiniteFormReduction.average_apply, map_smul, map_sum, h]

private theorem twist_intertwines {G Q Q' : Type*} [Group G] [Fintype G]
    [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q']
    (T : G → Q →ₗ[ℂ] Q) (U : G → Q' →ₗ[ℂ] Q') (s : G → ℂ)
    (L : Q →ₗ[ℂ] Q') (h : ∀ g v, L (T g v) = U g (L v)) (g : G) (v : Q) :
    L (SignTwistedReduction.twist T s g v) =
      SignTwistedReduction.twist U s g (L v) := by
  simp only [SignTwistedReduction.twist_apply, map_smul, h]

theorem inclusion_antisymmetrize (u : Ref N) :
    inclusion (Fin N × Fin 3) (fun _ => 0) (antisymmetrize (N := N) u) =
      PhysicalElectronicFermions.projection N PhotonFock
        (inclusion (Fin N × Fin 3) (fun _ => 0) u) := by
  have h := average_intertwines (G := Perm N) (Q := Ref N)
    (Q' := WaveSpace (Fin N × Fin 3)) (twisted (N := N)) (waveTwisted (N := N))
    (inclusion (Fin N × Fin 3) (fun _ => 0)).toLinearMap
    (twist_intertwines (G := Perm N) (Q := Ref N) (Q' := WaveSpace (Fin N × Fin 3))
      (permutation (N := N)) (waveAction (N := N)) (sign (N := N))
      (inclusion (Fin N × Fin 3) (fun _ => 0)).toLinearMap
      (fun π v => inclusion_permutation π v)) u
  exact h.trans (waveAverage_eq_projection _)

theorem projection_preserves_reference (u : Ref N) :
    ∃ v : Ref N, inclusion (Fin N × Fin 3) (fun _ => 0) v =
      PhysicalElectronicFermions.projection N PhotonFock
        (inclusion (Fin N × Fin 3) (fun _ => 0) u) :=
  ⟨antisymmetrize u, inclusion_antisymmetrize u⟩

end PfHk.PhysicalFermionicProjection
