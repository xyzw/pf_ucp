import PfHk.PhysicalReferencePermutation
import PfHk.SignTwistedReduction

/-! The finite signed antisymmetrizer acts on the actual free reference
domain and has precisely the existing fermionic L2 character. -/

noncomputable section
namespace PfHk.PhysicalFermionicAverage

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PhysicalReferencePermutation
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

attribute [local irreducible] inclusion PhysicalPFReference.referenceSubspace
  PhysicalReferencePermutation.permutation

variable {N : ℕ}

abbrev Perm (N : ℕ) := Equiv.Perm (Fin N)
abbrev Ref (N : ℕ) := Reference (Fin N × Fin 3) (fun _ => 0)

local instance referenceAddCommGroup : AddCommGroup (Ref N) :=
  (PhysicalPFReference.referenceSubspace (Fin N × Fin 3) (fun _ => 0)).addCommGroup

local instance referenceModule : Module ℂ (Ref N) :=
  (PhysicalPFReference.referenceSubspace (Fin N × Fin 3) (fun _ => 0)).module

local instance referenceSMul : SMul ℂ (Ref N) :=
  Submodule.smul (S := ℂ)
    (PhysicalPFReference.referenceSubspace (Fin N × Fin 3) (fun _ => 0))

abbrev sign (π : Perm N) : ℂ := PhysicalElectronicFermions.signCharacter N π

theorem sign_mul (π σ : Perm N) : sign (π * σ) = sign π * sign σ := by
  simp only [sign, PhysicalElectronicFermions.signCharacter, map_mul, Units.val_mul, Int.cast_mul]

theorem sign_square (π : Perm N) : sign π * sign π = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hp | hp <;>
    simp [sign, PhysicalElectronicFermions.signCharacter, hp]

theorem sign_star (π : Perm N) : star (sign π) = sign π := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hp | hp <;>
    simp [sign, PhysicalElectronicFermions.signCharacter, hp]

def fermionic : Submodule ℂ (Ref N) :=
  (PhysicalElectronicFermions.fermionicSubspace N PhotonFock).comap
    (inclusion (Fin N × Fin 3) (fun _ => 0)).toLinearMap

theorem mem_fermionic_iff (u : Ref N) :
    u ∈ fermionic (N := N) ↔
      ∀ π : Perm N, permutation (N := N) π u =
        @SMul.smul ℂ (Ref N) (referenceSMul (N := N)) (sign π) u := by
  constructor
  · intro hu π
    exact inclusion_injective (Fin N × Fin 3) (fun _ => 0)
      ((inclusion_permutation π u).trans ((hu π).trans
        (map_smul (inclusion (Fin N × Fin 3) (fun _ => 0)) (sign π) u).symm))
  · intro hu π
    exact (inclusion_permutation π u).symm.trans
      ((congrArg (inclusion (Fin N × Fin 3) (fun _ => 0)) (hu π)).trans
        (map_smul (inclusion (Fin N × Fin 3) (fun _ => 0)) (sign π) u))

def twisted (π : Perm N) : Ref N →ₗ[ℂ] Ref N :=
  SignTwistedReduction.twist (G := Perm N) (Q := Ref N)
    (permutation (N := N)) (sign (N := N)) π

def antisymmetrize : Ref N →ₗ[ℂ] Ref N :=
  FiniteFormReduction.average (G := Perm N) (Q := Ref N) (twisted (N := N))

theorem twisted_mul (π σ : Perm N) (u : Ref N) :
    twisted (N := N) π (twisted (N := N) σ u) = twisted (N := N) (σ * π) u :=
  SignTwistedReduction.twist_mul (G := Perm N) (Q := Ref N)
    (permutation (N := N)) (sign (N := N))
    (permutation_permutation (N := N)) (sign_mul (N := N)) π σ u

theorem fixed_iff (u : Ref N) :
    u ∈ FiniteFormReduction.fixed (G := Perm N) (Q := Ref N) (twisted (N := N)) ↔
      u ∈ fermionic (N := N) :=
  (SignTwistedReduction.fixed_iff (G := Perm N) (Q := Ref N)
    (permutation (N := N)) (sign (N := N)) (sign_square (N := N)) u).trans
    (mem_fermionic_iff u).symm

theorem antisymmetrize_fermionic (u : Ref N) :
    antisymmetrize (N := N) u ∈ fermionic (N := N) :=
  (fixed_iff _).mp (FiniteFormReduction.average_fixed (G := Perm N) (Q := Ref N)
    (twisted (N := N)) (twisted_mul (N := N)) u)

theorem antisymmetrize_eq_self {u : Ref N} (hu : u ∈ fermionic (N := N)) :
    antisymmetrize (N := N) u = u :=
  FiniteFormReduction.average_eq_self (G := Perm N) (Q := Ref N)
    (twisted (N := N)) ((fixed_iff u).mpr hu)

theorem mass_permutation (π : Perm N) (u v : Ref N) :
    ⟪inclusion (Fin N × Fin 3) (fun _ => 0) (permutation π u),
      inclusion (Fin N × Fin 3) (fun _ => 0) (permutation π v)⟫_ℂ =
    ⟪inclusion (Fin N × Fin 3) (fun _ => 0) u,
      inclusion (Fin N × Fin 3) (fun _ => 0) v⟫_ℂ :=
  (congrArg₂ (fun a b : WaveSpace (Fin N × Fin 3) => ⟪a, b⟫_ℂ)
    (inclusion_permutation π u) (inclusion_permutation π v)).trans
      ((pull (Q := PhotonFock) π).inner_map_map _ _)

theorem mass_antisymmetrize {u : Ref N} (hu : u ∈ fermionic) (v : Ref N) :
    ⟪inclusion (Fin N × Fin 3) (fun _ => 0) (antisymmetrize (N := N) v),
      inclusion (Fin N × Fin 3) (fun _ => 0) u⟫_ℂ =
    ⟪inclusion (Fin N × Fin 3) (fun _ => 0) v,
      inclusion (Fin N × Fin 3) (fun _ => 0) u⟫_ℂ :=
  FiniteFormReduction.mass_average (G := Perm N) (Q := Ref N)
    (H := WaveSpace (Fin N × Fin 3)) (twisted (N := N))
    (inclusion (Fin N × Fin 3) (fun _ => 0)).toLinearMap
    (SignTwistedReduction.mass_invariant (G := Perm N) (Q := Ref N)
      (H := WaveSpace (Fin N × Fin 3)) (permutation (N := N)) (sign (N := N))
      (sign_square (N := N)) (sign_star (N := N))
      (inclusion (Fin N × Fin 3) (fun _ => 0)).toLinearMap (mass_permutation (N := N)))
    ((fixed_iff u).mpr hu) v

end PfHk.PhysicalFermionicAverage
