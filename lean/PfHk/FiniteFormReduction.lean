import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

/-! Finite averaging extends an eigenvalue equation from an invariant
subspace to all form tests. The physical permutation action and its form
invariance are supplied by separate proved constructions. -/

noncomputable section
namespace PfHk.FiniteFormReduction

open scoped BigOperators InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 40000

variable {G Q : Type*} [Group G] [Fintype G]
  [AddCommGroup Q] [Module ℂ Q]

/-- The average of a finite linear anti-action. A sign twist makes its
fixed vectors precisely the fermionic vectors in the physical application. -/
def average (ρ : G → Q →ₗ[ℂ] Q) : Q →ₗ[ℂ] Q :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g

@[simp] theorem average_apply (ρ : G → Q →ₗ[ℂ] Q) (v : Q) :
    average ρ v = (Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g v := by
  simp only [average, LinearMap.smul_apply, LinearMap.sum_apply]

theorem card_ne_zero : (Fintype.card G : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

def fixed (ρ : G → Q →ₗ[ℂ] Q) : Submodule ℂ Q where
  carrier := {u | ∀ g, ρ g u = u}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv g; simp only [map_add, hu g, hv g]
  smul_mem' := by intro c u hu g; simp only [map_smul, hu g]

theorem average_fixed (ρ : G → Q →ₗ[ℂ] Q)
    (hρ : ∀ g h v, ρ g (ρ h v) = ρ (h * g) v) (v : Q) :
    average ρ v ∈ fixed ρ := by
  intro h
  simp only [average_apply, map_smul, map_sum, hρ]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun _ => rfl)

theorem average_eq_self (ρ : G → Q →ₗ[ℂ] Q) {v : Q} (hv : v ∈ fixed ρ) :
    average ρ v = v := by
  have hfix : ∀ g, ρ g v = v := hv
  simp only [average_apply, hfix, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (card_ne_zero (G := G)), one_smul]

theorem semilinear_average (ρ : G → Q →ₗ[ℂ] Q)
    (f : Q →ₗ⋆[ℂ] ℂ) (hf : ∀ g v, f (ρ g v) = f v) (v : Q) :
    f (average ρ v) = f v := by
  rw [average_apply, map_smulₛₗ, map_sum]
  simp only [hf, Finset.sum_const, Finset.card_univ, map_inv₀, map_natCast]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (card_ne_zero (G := G)), one_smul]

def leftForm (q : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ) (u : Q) : Q →ₗ⋆[ℂ] ℂ where
  toFun v := q v u
  map_add' v w := by simp only [map_add, LinearMap.add_apply]
  map_smul' c v := by simp only [map_smulₛₗ, LinearMap.smul_apply]

theorem form_average (ρ : G → Q →ₗ[ℂ] Q)
    (q : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ)
    (hq : ∀ g v w, q (ρ g v) (ρ g w) = q v w)
    {u : Q} (hu : u ∈ fixed ρ) (v : Q) : q (average ρ v) u = q v u := by
  apply semilinear_average ρ (leftForm q u) _ v
  intro g w
  exact (congrArg (fun z : Q => q (ρ g w) z) (hu g)).symm.trans (hq g w u)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def massLeft (L : Q →ₗ[ℂ] H) (u : Q) : Q →ₗ⋆[ℂ] ℂ where
  toFun v := ⟪L v, L u⟫_ℂ
  map_add' v w := by simp only [map_add, inner_add_left]
  map_smul' c v := by simp only [map_smul, inner_smul_left, smul_eq_mul]

theorem mass_average (ρ : G → Q →ₗ[ℂ] Q) (L : Q →ₗ[ℂ] H)
    (hL : ∀ g v w, ⟪L (ρ g v), L (ρ g w)⟫_ℂ = ⟪L v, L w⟫_ℂ)
    {u : Q} (hu : u ∈ fixed ρ) (v : Q) :
    ⟪L (average ρ v), L u⟫_ℂ = ⟪L v, L u⟫_ℂ := by
  apply semilinear_average ρ (massLeft L u) _ v
  intro g w
  exact (congrArg (fun z : Q => ⟪L (ρ g w), L z⟫_ℂ) (hu g)).symm.trans (hL g w u)

/-- The restricted weak eigenvalue equation extends to every form vector.
No differentiability or spectral assertion is hidden in this algebraic step. -/
theorem full_weak_of_fixed_weak (ρ : G → Q →ₗ[ℂ] Q)
    (hρ : ∀ g h v, ρ g (ρ h v) = ρ (h * g) v)
    (L : Q →ₗ[ℂ] H)
    (hL : ∀ g v w, ⟪L (ρ g v), L (ρ g w)⟫_ℂ = ⟪L v, L w⟫_ℂ)
    (q : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ)
    (hq : ∀ g v w, q (ρ g v) (ρ g w) = q v w)
    {u : Q} (hu : u ∈ fixed ρ) (E : ℝ)
    (heigen : ∀ v ∈ fixed ρ, q v u = (E : ℂ) * ⟪L v, L u⟫_ℂ) :
    ∀ v : Q, q v u = (E : ℂ) * ⟪L v, L u⟫_ℂ := by
  intro v
  exact (form_average ρ q hq hu v).symm.trans
    ((heigen (average ρ v) (average_fixed ρ hρ v)).trans
      (congrArg ((E : ℂ) * ·) (mass_average ρ L hL hu v)))

end PfHk.FiniteFormReduction
