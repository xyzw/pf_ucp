import PfHk.FiniteFormReduction

/-! A real sign character converts a fermionic anti-action into an ordinary
fixed-vector problem. The finite-average reduction then applies directly. -/

noncomputable section
namespace PfHk.SignTwistedReduction

open scoped InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 30000

variable {G Q : Type*} [Group G] [Fintype G]
  [AddCommGroup Q] [Module ℂ Q]
  (T : G → Q →ₗ[ℂ] Q) (s : G → ℂ)

def twist (g : G) : Q →ₗ[ℂ] Q := s g • T g

@[simp] theorem twist_apply (g : G) (u : Q) : twist T s g u = s g • T g u := rfl

theorem twist_mul
    (hT : ∀ g h u, T g (T h u) = T (h * g) u)
    (hs : ∀ g h, s (g * h) = s g * s h) (g h : G) (u : Q) :
    twist T s g (twist T s h u) = twist T s (h * g) u := by
  simp only [twist_apply, map_smul, smul_smul, hT, hs]

theorem fixed_iff (hs : ∀ g, s g * s g = 1) (u : Q) :
    u ∈ FiniteFormReduction.fixed (twist T s) ↔ ∀ g, T g u = s g • u := by
  constructor
  · intro hu g
    have hh := congrArg (fun z : Q => s g • z) (hu g)
    simpa only [twist_apply, smul_smul, hs g, one_smul] using hh
  · intro hu g
    simp only [twist_apply, hu g, smul_smul, hs g, one_smul]

theorem form_invariant
    (hs : ∀ g, s g * s g = 1) (hstar : ∀ g, star (s g) = s g)
    (q : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ)
    (hq : ∀ g u v, q (T g u) (T g v) = q u v) (g : G) (u v : Q) :
    q (twist T s g u) (twist T s g v) = q u v := by
  have hconj (g : G) : starRingEnd ℂ (s g) = s g := hstar g
  simp only [twist_apply, map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply,
    smul_eq_mul, hconj, ← mul_assoc, hs, one_mul, hq]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem mass_invariant
    (hs : ∀ g, s g * s g = 1) (hstar : ∀ g, star (s g) = s g)
    (L : Q →ₗ[ℂ] H)
    (hL : ∀ g u v, ⟪L (T g u), L (T g v)⟫_ℂ = ⟪L u, L v⟫_ℂ)
    (g : G) (u v : Q) :
    ⟪L (twist T s g u), L (twist T s g v)⟫_ℂ = ⟪L u, L v⟫_ℂ := by
  have hconj (g : G) : starRingEnd ℂ (s g) = s g := hstar g
  simp only [twist_apply, map_smul, inner_smul_left, inner_smul_right,
    hconj, ← mul_assoc, hs, one_mul, hL]

/-- A weak equation tested only on sign-character vectors determines the
full weak equation when the actual mass and form are permutation invariant. -/
theorem full_weak_of_fermionic_weak
    (hT : ∀ g h u, T g (T h u) = T (h * g) u)
    (hsmul : ∀ g h, s (g * h) = s g * s h)
    (hs : ∀ g, s g * s g = 1) (hstar : ∀ g, star (s g) = s g)
    (L : Q →ₗ[ℂ] H)
    (hL : ∀ g u v, ⟪L (T g u), L (T g v)⟫_ℂ = ⟪L u, L v⟫_ℂ)
    (q : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ)
    (hq : ∀ g u v, q (T g u) (T g v) = q u v)
    {u : Q} (hu : ∀ g, T g u = s g • u) (E : ℝ)
    (heigen : ∀ v, (∀ g, T g v = s g • v) → q v u = (E : ℂ) * ⟪L v, L u⟫_ℂ) :
    ∀ v : Q, q v u = (E : ℂ) * ⟪L v, L u⟫_ℂ := by
  apply FiniteFormReduction.full_weak_of_fixed_weak (twist T s)
    (twist_mul T s hT hsmul) L (mass_invariant T s hs hstar L hL)
    q (form_invariant T s hs hstar q hq) ((fixed_iff T s hs u).mpr hu) E
  intro v hv
  exact heigen v ((fixed_iff T s hs v).mp hv)

end PfHk.SignTwistedReduction
