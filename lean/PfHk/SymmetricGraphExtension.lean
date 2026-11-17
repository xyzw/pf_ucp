import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic

/-! Uniqueness of a symmetric extension from nonreal resolvent surjectivity.
This is the elementary operator-theory step that identifies a weak form
realization after Kato--Rellich has supplied a self-adjoint algebraic sum. -/

noncomputable section
namespace PfHk.SymmetricGraphExtension

open scoped InnerProductSpace

set_option maxHeartbeats 20000
set_option Elab.async false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def Symmetric (G : H → H → Prop) : Prop :=
  ∀ x y x' y', G x y → G x' y' → ⟪x, y'⟫_ℂ = ⟪y, x'⟫_ℂ

theorem shifted_pair_unique (G : H → H → Prop) (hG : Symmetric G)
    {x y x' y' : H} (h : G x y) (h' : G x' y')
    (heq : y + Complex.I • x = y' + Complex.I • x') : x = x' ∧ y = y' := by
  have hs : ⟪x - x', y - y'⟫_ℂ = ⟪y - y', x - x'⟫_ℂ := by
    simp only [inner_sub_left, inner_sub_right]
    rw [hG x y x y h h, hG x y x' y' h h', hG x' y' x y h' h,
      hG x' y' x' y' h' h']
  have hd : y - y' = (-Complex.I) • (x - x') := by
    have hh : y - y' = Complex.I • x' - Complex.I • x := by
      exact (sub_eq_sub_iff_add_eq_add).mpr (heq.trans (add_comm _ _))
    rw [hh, smul_sub, neg_smul, neg_smul]
    abel
  rw [hd, inner_smul_right, inner_smul_left] at hs
  have hi := congrArg Complex.im hs
  have hz : ‖x - x'‖ ^ 2 = 0 := by
    simp only [map_neg, Complex.conj_I, neg_neg, Complex.mul_im,
      Complex.neg_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      neg_mul, zero_add] at hi
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    change (⟪x - x', x - x'⟫_ℂ).re = 0
    nlinarith
  have hx : x = x' := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  exact ⟨hx, add_right_cancel (by simpa only [hx] using heq)⟩

/-- A symmetric graph with surjective resolvent has no proper symmetric
extension. No topology or physical parameters are involved. -/
theorem eq_of_resolvent_surjective (G E : H → H → Prop)
    (hE : Symmetric E) (hext : ∀ x y, G x y → E x y)
    (hres : ∀ z : H, ∃ x y, G x y ∧ y + Complex.I • x = z) :
    ∀ x y, E x y ↔ G x y := by
  intro x y
  constructor
  · intro hxy
    obtain ⟨x', y', hg, heq⟩ := hres (y + Complex.I • x)
    have hh := shifted_pair_unique E hE hxy (hext x' y' hg) heq.symm
    exact hh.1.symm ▸ hh.2.symm ▸ hg
  · exact hext x y

end PfHk.SymmetricGraphExtension
