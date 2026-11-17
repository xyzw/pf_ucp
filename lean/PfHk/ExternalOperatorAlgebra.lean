import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Continuous

/-! Hilbert-space algebra used by the external magnetic operator expansion. -/

noncomputable section
namespace PfHk.ExternalOperatorAlgebra

open Filter
open scoped InnerProductSpace Topology

set_option maxHeartbeats 20000
set_option Elab.async false

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype I]

theorem divergence_pair_limit (v div : H) (du dv au av : I → H)
    (uSeq vSeq : ℕ → I → H) (divSeq : ℕ → H)
    (hu : ∀ i, Tendsto (fun n => uSeq n i) atTop (𝓝 (au i)))
    (hv : ∀ i, Tendsto (fun n => vSeq n i) atTop (𝓝 (av i)))
    (hd : Tendsto divSeq atTop (𝓝 div))
    (heq : ∀ n, (∑ i, ⟪dv i, uSeq n i⟫_ℂ) =
      (∑ i, ⟪vSeq n i, du i⟫_ℂ) - Complex.I * ⟪v, divSeq n⟫_ℂ) :
    (∑ i, ⟪dv i, au i⟫_ℂ) =
      (∑ i, ⟪av i, du i⟫_ℂ) - Complex.I * ⟪v, div⟫_ℂ := by
  have hl : Tendsto (fun n => ∑ i, ⟪dv i, uSeq n i⟫_ℂ) atTop
      (𝓝 (∑ i, ⟪dv i, au i⟫_ℂ)) := tendsto_finsetSum Finset.univ
    (fun i _ => tendsto_const_nhds.inner (hu i))
  have hr : Tendsto (fun n => (∑ i, ⟪vSeq n i, du i⟫_ℂ) - Complex.I * ⟪v, divSeq n⟫_ℂ)
      atTop (𝓝 ((∑ i, ⟪av i, du i⟫_ℂ) - Complex.I * ⟪v, div⟫_ℂ)) := (tendsto_finsetSum Finset.univ
    (fun i _ => (hv i).inner tendsto_const_nhds)).sub
      (tendsto_const_nhds.mul (tendsto_const_nhds.inner hd))
  exact tendsto_nhds_unique hl (hr.congr fun n => (heq n).symm)

theorem magnetic_form_expansion (v div p n : H) (du dv au av first square : I → H)
    (r pp nn : ℂ)
    (hcross : (∑ i, ⟪dv i, au i⟫_ℂ) =
      (∑ i, ⟪av i, du i⟫_ℂ) - Complex.I * ⟪v, div⟫_ℂ)
    (hfirst : ∀ i, ⟪av i, du i⟫_ℂ = ⟪v, first i⟫_ℂ)
    (hsquare : ∀ i, ⟪av i, au i⟫_ℂ = ⟪v, square i⟫_ℂ)
    (hp : pp = ⟪v, p⟫_ℂ) (hn : nn = ⟪v, n⟫_ℂ) :
    (1 / 2 : ℂ) * (∑ i, ⟪dv i + av i, du i + au i⟫_ℂ) + r + pp - nn =
      ((1 / 2 : ℂ) * (∑ i, ⟪dv i, du i⟫_ℂ) + r) +
        ⟪v, (∑ i, first i) + (1 / 2 : ℂ) • (∑ i, square i) +
          (-Complex.I / 2) • div + p - n⟫_ℂ := by
  simp only [inner_add_left, inner_add_right, Finset.sum_add_distrib]
  rw [hcross]
  simp only [hfirst, hsquare, hp, hn, inner_sub_right, inner_add_right,
    inner_smul_right, inner_sum]
  ring

end PfHk.ExternalOperatorAlgebra
