import PfHk.PhysicalCutoffMultiplier

/-! Ordinary scalar L² algebra and approximation data with an arbitrary
complex Hilbert fibre. -/

noncomputable section
namespace PfHk.ExternalScalarApproximation

open MeasureTheory Filter GptLean.ElectronicH1Space GptLean.ElectronicH1Multiplier
open scoped InnerProductSpace Topology

set_option Elab.async false
set_option maxHeartbeats 20000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem square_pair {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (a : X → ℝ) (u v au av aau : Lp H 2 μ)
    (hu : au =ᵐ[μ] fun x => a x • u x)
    (hv : av =ᵐ[μ] fun x => a x • v x)
    (hs : aau =ᵐ[μ] fun x => a x ^ 2 • u x) :
    ⟪av, au⟫_ℂ = ⟪v, aau⟫_ℂ := by
  apply PhysicalCutoffCommutator.l2_inner_eq_of_ae
  filter_upwards [hu, hv, hs] with x hx hy hz
  rw [hx, hy, hz]
  simp only [inner_smul_left_eq_smul, inner_smul_right_eq_smul, smul_smul, pow_two]

theorem covariant_pair (jv du dv mju mjv mdu dmju b : H)
    (hsymmetric : ⟪jv, dmju⟫_ℂ = ⟪dv, mju⟫_ℂ)
    (hproduct : dmju = mdu + (-Complex.I) • b)
    (hmultiplier : ⟪jv, mdu⟫_ℂ = ⟪mjv, du⟫_ℂ) :
    ⟪dv, mju⟫_ℂ = ⟪mjv, du⟫_ℂ - Complex.I * ⟪jv, b⟫_ℂ := by
  rw [hproduct, inner_add_right, inner_smul_right, hmultiplier] at hsymmetric
  exact hsymmetric.symm.trans (by ring)

theorem sum_covariant_pair {I : Type*} [Fintype I]
    (v : H) (du dv au av b : I → H)
    (h : ∀ i, ⟪dv i, au i⟫_ℂ = ⟪av i, du i⟫_ℂ - Complex.I * ⟪v, b i⟫_ℂ) :
    (∑ i, ⟪dv i, au i⟫_ℂ) = (∑ i, ⟪av i, du i⟫_ℂ) - Complex.I * ⟪v, ∑ i, b i⟫_ℂ := by
  simp only [h, Finset.sum_sub_distrib, inner_sum, Finset.mul_sum]

variable [CompleteSpace H] {I : Type*} [Fintype I] [DecidableEq I]

structure Data (u v : L2 H I) (au av : I → L2 H I) (divu : L2 H I) where
  coefficient : ℕ → I → DifferentiableMultiplier I
  value_u : ∀ i, Tendsto (fun n => (coefficient n i).multiplier u) atTop (𝓝 (au i))
  value_v : ∀ i, Tendsto (fun n => (coefficient n i).multiplier v) atTop (𝓝 (av i))
  divergence_u : Tendsto (fun n => ∑ i, (coefficient n i).derivativeMultiplier i u)
    atTop (𝓝 divu)

end PfHk.ExternalScalarApproximation
