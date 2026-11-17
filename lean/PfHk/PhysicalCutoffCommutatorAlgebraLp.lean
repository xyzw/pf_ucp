import PfHk.PhysicalCutoffMultiplier
import PfHk.PhysicalCutoffCommutatorAlgebra

/-! L2 versions of the cutoff identities. Selecting scalar instances with
an abstract Hilbert fiber avoids repeatedly normalizing the concrete Fock
space while applying the identities to physical reference vectors. -/

noncomputable section
namespace PfHk.PhysicalCutoffCommutator

open MeasureTheory GptLean.ElectronicH1Multiplier GptLean.ElectronicH1Space
open scoped InnerProductSpace

set_option maxHeartbeats 20000
set_option Elab.async false

variable {I H : Type} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def singleCutoffError (a : TwiceDifferentiableMultiplier I) (i : I) (u du : L2 H I) : L2 H I :=
  (-Complex.I) • (a.derivative i).multiplier du +
    (-(1 / 2) : ℂ) • (a.derivative i).derivativeMultiplier i u

def scalarCommutator (a : TwiceDifferentiableMultiplier I) (u : L2 H I) (D : I → L2 H I) : L2 H I :=
  ∑ i, singleCutoffError a i u (D i)

omit [CompleteSpace H] in
theorem inner_scalarCommutator (a : TwiceDifferentiableMultiplier I)
    (v u : L2 H I) (D : I → L2 H I) :
    ⟪v, scalarCommutator a u D⟫_ℂ = ∑ i, ⟪v, singleCutoffError a i u (D i)⟫_ℂ := by
  simp only [scalarCommutator, inner_sum]

omit [DecidableEq I] in
theorem half_sum_form (p q : I → ℂ) (r₁ r₂ r₃ r₄ k : ℂ) (hk : k = ∑ i, q i) :
    (1 / 2 : ℂ) * (∑ i, (p i + 2 * q i)) + r₁ + r₂ + r₃ - r₄ =
      ((1 / 2 : ℂ) * (∑ i, p i) + r₁ + r₂ + r₃ - r₄) + k := by
  rw [hk, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

omit [CompleteSpace H] in
theorem scalar_multiplier_pair (a : DifferentiableMultiplier I)
    (x y x' y' : L2 H I)
    (hx : x' = a.multiplier x) (hy : y' = a.multiplier y) :
    ⟪x, y'⟫_ℂ = ⟪x', y⟫_ℂ :=
  (congrArg (fun z : L2 H I => ⟪x, z⟫_ℂ) hy).trans
    ((a.multiplier_symmetric x y).trans
      (congrArg (fun z : L2 H I => ⟪z, y⟫_ℂ) hx).symm)

theorem scalar_cutoff_kinetic (a : TwiceDifferentiableMultiplier I) (i : I)
    (pu pv du dv duη dvη derivativeImage derivativeValue : L2 H I)
    (huη : duη = a.scalar.multiplier du + (-Complex.I) • a.scalar.derivativeMultiplier i pu)
    (hvη : dvη = a.scalar.multiplier dv + (-Complex.I) • a.scalar.derivativeMultiplier i pv)
    (hderivative : derivativeImage = (a.derivative i).multiplier du +
      (-Complex.I) • (a.derivative i).derivativeMultiplier i pu)
    (hvalue : derivativeValue = (a.derivative i).multiplier pu)
    (hsym : ⟪pv, derivativeImage⟫_ℂ = ⟪dv, derivativeValue⟫_ℂ) :
    ⟪dv, duη⟫_ℂ = ⟪dvη, du⟫_ℂ + 2 * ⟪pv, singleCutoffError a i pu du⟫_ℂ := by
  let L := a.scalar.multiplier (H := H)
  let B := (a.derivative i).multiplier (H := H)
  let B₂ := (a.derivative i).derivativeMultiplier (H := H) i
  have huη' : duη = L du + (-Complex.I) • B pu := huη.trans
    (congrArg (fun z : L2 H I => L du + (-Complex.I) • z) (derivative_multiplier a i pu).symm)
  have hvη' : dvη = L dv + (-Complex.I) • B pv := hvη.trans
    (congrArg (fun z : L2 H I => L dv + (-Complex.I) • z) (derivative_multiplier a i pv).symm)
  have hcov : ⟪pv, B du + (-Complex.I) • B₂ pu⟫_ℂ = ⟪dv, B pu⟫_ℂ :=
    (congrArg (fun z : L2 H I => ⟪pv, z⟫_ℂ) hderivative).symm.trans
      (hsym.trans (congrArg (fun z : L2 H I => ⟪dv, z⟫_ℂ) hvalue))
  have h := cutoff_kinetic_pair L B B₂ a.scalar.multiplier_symmetric
    (a.derivative i).multiplier_symmetric pu pv du dv hcov
  exact (congrArg (fun z : L2 H I => ⟪dv, z⟫_ℂ) huη').trans
    (h.trans (congrArg (fun z : L2 H I => ⟪z, du⟫_ℂ +
      2 * ⟪pv, (-Complex.I) • B du + (-(1 / 2) : ℂ) • B₂ pu⟫_ℂ) hvη').symm)

end PfHk.PhysicalCutoffCommutator
