import PfHk.PhysicalCoefficientLocality
import PfHk.PhysicalCutoffCommutator

/-! A cutoff constant near a vector's support acts as the identity and
has zero physical commutator on that vector. -/

noncomputable section
namespace PfHk.PhysicalCutoffLocality

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.ElectronicH1Multiplier PfHk.PhysicalLocalEnergy PfHk.PhysicalCutoffCommutator
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [local irreducible] inclusion covariant radiation potential roughMultiply
  externalCovariant PhysicalPFScalarMultiplier.multiply PhysicalPFReference.referenceSubspace
  DifferentiableMultiplier.multiplier DifferentiableMultiplier.derivativeMultiplier
  PfHk.PhysicalCutoffCommutator.commutator

private theorem lp_product_zero {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {μ : Measure X}
    (u : Lp H 2 μ) (b : X → ℝ) (hb : MemLp (fun x => b x • u x) 2 μ) (hu : u = 0) :
    hb.toLp (fun x => b x • u x) = 0 := by
  subst u
  have h0 : MemLp (0 : X → H) 2 μ := MemLp.zero
  have hzero : (fun x => b x • (0 : Lp H 2 μ) x) =ᵐ[μ] (0 : X → H) :=
    (Lp.coeFn_zero H 2 μ).mono fun x hx => by simp only [hx, Pi.zero_apply, smul_zero]
  exact (MemLp.toLp_congr hb h0 hzero).trans (MemLp.toLp_zero h0)

private theorem zero_add_product {H : Type*} [AddCommGroup H] [Module ℂ H]
    (a b : H) (h : 0 = a + (-Complex.I) • b) (hb : b = 0) : a = 0 := by
  simpa only [hb, smul_zero, add_zero] using h.symm

private theorem scalarCommutator_zero {I H : Type} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (a : TwiceDifferentiableMultiplier I) (u : ElectronicH1Space.L2 H I)
    (D : I → ElectronicH1Space.L2 H I)
    (hfirst : ∀ i, (a.derivative i).multiplier (D i) = 0)
    (hsecond : ∀ i, (a.derivative i).derivativeMultiplier i u = 0) :
    scalarCommutator a u D = 0 := by
  simp only [scalarCommutator, singleCutoffError, hfirst, hsecond, smul_zero,
    add_zero, Finset.sum_const_zero]

variable {I : Type} [Fintype I] [DecidableEq I]
  (V : Position I → ℝ)

theorem reference_multiply_eq_of_value (a : DifferentiableMultiplier I)
    (u v : Reference I V)
    (h : a.multiplier (inclusion I V u) = inclusion I V v) :
    PhysicalPFScalarMultiplier.multiply V a u = v :=
  inclusion_injective I V ((PhysicalPFScalarMultiplier.value_multiply V a u).trans h)

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i : I, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i : I, ∀ᵐ x : Position I ∂volume, ‖(κ i x).val‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

theorem externalCovariant_zero (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) (hz : u = 0) (i : I) :
    externalCovariant V C κ hκ M hbound e A positive negative u hu i = 0 := by
  have hv : inclusion I V u = 0 :=
    (congrArg (inclusion I V) hz).trans (map_zero _)
  have hD : covariant I V C κ hκ M hbound e i u = 0 :=
    (congrArg (covariant I V C κ hκ M hbound e i) hz).trans (map_zero _)
  have hA : roughMultiply (A i) (inclusion I V u) (hu.vector i) = 0 := by
    unfold roughMultiply
    exact lp_product_zero (inclusion I V u) (A i) (hu.vector i) hv
  unfold externalCovariant
  exact (congrArg₂ (fun x y : WaveSpace I => x + y) hD hA).trans (zero_add _)

theorem commutator_zero (a : TwiceDifferentiableMultiplier I)
    (u : Reference I V) (hu : ExternalDomain V A positive negative u)
    (hfirst : ∀ i, (a.derivative i).multiplier (inclusion I V u) = 0)
    (hsecond : ∀ i, (a.derivative i).derivativeMultiplier i (inclusion I V u) = 0) :
    PfHk.PhysicalCutoffCommutator.commutator V C κ hκ M hbound e A positive negative a u hu = 0 := by
  have hD (i : I) : (a.derivative i).multiplier
      (externalCovariant V C κ hκ M hbound e A positive negative u hu i) = 0 := by
    have hzero : PhysicalPFScalarMultiplier.multiply V (a.derivative i) u = 0 :=
      reference_multiply_eq_of_value V (a.derivative i) u 0
        ((hfirst i).trans (map_zero (inclusion I V)).symm)
    have hzeroD := externalCovariant_zero V C κ hκ M hbound e A positive negative _
      (hu.localize V (a.derivative i)) hzero i
    have hproduct := externalCovariant_localize V C κ hκ M hbound e A positive negative
      u hu (a.derivative i) i
    exact zero_add_product _ _ (hzeroD.symm.trans hproduct) (hsecond i)
  unfold PfHk.PhysicalCutoffCommutator.commutator
  exact scalarCommutator_zero a (inclusion I V u)
    (externalCovariant V C κ hκ M hbound e A positive negative u hu) hD hsecond

end PfHk.PhysicalCutoffLocality
