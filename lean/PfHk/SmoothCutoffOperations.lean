import PfHk.PhysicalCutoffCommutatorAlgebraLp

/-! Subtraction of actual scalar cutoffs and its exact L2 commutator rule.
An outer cutoff minus an inner retained bump is the annular cutoff needed
in the continuation argument. -/

noncomputable section
namespace PfHk.PhysicalCutoffCommutator

open MeasureTheory GptLean GptLean.ElectronicH1Multiplier GptLean.ElectronicH1Space

set_option maxHeartbeats 40000
set_option Elab.async false

variable {I : Type} [Fintype I] [DecidableEq I]

def scalarSub (a b : DifferentiableMultiplier I) : DifferentiableMultiplier I where
  weight := fun x => a.weight x - b.weight x
  differentiable := a.differentiable.sub b.differentiable
  bound := a.bound + b.bound
  bounded := fun x => (abs_sub _ _).trans (add_le_add (a.bounded x) (b.bounded x))
  derivativeBound := a.derivativeBound + b.derivativeBound
  derivative_bounded := by
    intro i x
    change |fderiv ℝ (a.weight - b.weight) x (EuclideanSpace.single i 1)| ≤
      a.derivativeBound + b.derivativeBound
    rw [((a.differentiable x).hasFDerivAt.sub (b.differentiable x).hasFDerivAt).fderiv,
      ContinuousLinearMap.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (a.derivative_bounded i x) (b.derivative_bounded i x))

theorem scalarSub_gradient (a b : DifferentiableMultiplier I) (i : I) (x : EuclideanSpace ℝ I) :
    (scalarSub a b).gradient i x = a.gradient i x - b.gradient i x := by
  change fderiv ℝ (a.weight - b.weight) x (EuclideanSpace.single i 1) = _
  rw [((a.differentiable x).hasFDerivAt.sub (b.differentiable x).hasFDerivAt).fderiv]
  rfl

def twiceSub (a b : TwiceDifferentiableMultiplier I) : TwiceDifferentiableMultiplier I where
  scalar := scalarSub a.scalar b.scalar
  derivative := fun i => scalarSub (a.derivative i) (b.derivative i)
  derivative_weight := by
    intro i
    funext x
    change (a.derivative i).weight x - (b.derivative i).weight x = _
    rw [a.derivative_weight, b.derivative_weight, scalarSub_gradient]

section L2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem scalar_multiplier_ae (a : DifferentiableMultiplier I) (u : L2 H I) :
    a.multiplier u =ᵐ[volume] fun x => a.weight x • u x :=
  PhotonLocalization.realL2Multiplier_apply a.weight a.differentiable.continuous.aestronglyMeasurable
    a.bound (ae_of_all _ a.bounded) u

omit [CompleteSpace H] in
private theorem scalar_derivative_ae (a : DifferentiableMultiplier I) (i : I) (u : L2 H I) :
    a.derivativeMultiplier i u =ᵐ[volume] fun x => a.gradient i x • u x :=
  PhotonLocalization.realL2Multiplier_apply (a.gradient i)
    (a.gradient_measurable i).aestronglyMeasurable a.derivativeBound
    (ae_of_all _ (a.derivative_bounded i)) u

theorem scalarSub_multiplier (a b : DifferentiableMultiplier I) (u : L2 H I) :
    (scalarSub a b).multiplier u = a.multiplier u - b.multiplier u := by
  apply Lp.ext
  filter_upwards [scalar_multiplier_ae (scalarSub a b) u, scalar_multiplier_ae a u,
    scalar_multiplier_ae b u, Lp.coeFn_sub (a.multiplier u) (b.multiplier u)] with x hx ha hb hs
  rw [hs, Pi.sub_apply, hx, ha, hb]
  exact sub_smul _ _ _

theorem scalarSub_derivativeMultiplier (a b : DifferentiableMultiplier I) (i : I) (u : L2 H I) :
    (scalarSub a b).derivativeMultiplier i u = a.derivativeMultiplier i u - b.derivativeMultiplier i u := by
  apply Lp.ext
  filter_upwards [scalar_derivative_ae (scalarSub a b) i u, scalar_derivative_ae a i u,
    scalar_derivative_ae b i u, Lp.coeFn_sub (a.derivativeMultiplier i u) (b.derivativeMultiplier i u)]
    with x hx ha hb hs
  rw [hs, Pi.sub_apply, hx, ha, hb, scalarSub_gradient]
  exact sub_smul _ _ _

theorem scalarCommutator_sub (a b : TwiceDifferentiableMultiplier I)
    (u : L2 H I) (D : I → L2 H I) :
    scalarCommutator (twiceSub a b) u D = scalarCommutator a u D - scalarCommutator b u D := by
  simp only [scalarCommutator, singleCutoffError, twiceSub, scalarSub_multiplier,
    scalarSub_derivativeMultiplier, smul_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  abel

end L2
end PfHk.PhysicalCutoffCommutator
