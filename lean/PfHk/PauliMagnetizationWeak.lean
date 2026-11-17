import PfHk.PauliCurrentCorrection
import GptLean.ElectronicH1Multiplier
import PfHk.PauliSpinMaps

/-! The weak product rule for the actual spin magnetization. It is
obtained from H1 integration by parts and the self-adjoint Pauli matrices.
The result applies to bounded smooth tests, including lifted one-body tests. -/

noncomputable section
namespace PfHk.PauliMagnetizationWeak

open MeasureTheory GptLean GptLean.ElectronicH1Complex
  GptLean.ElectronicH1Multiplier PfHk.PauliSpin PfHk.PauliCurrentCorrection
open scoped ComplexConjugate

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [local irreducible] ElectronicH1Complex.complexWeakGraph
  ElectronicH1Complex.value ElectronicH1Complex.derivative ElectronicH1Complex.realEquiv

variable {N : ℕ} {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Fintype I] [DecidableEq I]

theorem spinPair_re_swap (n : Fin N) (u v : SpinIndex N → H) (k : Fin 3) :
    (spinPair n u v k).re = (spinPair n v u k).re := by
  have h : spinPair n u v k = conj (spinPair n v u k) := by
    calc
      _ = ∑ s, inner ℂ (sigmaFamily n k u s) (v s) :=
        (sigmaFamily_selfadjoint n k u v).symm
      _ = _ := by simp only [spinPair, map_sum, inner_conj_symm]
  exact (congrArg Complex.re h).trans (Complex.conj_re _)

variable [CompleteSpace H]

theorem weighted_product_rule (a : SmoothMultiplier I) (n : Fin N) (k : Fin 3)
    (u : SpinIndex N → ComplexH1 H I) (i : I) :
    (spinPair n (fun s => a.derivativeMultiplier i (value (E := H) (I := I) (u s)))
      (fun s => value (E := H) (I := I) (u s)) k).re =
      -2 * (spinPair n (fun s => value (E := H) (I := I) (u s))
        (fun s => a.multiplier (derivative (E := H) (I := I) i (u s))) k).re := by
  let v : SpinIndex N → ElectronicH1Space.L2 H I := fun s => value (E := H) (I := I) (u s)
  let d : SpinIndex N → ElectronicH1Space.L2 H I := fun s => derivative (E := H) (I := I) i (u s)
  have hv : (fun s => value (E := H) (I := I) (sigmaFamily n k u s)) = sigmaFamily n k v :=
    (sigmaFamily_map n k (value (E := H) (I := I)).toLinearMap u).symm
  have hd : (fun s => a.multiplier (derivative (E := H) (I := I) i (sigmaFamily n k u s))) =
      sigmaFamily n k (fun s => a.multiplier (d s)) :=
    (sigmaFamily_map n k
      (a.multiplier.comp (derivative i (E := H))).toLinearMap u).symm
  have hs (s : SpinIndex N) :
      inner ℂ (v s) (sigmaFamily n k (fun t => a.multiplier (d t)) s) =
      -(inner ℂ (a.multiplier (d s)) (sigmaFamily n k v s) +
        inner ℂ (a.derivativeMultiplier i (v s)) (sigmaFamily n k v s)) := by
    rw [← congrFun hd s, ← congrFun hv s]
    have hb := a.weighted_integration_by_parts (H := H)
      (realEquiv (E := H) (I := I) (u s))
      (realEquiv (E := H) (I := I) (sigmaFamily n k u s)) i
    simpa only [value_realEquiv, derivative_realEquiv] using hb
  have hh : spinPair n v (fun s => a.multiplier (d s)) k =
      -(spinPair n (fun s => a.multiplier (d s)) v k +
        spinPair n (fun s => a.derivativeMultiplier i (v s)) v k) := by
    unfold spinPair
    simp only [hs, Finset.sum_neg_distrib, Finset.sum_add_distrib]
  have hr := congrArg Complex.re hh
  simp only [Complex.neg_re, Complex.add_re] at hr
  have hswap := spinPair_re_swap n (fun s => a.multiplier (d s)) v k
  change (spinPair n (fun s => a.derivativeMultiplier i (v s)) v k).re =
    -2 * (spinPair n v (fun s => a.multiplier (d s)) k).re
  linarith

end PfHk.PauliMagnetizationWeak
