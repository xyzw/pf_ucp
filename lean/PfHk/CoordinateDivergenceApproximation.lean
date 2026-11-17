import PfHk.ExternalScalarApproximation
import PfHk.FriedrichsDivergenceBackground
import PfHk.CoordinateMultiplierConvergence

/-! Ordinary coefficient convergence produces actual L2 approximation,
with an arbitrary complex Hilbert fibre. -/

noncomputable section
namespace PfHk.CoordinateDivergenceApproximation

open MeasureTheory Filter GptLean GptLean.ElectronicH1Space
open GptLean.ElectronicH1Multiplier GptLean.PhysicalSourceCoordinates
open PfHk.CoordinateSobolev PfHk.FriedrichsDivergenceBackground
open scoped ENNReal Topology

set_option Elab.async false
set_option maxHeartbeats 20000

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem multiplier_ae (a : DifferentiableMultiplier (Fin N × Fin 3))
    (u : L2 H (Fin N × Fin 3)) :
    a.multiplier u =ᵐ[volume] fun x => a.weight x • u x :=
  PhotonLocalization.realL2Multiplier_apply a.weight
    a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded) u

theorem derivative_ae (a : DifferentiableMultiplier (Fin N × Fin 3))
    (u : L2 H (Fin N × Fin 3)) (i : Fin N × Fin 3) :
    a.derivativeMultiplier i u =ᵐ[volume] fun x => a.gradient i x • u x :=
  PhotonLocalization.realL2Multiplier_apply (a.gradient i)
    (a.gradient_measurable i).aestronglyMeasurable a.derivativeBound
    (ae_of_all _ (a.derivative_bounded i)) u

theorem multiplier_difference_ae (a : DifferentiableMultiplier (Fin N × Fin 3))
    (b : Configuration N → ℝ) (u bu : L2 H (Fin N × Fin 3))
    (hb : bu =ᵐ[volume] fun x => b x • u x) :
    (a.multiplier u - bu) =ᵐ[volume] fun x => (a.weight x - b x) • u x := by
  filter_upwards [Lp.coeFn_sub (a.multiplier u) bu, multiplier_ae a u, hb] with x hs ha hb
  simpa only [Pi.sub_apply, ha, hb, sub_smul] using hs

theorem value_tendsto (S : CoordinateSobolev.Data H N)
    (A : Fin N → Fin 3 → Position → ℝ) (d : Fin N → Position → ℝ) (q : ℝ)
    (a : Approximation A d q) (u : L2 H (Fin N × Fin 3))
    (au : (Fin N × Fin 3) → L2 H (Fin N × Fin 3))
    (hau : ∀ i, au i =ᵐ[volume] fun x => configurationVector A i x • u x)
    (hB : ∀ n, ∃ v : L2 H (Fin N × Fin 3), BesselPair n (1 / 2) u v)
    (i : Fin N × Fin 3) :
    Tendsto (fun k => (a.coefficient k i).multiplier u) atTop (𝓝 (au i)) := by
  let v := Classical.choose (hB i.1)
  have hv : BesselPair i.1 (3 / 6) u v := by
    simpa only [show (3 : ℝ) / 6 = 1 / 2 by norm_num] using Classical.choose_spec (hB i.1)
  have ht := coordinate_product_tendsto_zero S (by norm_num : (2 : ℝ) < 6) i.1
    (fun k => a.vectorError k i) (fun k => by simpa using a.vector_memLp k i)
    (by simpa using a.vector_tendsto i) u v hv
    (fun k => (a.coefficient k i).multiplier u - au i) (by
      intro k
      exact (multiplier_difference_ae (a.coefficient k i) (configurationVector A i) u (au i) (hau i)).trans
        (ae_of_all _ fun x => congrArg (fun z : ℝ => z • u x) (a.vector_identity k i x)))
  simpa only [sub_add_cancel, zero_add] using ht.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => au i) atTop (𝓝 (au i)))

theorem divergence_tendsto (S : CoordinateSobolev.Data H N)
    (A : Fin N → Fin 3 → Position → ℝ) (d : Fin N → Position → ℝ) (q : ℝ) (hq : 2 < q)
    (a : Approximation A d q) (u du : L2 H (Fin N × Fin 3))
    (hdu : du =ᵐ[volume] fun x => configurationDivergence d x • u x)
    (hB : ∀ n, ∃ v : L2 H (Fin N × Fin 3), BesselPair n (3 / q) u v) :
    Tendsto (fun k => ∑ i, (a.coefficient k i).derivativeMultiplier i u) atTop (𝓝 du) := by
  let v (n : Fin N) := Classical.choose (hB n)
  have hv (n : Fin N) : BesselPair n (3 / q) u (v n) := Classical.choose_spec (hB n)
  let hm (k : ℕ) (n : Fin N) := Classical.choose
    (coordinate_multiplier S hq n (a.divergenceError k n) (a.divergence_memLp k n) u (v n) (hv n))
  let err (k : ℕ) (n : Fin N) : L2 H (Fin N × Fin 3) := (hm k n).toLp _
  have herr (k : ℕ) (n : Fin N) : err k n =ᵐ[volume]
      fun x => coordinateCoefficient n (a.divergenceError k n) x • u x := (hm k n).coeFn_toLp
  have hzero (n : Fin N) : Tendsto (fun k => err k n) atTop (𝓝 0) :=
    coordinate_product_tendsto_zero S hq n (fun k => a.divergenceError k n)
      (fun k => a.divergence_memLp k n) (a.divergence_tendsto n)
      u (v n) (hv n) (fun k => err k n) (fun k => herr k n)
  have heq (k : ℕ) : (∑ i, (a.coefficient k i).derivativeMultiplier i u) - du = ∑ n, err k n := by
    apply Lp.ext
    have hder : ∀ᵐ x ∂volume, ∀ i,
        (a.coefficient k i).derivativeMultiplier i u x = (a.coefficient k i).gradient i x • u x :=
      ae_all_iff.mpr fun i => derivative_ae (a.coefficient k i) u i
    have her : ∀ᵐ x ∂volume, ∀ n,
        err k n x = coordinateCoefficient n (a.divergenceError k n) x • u x := ae_all_iff.mpr (herr k)
    filter_upwards [Lp.coeFn_sub (∑ i, (a.coefficient k i).derivativeMultiplier i u) du,
      Lp.coeFn_fun_finsetSum Finset.univ (fun i => (a.coefficient k i).derivativeMultiplier i u),
      Lp.coeFn_fun_finsetSum Finset.univ (err k), hder, her, hdu]
      with x hsub hsum hsumerr hdv hev htarget
    simp only [Pi.sub_apply] at hsub
    rw [hsub, hsum, hsumerr, htarget]
    simp only [hdv, hev, ← Finset.sum_smul, ← sub_smul, a.divergence_identity]
  have ht : Tendsto (fun k => ∑ n, err k n) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun n _ => hzero n)
  have ht' : Tendsto (fun k => (∑ i, (a.coefficient k i).derivativeMultiplier i u) - du) atTop (𝓝 0) :=
    ht.congr fun k => (heq k).symm
  simpa only [sub_add_cancel, zero_add] using ht'.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => du) atTop (𝓝 du))

def from_coordinates (S : CoordinateSobolev.Data H N)
    (A : Fin N → Fin 3 → Position → ℝ) (d : Fin N → Position → ℝ) (q : ℝ) (hq : 2 < q)
    (a : Approximation A d q) (u v : L2 H (Fin N × Fin 3))
    (au av : (Fin N × Fin 3) → L2 H (Fin N × Fin 3)) (du : L2 H (Fin N × Fin 3))
    (hau : ∀ i, au i =ᵐ[volume] fun x => configurationVector A i x • u x)
    (hav : ∀ i, av i =ᵐ[volume] fun x => configurationVector A i x • v x)
    (hdu : du =ᵐ[volume] fun x => configurationDivergence d x • u x)
    (hBu : ∀ n, ∃ w : L2 H (Fin N × Fin 3), BesselPair n (1 / 2) u w)
    (hBv : ∀ n, ∃ w : L2 H (Fin N × Fin 3), BesselPair n (1 / 2) v w)
    (hBd : ∀ n, ∃ w : L2 H (Fin N × Fin 3), BesselPair n (3 / q) u w) :
    ExternalScalarApproximation.Data u v au av du where
  coefficient := a.coefficient
  value_u := value_tendsto S A d q a u au hau hBu
  value_v := value_tendsto S A d q a v av hav hBv
  divergence_u := divergence_tendsto S A d q hq a u du hdu hBd

end PfHk.CoordinateDivergenceApproximation
