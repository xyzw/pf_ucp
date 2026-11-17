import GptLean.PhysicalFockChannelNumber
import GptLean.PhysicalL2QuadraticSeries

/-!
Joint photon-number laws on the actual coupled electronic/Fock space.
The physical tensor-sector coordinates are lifted pointwise. Nonnegative
Fubini and normal spectral decomposition identify their retained and
total bounded number observables on the same full normal channel.
-/

noncomputable section
namespace GptLean.PhysicalFock.ChannelNumber

open MeasureTheory PhotonLocalizationChannel PhysicalNormalTrace
open TensorCoordinates
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

private theorem lift_mass_series {X H ι : Type*} [MeasurableSpace X]
    (μ : Measure X) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [Countable ι] {K : ι → Type*} [∀ i, NormedAddCommGroup (K i)]
    [∀ i, InnerProductSpace ℂ (K i)]
    (Q : ∀ i, H →L[ℂ] K i)
    (hseries : ∀ v, HasSum (fun i => ‖Q i v‖ ^ 2) (‖v‖ ^ 2))
    (u : Lp H 2 μ) :
    HasSum (fun i => ‖(Q i).compLpL 2 μ u‖ ^ 2) (‖u‖ ^ 2) := by
  have hpure (v : H) : HasSum (fun i => (1 : ℝ) * ‖Q i v‖ ^ 2)
      (⟪v, (ContinuousLinearMap.id ℂ H) v⟫_ℂ).re := by
    have h := (hseries v).congr_fun (fun i => one_mul _)
    have he : (⟪v, (ContinuousLinearMap.id ℂ H) v⟫_ℂ).re = ‖v‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) v
    exact he.symm ▸ h
  have h := PhysicalL2QuadraticSeries.lift_norm_hasSum μ Q (fun _ => 1)
    (ContinuousLinearMap.id ℂ H) (fun _ => by norm_num) hpure u
  have hid : (ContinuousLinearMap.id ℂ H).compLpL 2 μ u = u := by
    apply Lp.ext
    exact (ContinuousLinearMap.id ℂ H).coeFn_compLpL u
  have he : (⟪u, (ContinuousLinearMap.id ℂ H).compLpL 2 μ u⟫_ℂ).re = ‖u‖ ^ 2 :=
    (congrArg (fun v : Lp H 2 μ => (⟪u, v⟫_ℂ).re) hid).trans
      (inner_self_eq_norm_sq (𝕜 := ℂ) u)
  exact he ▸ h.congr_fun (fun i => (one_mul _).symm)

private def QuadraticResolution {X H ι : Type*} [MeasurableSpace X]
    (μ : Measure X) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {K : ι → Type*} [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
    (Q : ∀ i, H →L[ℂ] K i) (w : ι → ℝ) (A : H →L[ℂ] H) : Prop :=
  ∀ u : Lp H 2 μ, HasSum (fun i => w i * ‖(Q i).compLpL 2 μ u‖ ^ 2)
    (⟪u, A.compLpL 2 μ u⟫_ℂ).re

variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  (BF : StandardSymmetricFockExponential) (BT : StandardNormalTraceBackground)
  (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
    WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))

def fullJointEffect (p : ℕ × ℕ) : BT.Trace (Lp PhotonFock 2 μ) →L[ℝ] ℝ :=
  ((BT.realization (Lp (TensorSpace (Sector photonMeasure p.1)
    (Sector photonMeasure p.2)) 2 μ)).rank.trace).comp
      (BT.push ((jointCoordinate photonMeasure (photonExponential BF) j p).compLpL 2 μ))

@[simp] theorem fullJointEffect_rankOne (p : ℕ × ℕ) (u : Lp PhotonFock 2 μ) :
    fullJointEffect μ BF BT j p ((BT.realization (Lp PhotonFock 2 μ)).rank.rankOne u) =
      ‖(jointCoordinate photonMeasure (photonExponential BF) j p).compLpL 2 μ u‖ ^ 2 := by
  simp only [fullJointEffect, ContinuousLinearMap.comp_apply, BT.push_rankOne,
    Gaussian.RankOneData.trace_rankOne]

def fullNumberTest (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) :
    BT.Trace (Lp PhotonFock 2 μ) →L[ℝ] ℝ :=
  Complex.reCLM.comp (((ContinuousLinearMap.apply ℂ ℂ
    ((boundedWeightOperator (Sector photonMeasure) w hw).compLpL 2 μ)).restrictScalars ℝ).comp
      (BT.realization (Lp PhotonFock 2 μ)).functional.repr)

@[simp] theorem fullNumberTest_rankOne (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1)
    (u : Lp PhotonFock 2 μ) :
    fullNumberTest μ BT w hw ((BT.realization (Lp PhotonFock 2 μ)).rank.rankOne u) =
      (⟪u, (boundedWeightOperator (Sector photonMeasure) w hw).compLpL 2 μ u⟫_ℂ).re := by
  change ((BT.realization (Lp PhotonFock 2 μ)).functional.repr
    ((BT.realization (Lp PhotonFock 2 μ)).rank.rankOne u) _).re = _
  exact congrArg Complex.re ((BT.realization (Lp PhotonFock 2 μ)).functional.rankOne u
    ((boundedWeightOperator (Sector photonMeasure) w hw).compLpL 2 μ))

private def totalOperator (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) :
    PhotonFock →L[ℂ] PhotonFock := boundedWeightOperator (Sector photonMeasure) w hw

private theorem lifted_total_hasSum (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1)
    (hpos : ∀ n, 0 ≤ w n) :
    QuadraticResolution (H := PhotonFock)
      (K := fun p : ℕ × ℕ => TensorSpace (Sector photonMeasure p.1) (Sector photonMeasure p.2)) μ
      (jointCoordinate photonMeasure (photonExponential BF) j)
      (fun p : ℕ × ℕ => w (p.1 + p.2)) (totalOperator w hw) := by
  intro u
  let Q := jointCoordinate photonMeasure (photonExponential BF) j
  have hpure (v : PhotonFock) :
      HasSum (fun p : ℕ × ℕ => w (p.1 + p.2) * ‖Q p v‖ ^ 2)
        (⟪v, totalOperator w hw v⟫_ℂ).re :=
    joint_total_hasSum photonMeasure (photonExponential BF) j w hw v
  have h := @PhysicalL2QuadraticSeries.lift_norm_hasSum X PhotonFock
    (inferInstance : MeasurableSpace X) μ
    (inferInstance : NormedAddCommGroup PhotonFock)
    (inferInstance : InnerProductSpace ℂ PhotonFock) (ℕ × ℕ) inferInstance
    (fun p : ℕ × ℕ => TensorSpace (Sector photonMeasure p.1) (Sector photonMeasure p.2))
    (fun p => inferInstance) (fun p => inferInstance) Q
    (fun p : ℕ × ℕ => w (p.1 + p.2)) (totalOperator w hw)
    (fun p => hpos _) hpure u
  exact h

theorem full_total_hasSum (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) (hpos : ∀ n, 0 ≤ w n)
    {x : BT.Trace (Lp PhotonFock 2 μ)} (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    HasSum (fun p => w (p.1 + p.2) * fullJointEffect μ BF BT j p x)
      (fullNumberTest μ BT w hw x) := by
  apply BT.normal.measurement_weighted (fullJointEffect μ BF BT j) (fullNumberTest μ BT w hw)
    (fun p => w (p.1 + p.2)) (fun p => hpos _)
    (fun p u => by rw [fullJointEffect_rankOne]; positivity) _ hx
  intro u
  simpa only [fullJointEffect_rankOne, fullNumberTest_rankOne, totalOperator] using
    lifted_total_hasSum μ BF j w hw hpos u

private def pullback (A : PhotonFock →L[ℂ] PhotonFock) : PhotonFock →L[ℂ] PhotonFock :=
  ((photonExponential BF).split photonMeasure j).toContinuousLinearMap.adjoint.comp
    ((retainedOperator A).comp ((photonExponential BF).split photonMeasure j).toContinuousLinearMap)

private theorem pullback_inner (A : PhotonFock →L[ℂ] PhotonFock) (u : PhotonFock) :
    ⟪u, pullback BF j A u⟫_ℂ =
      ⟪(photonExponential BF).split photonMeasure j u,
        retainedOperator A ((photonExponential BF).split photonMeasure j u)⟫_ℂ := by
  exact ((photonExponential BF).split photonMeasure j).toContinuousLinearMap.adjoint_inner_right _ _

private theorem weight_nonneg (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1)
    (hpos : ∀ n, 0 ≤ w n) (u : PhotonFock) :
    0 ≤ (⟪u, boundedWeightOperator (Sector photonMeasure) w hw u⟫_ℂ).re :=
  (tsum_nonneg (fun n => mul_nonneg (hpos n) (sq_nonneg _))).trans_eq
    (boundedWeightOperator_hasSum (Sector photonMeasure) w hw u).tsum_eq

private theorem lifted_factor_coordinate (u : Lp PhotonFock 2 μ) (n : ℕ) :
    (electronicFactorization μ (photonFactorization BF)).factor j u n =
      ((lp.evalCLM ℂ (fun _ : ℕ => PhotonFock) 2 n).comp
        ((photonFactorization BF).factor j).toContinuousLinearMap).compLpL 2 μ u := rfl

private theorem photon_factor_coordinate (u : PhotonFock) (n : ℕ) :
    ((lp.evalCLM ℂ (fun _ : ℕ => PhotonFock) 2 n).comp
      ((photonFactorization BF).factor j).toContinuousLinearMap) u =
      environmentalCoordinates PhotonFock ((photonExponential BF).split photonMeasure j u) n := rfl

theorem full_retained_hasSum (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) (hpos : ∀ n, 0 ≤ w n)
    {x : BT.Trace (Lp PhotonFock 2 μ)} (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    HasSum (fun p => w p.1 * fullJointEffect μ BF BT j p x)
      (fullNumberTest μ BT w hw
        (BT.normal.extend ((electronicFactorization μ (photonFactorization BF)).factor j) x)) := by
  let U := (electronicFactorization μ (photonFactorization BF)).factor j
  let A := boundedWeightOperator (Sector photonMeasure) w hw
  let Q (n : ℕ) : PhotonFock →L[ℂ] PhotonFock :=
    (lp.evalCLM ℂ (fun _ : ℕ => PhotonFock) 2 n).comp
      ((photonFactorization BF).factor j).toContinuousLinearMap
  apply BT.normal.measurement_weighted (fullJointEffect μ BF BT j)
    ((fullNumberTest μ BT w hw).comp (BT.normal.extend U)) (fun p => w p.1)
    (fun p => hpos _) (fun p u => by rw [fullJointEffect_rankOne]; positivity) _ hx
  intro u
  have hj := PhysicalL2QuadraticSeries.lift_norm_hasSum (H := PhotonFock)
    (K := fun p : ℕ × ℕ => TensorSpace (Sector photonMeasure p.1) (Sector photonMeasure p.2)) μ
    (jointCoordinate photonMeasure (photonExponential BF) j) (fun p : ℕ × ℕ => w p.1)
    (pullback BF j A) (fun p => hpos _)
    (fun v => (congrArg Complex.re (pullback_inner BF j A v)).symm ▸
      joint_retained_hasSum photonMeasure (photonExponential BF) j w hw v) u
  have hk := PhysicalL2QuadraticSeries.lift_hasSum (H := PhotonFock)
    (K := fun _ : ℕ => PhotonFock) μ Q (fun _ => A) (pullback BF j A)
    (fun _ v => weight_nonneg w hw hpos _) (fun v => by
      simpa only [Q, photon_factor_coordinate, pullback_inner, Complex.reCLM_apply] using
        Complex.reCLM.hasSum (environmentalCoordinates_observable_hasSum A
          ((photonExponential BF).split photonMeasure j v))) u
  have hn := Complex.reCLM.hasSum
    ((BT.realization (Lp PhotonFock 2 μ)).functional.observable_hasSum
      (pure_hasSum (BT.realization (Lp PhotonFock 2 μ)).rank U u) (A.compLpL 2 μ))
  simp only [U, lifted_factor_coordinate, Complex.reCLM_apply] at hn
  have he : fullNumberTest μ BT w hw
      (pure (BT.realization (Lp PhotonFock 2 μ)).rank U u) =
        (⟪u, (pullback BF j A).compLpL 2 μ u⟫_ℂ).re := by
    exact HasSum.unique hn hk
  simpa only [ContinuousLinearMap.comp_apply, BT.normal.extend_rankOne,
    fullJointEffect_rankOne, he] using hj

theorem fullJointEffect_hasSum {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    HasSum (fun p => fullJointEffect μ BF BT j p x)
      ((BT.realization (Lp PhotonFock 2 μ)).rank.trace x) := by
  apply BT.normal.measurement_hasSum _ _
    (fun p u => by rw [fullJointEffect_rankOne]; positivity) _ hx
  intro u
  have h := @lift_mass_series X PhotonFock (ℕ × ℕ)
    (inferInstance : MeasurableSpace X) μ
    (inferInstance : NormedAddCommGroup PhotonFock)
    (inferInstance : InnerProductSpace ℂ PhotonFock) inferInstance
    (fun p : ℕ × ℕ => TensorSpace (Sector photonMeasure p.1) (Sector photonMeasure p.2))
    (fun p => inferInstance) (fun p => inferInstance)
    (jointCoordinate photonMeasure (photonExponential BF) j)
    (joint_mass_hasSum photonMeasure (photonExponential BF) j) u
  simpa only [fullJointEffect_rankOne, Gaussian.RankOneData.trace_rankOne] using h

end GptLean.PhysicalFock.ChannelNumber
