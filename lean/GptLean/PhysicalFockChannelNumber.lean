import GptLean.PhysicalFockTensorSectors
import GptLean.PhysicalFockNumber
import GptLean.PhysicalFockChannel

/-!
Joint photon-number laws for the matched physical exponential map.

The joint masses are squared coordinates in the actual retained/discarded
tensor sectors. Both bounded number identities follow from these
coordinates and the creation-word matching of the exponential law.
The normal spectral theorem then gives the mixed-state identities.
No environmental basis vector is designated as the vacuum.
-/

noncomputable section
namespace GptLean.PhysicalFock.ChannelNumber

open MeasureTheory UniformSpace Filter Topology
open PhotonLocalizationChannel PhysicalNormalTrace
open TensorCoordinates TensorSectors
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true

private theorem weighted_isometry_hasSum {H ι : Type*} {K : ι → Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
    (J : H →ₗᵢ[ℂ] lp K 2) (A : H →L[ℂ] H) (w : ι → ℝ)
    (h : ∀ u i, J (A u) i = (w i : ℂ) • J u i) (u : H) :
    HasSum (fun i => w i * ‖J u i‖ ^ 2) (⟪u, A u⟫_ℂ).re := by
  have hs := Complex.reCLM.hasSum (lp.hasSum_inner (J u) (J (A u)))
  rw [J.inner_map_map] at hs
  change HasSum (fun i => (⟪J u i, J (A u) i⟫_ℂ).re) (⟪u, A u⟫_ℂ).re at hs
  apply hs.congr_fun
  intro i
  simp only [h, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

private theorem weighted_tensor_hasSum {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : ℕ → Type*) [∀ n, NormedAddCommGroup (K n)]
    [∀ n, InnerProductSpace ℂ (K n)]
    (U : H →ₗᵢ[ℂ] TensorSpace (Space K) (Space K))
    (A : H →L[ℂ] H) (w : ℕ × ℕ → ℝ)
    (h : ∀ u p, pairCoordinate K p (U (A u)) =
      (w p : ℂ) • pairCoordinate K p (U u)) (u : H) :
    HasSum (fun p => w p * ‖pairCoordinate K p (U u)‖ ^ 2)
      (⟪u, A u⟫_ℂ).re := by
  exact weighted_isometry_hasSum ((pairCoefficients K).toLinearIsometry.comp U)
    A w h u

private theorem pair_retained_weight_generic
    (K : ℕ → Type*) [∀ n, NormedAddCommGroup (K n)]
    [∀ n, InnerProductSpace ℂ (K n)]
    (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1)
    (z : TensorSpace (Space K) (Space K)) (p : ℕ × ℕ) :
    pairCoordinate K p (retainedOperator (boundedWeightOperator K w hw) z) =
      (w p.1 : ℂ) • pairCoordinate K p z := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((pairCoordinate K p).continuous.comp
      (retainedOperator (boundedWeightOperator K w hw)).continuous)
      ((pairCoordinate K p).continuous.const_smul (w p.1 : ℂ))
  | ih z =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [Completion.coe_zero, map_zero, smul_zero]
    | tmul u v =>
      change pairCoefficients K
        (retainedOperator (boundedWeightOperator K w hw) (tensor u v)) p =
          (w p.1 : ℂ) • pairCoefficients K (tensor u v) p
      rw [retainedOperator_tensor, pairCoefficients_tensor, pairCoefficients_tensor,
        boundedWeightOperator_apply, map_smul]
      rfl
    | add z z' hz hz' =>
      simpa only [Completion.coe_add, map_add, smul_add] using congrArg₂ (· + ·) hz hz'

private theorem pair_retained_hasSum_generic
    (K : ℕ → Type*) [∀ n, NormedAddCommGroup (K n)]
    [∀ n, InnerProductSpace ℂ (K n)]
    (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1)
    (z : TensorSpace (Space K) (Space K)) :
    HasSum (fun p => w p.1 * ‖pairCoordinate K p z‖ ^ 2)
      (⟪z, retainedOperator (boundedWeightOperator K w hw) z⟫_ℂ).re := by
  exact weighted_isometry_hasSum (pairCoefficients K).toLinearIsometry
    (retainedOperator (boundedWeightOperator K w hw)) (fun p => w p.1)
    (fun v p => pair_retained_weight_generic K w hw v p) z

section Pure
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
  (B : ConcreteExponentialLaw μ)
  (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))

def jointCoordinate (p : ℕ × ℕ) :
    Fock μ →L[ℂ] TensorSpace (Sector μ p.1) (Sector μ p.2) :=
  (pairCoordinate (Sector μ) p).comp (B.split μ j).toContinuousLinearMap

@[simp] theorem jointCoordinate_apply (p : ℕ × ℕ) (u : Fock μ) :
    jointCoordinate μ B j p u = pairCoefficients (Sector μ) (B.split μ j u) p := rfl

theorem joint_mass_hasSum (u : Fock μ) :
    HasSum (fun p => ‖jointCoordinate μ B j p u‖ ^ 2) (‖u‖ ^ 2) := by
  simpa only [jointCoordinate_apply, ENNReal.toReal_ofNat, Real.rpow_two,
    LinearIsometryEquiv.norm_map, LinearIsometry.norm_map] using
    lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
      (pairCoefficients (Sector μ) (B.split μ j u))

private theorem weight_sector (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1)
    (u : Fock μ) (n : ℕ) :
    photonSector μ n (boundedWeightOperator (Sector μ) w hw u) =
      (w n : ℂ) • photonSector μ n u := by
  change lp.single 2 n ((w n : ℂ) • u n) = (w n : ℂ) • lp.single 2 n (u n)
  exact map_smul (lp.singleContinuousLinearMap ℂ (Sector μ) 2 n) (w n : ℂ) (u n)

theorem joint_total_weight (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1)
    (u : Fock μ) (p : ℕ × ℕ) :
    jointCoordinate μ B j p (boundedWeightOperator (Sector μ) w hw u) =
      (w (p.1 + p.2) : ℂ) • jointCoordinate μ B j p u := by
  let Q := jointCoordinate μ B j p
  calc
    Q (boundedWeightOperator (Sector μ) w hw u) =
        Q (photonSector μ (p.1 + p.2) (boundedWeightOperator (Sector μ) w hw u)) :=
      split_pair_eq_sector μ B j _ p
    _ = Q ((w (p.1 + p.2) : ℂ) • photonSector μ (p.1 + p.2) u) :=
      congrArg Q (weight_sector μ w hw u (p.1 + p.2))
    _ = (w (p.1 + p.2) : ℂ) • Q (photonSector μ (p.1 + p.2) u) := Q.map_smul _ _
    _ = (w (p.1 + p.2) : ℂ) • Q u :=
      congrArg ((w (p.1 + p.2) : ℂ) • ·) (split_pair_eq_sector μ B j u p).symm

theorem joint_total_hasSum (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) (u : Fock μ) :
    HasSum (fun p => w (p.1 + p.2) * ‖jointCoordinate μ B j p u‖ ^ 2)
      (⟪u, boundedWeightOperator (Sector μ) w hw u⟫_ℂ).re := by
  apply weighted_tensor_hasSum (Sector μ) (B.split μ j)
    (boundedWeightOperator (Sector μ) w hw) (fun p => w (p.1 + p.2))
  exact fun v p => joint_total_weight μ B j w hw v p

theorem pair_retained_weight (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1)
    (z : TensorSpace (Fock μ) (Fock μ)) (p : ℕ × ℕ) :
    pairCoefficients (Sector μ)
      (retainedOperator (boundedWeightOperator (Sector μ) w hw) z) p =
      (w p.1 : ℂ) • pairCoefficients (Sector μ) z p := by
  exact pair_retained_weight_generic (Sector μ) w hw z p

theorem joint_retained_hasSum (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) (u : Fock μ) :
    HasSum (fun p => w p.1 * ‖jointCoordinate μ B j p u‖ ^ 2)
      (⟪B.split μ j u,
        retainedOperator (boundedWeightOperator (Sector μ) w hw) (B.split μ j u)⟫_ℂ).re := by
  exact pair_retained_hasSum_generic (Sector μ) w hw (B.split μ j u)

end Pure

section Normal
variable (BF : StandardSymmetricFockExponential) (BT : StandardNormalTraceBackground)
  (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
    WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))

abbrev PhotonTrace := BT.Trace PhotonFock

private theorem factor_apply (u : PhotonFock) :
    (photonFactorization BF).factor j u =
      environmentalCoordinates PhotonFock ((photonExponential BF).split photonMeasure j u) := rfl

def jointEffect (p : ℕ × ℕ) : PhotonTrace BT →L[ℝ] ℝ :=
  ((BT.realization (TensorSpace (Sector photonMeasure p.1) (Sector photonMeasure p.2))).rank.trace).comp
    (BT.push (jointCoordinate photonMeasure (photonExponential BF) j p))

@[simp] theorem jointEffect_rankOne (p : ℕ × ℕ) (u : PhotonFock) :
    jointEffect BF BT j p ((BT.realization PhotonFock).rank.rankOne u) =
      ‖jointCoordinate photonMeasure (photonExponential BF) j p u‖ ^ 2 := by
  simp only [jointEffect, ContinuousLinearMap.comp_apply, BT.push_rankOne,
    Gaussian.RankOneData.trace_rankOne]

theorem jointEffect_nonneg (p : ℕ × ℕ) {x : PhotonTrace BT}
    (hx : x ∈ (BT.realization PhotonFock).rank.positive) : 0 ≤ jointEffect BF BT j p x :=
  BT.normal.observable_nonneg _ (fun u => by rw [jointEffect_rankOne]; positivity) hx

theorem jointEffect_hasSum {x : PhotonTrace BT}
    (hx : x ∈ (BT.realization PhotonFock).rank.positive) :
    HasSum (fun p => jointEffect BF BT j p x) ((BT.realization PhotonFock).rank.trace x) := by
  apply BT.normal.measurement_hasSum _ _
    (fun p u => by rw [jointEffect_rankOne]; positivity) _ hx
  intro u
  simpa only [jointEffect_rankOne, Gaussian.RankOneData.trace_rankOne] using
    joint_mass_hasSum photonMeasure (photonExponential BF) j u

def numberTest (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) : PhotonTrace BT →L[ℝ] ℝ :=
  boundedWeightTrace (Sector photonMeasure) (BT.realization PhotonFock).functional w hw

@[simp] theorem numberTest_rankOne (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) (u : PhotonFock) :
    numberTest BT w hw ((BT.realization PhotonFock).rank.rankOne u) =
      (⟪u, boundedWeightOperator (Sector photonMeasure) w hw u⟫_ℂ).re := by
  rw [numberTest, boundedWeightTrace_apply, (BT.realization PhotonFock).functional.rankOne]

theorem total_hasSum (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) (hpos : ∀ n, 0 ≤ w n)
    {x : PhotonTrace BT} (hx : x ∈ (BT.realization PhotonFock).rank.positive) :
    HasSum (fun p => w (p.1 + p.2) * jointEffect BF BT j p x) (numberTest BT w hw x) := by
  apply BT.normal.measurement_weighted (jointEffect BF BT j) (numberTest BT w hw)
    (fun p => w (p.1 + p.2)) (fun p => hpos _) (fun p u => by
      rw [jointEffect_rankOne]; positivity) _ hx
  intro u
  simpa only [jointEffect_rankOne, numberTest_rankOne] using
    joint_total_hasSum photonMeasure (photonExponential BF) j w hw u

theorem retained_hasSum (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) (hpos : ∀ n, 0 ≤ w n)
    {x : PhotonTrace BT} (hx : x ∈ (BT.realization PhotonFock).rank.positive) :
    HasSum (fun p => w p.1 * jointEffect BF BT j p x)
      (numberTest BT w hw (BT.normal.extend ((photonFactorization BF).factor j) x)) := by
  apply BT.normal.measurement_weighted (jointEffect BF BT j)
    ((numberTest BT w hw).comp (BT.normal.extend ((photonFactorization BF).factor j)))
    (fun p => w p.1) (fun p => hpos _) (fun p u => by
      rw [jointEffect_rankOne]; positivity) _ hx
  intro u
  have hnormal := Complex.reCLM.hasSum ((BT.realization PhotonFock).functional.observable_hasSum
    (pure_hasSum (BT.realization PhotonFock).rank ((photonFactorization BF).factor j) u)
    (boundedWeightOperator (Sector photonMeasure) w hw))
  simp only [factor_apply] at hnormal
  have htensor := Complex.reCLM.hasSum (environmentalCoordinates_observable_hasSum
    (boundedWeightOperator (Sector photonMeasure) w hw)
    ((photonExponential BF).split photonMeasure j u))
  have he : numberTest BT w hw
      (pure (BT.realization PhotonFock).rank ((photonFactorization BF).factor j) u) =
      (⟪(photonExponential BF).split photonMeasure j u,
        retainedOperator (boundedWeightOperator (Sector photonMeasure) w hw)
          ((photonExponential BF).split photonMeasure j u)⟫_ℂ).re := by
    exact HasSum.unique hnormal htensor
  simp only [ContinuousLinearMap.comp_apply, BT.normal.extend_rankOne, he,
    jointEffect_rankOne]
  exact joint_retained_hasSum photonMeasure (photonExponential BF) j w hw u

end Normal
end GptLean.PhysicalFock.ChannelNumber
