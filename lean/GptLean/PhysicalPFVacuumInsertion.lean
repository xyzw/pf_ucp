import GptLean.PhysicalFockHardSoftVacuum
import GptLean.PhysicalFockHardField
import GptLean.PhysicalPhotonMarginal
import GptLean.PhysicalPFSpatialObservables
import GptLean.ElectronicH1Map

/-!
Spatial insertion of the actual soft photon vacuum.  The map is the L² lift
of the constructed hard-photon inclusion.  Density tests and the full photon
marginal are preserved through the same normal trace realization.  The
electronic weak derivative commutes with insertion on its actual H1 graph.
-/

noncomputable section

namespace GptLean.PhysicalPFVacuumInsertion

open MeasureTheory Filter Topology PhysicalNormalTrace PhysicalL2HilbertSum
  PhysicalFock PhotonLocalization PhysicalPFSource
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section Lift

variable {X H K : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- A fiber isometry acts isometrically on the actual spatial L² classes. -/
def spatialLift (J : H →ₗᵢ[ℂ] K) : Lp H 2 μ →ₗᵢ[ℂ] Lp K 2 μ :=
  (J.toContinuousLinearMap.compLpL 2 μ).toLinearMap.isometryOfInner (fun u v => by
    change ⟪J.toContinuousLinearMap.compLpL 2 μ u,
      J.toContinuousLinearMap.compLpL 2 μ v⟫_ℂ = ⟪u, v⟫_ℂ
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [J.toContinuousLinearMap.coeFn_compLpL u,
      J.toContinuousLinearMap.coeFn_compLpL v] with x hu hv
    rw [hu, hv]
    exact J.inner_map_map (u x) (v x))

@[simp] theorem spatialLift_apply (J : H →ₗᵢ[ℂ] K) (u : Lp H 2 μ) :
    spatialLift μ J u = J.toContinuousLinearMap.compLpL 2 μ u := rfl

theorem spatialLift_ae (J : H →ₗᵢ[ℂ] K) (u : Lp H 2 μ) :
    spatialLift μ J u =ᵐ[μ] fun x => J (u x) :=
  J.toContinuousLinearMap.coeFn_compLpL u

theorem spatialLift_norm_ae (J : H →ₗᵢ[ℂ] K) (u : Lp H 2 μ) :
    ∀ᵐ x ∂μ, ‖spatialLift μ J u x‖ = ‖u x‖ := by
  filter_upwards [spatialLift_ae μ J u] with x hx
  rw [hx, J.norm_map]

theorem spatialLift_weighted_norm (J : H →ₗᵢ[ℂ] K) (a : X → ℝ) (u : Lp H 2 μ) :
    (∫ x, a x * ‖spatialLift μ J u x‖ ^ 2 ∂μ) = ∫ x, a x * ‖u x‖ ^ 2 ∂μ := by
  apply integral_congr_ae
  filter_upwards [spatialLift_norm_ae μ J u] with x hx
  rw [hx]

end Lift

section Coefficients

variable {X H K ι : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (b : HilbertBasis ι ℂ (Lp ℂ 2 μ))

/-- Spatial Hilbert coefficients commute with bounded maps between fibers. -/
theorem coefficients_map (L : H →L[ℂ] K) (u : Lp H 2 μ) (i : ι) :
    coefficients b (L.compLpL 2 μ u) i = L (coefficients b u i) := by
  apply ext_inner_left ℂ
  intro v
  rw [coefficients_inner, ← L.adjoint_inner_left, coefficients_inner]
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tensor_ae (b i) v, tensor_ae (b i) (L.adjoint v),
    L.coeFn_compLpL u] with x hv hw hL
  rw [hv, hw, hL, inner_smul_left, inner_smul_left, L.adjoint_inner_left]

theorem countableCoefficients_map (e : ι ↪ ℕ) (L : H →L[ℂ] K)
    (u : Lp H 2 μ) (n : ℕ) :
    countableCoefficients b e (L.compLpL 2 μ u) n =
      L (countableCoefficients b e u n) := by
  classical
  by_cases hn : n ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hn
    change padding e (coefficients b (L.compLpL 2 μ u)) (e i) =
      L (padding e (coefficients b u) (e i))
    rw [padding_at, padding_at, coefficients_map]
  · change padding e (coefficients b (L.compLpL 2 μ u)) n =
      L (padding e (coefficients b u) n)
    rw [padding_off e _ n hn, padding_off e _ n hn, map_zero]

theorem spatialCoefficients_map [IsSeparable μ] (L : H →L[ℂ] K)
    (u : Lp H 2 μ) (n : ℕ) :
    spatialCoefficients μ K (L.compLpL 2 μ u) n =
      L (spatialCoefficients μ H u n) :=
  countableCoefficients_map (spatialBasis μ) (spatialIndexEmbedding μ) L u n

end Coefficients

section Normal

variable {X H K : Type} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (B : StandardNormalTraceBackground) (J : H →ₗᵢ[ℂ] K)

/-- The actual full photon marginal commutes with insertion on every vector. -/
theorem marginal_rankOne :
    ∀ u : Lp H 2 μ,
      PhysicalPhotonMarginal.marginal B μ
        ((B.realization (Lp K 2 μ)).rank.rankOne (spatialLift μ J u)) =
      B.push J.toContinuousLinearMap (PhysicalPhotonMarginal.marginal B μ
        ((B.realization (Lp H 2 μ)).rank.rankOne u)) := by
  intro u
  change B.partialTrace (spatialCoefficients μ K)
      ((B.realization (Lp K 2 μ)).rank.rankOne (spatialLift μ J u)) =
    B.push J.toContinuousLinearMap (B.partialTrace (spatialCoefficients μ H)
      ((B.realization (Lp H 2 μ)).rank.rankOne u))
  rw [B.partialTrace_rankOne, B.partialTrace_rankOne]
  have hs := (B.push J.toContinuousLinearMap).hasSum
    (Repair.rankOneSeries_hasSum (B.realization H).rank
      (StandardNormalTraceBackground.dilation_mass (spatialCoefficients μ H) u))
  simpa only [B.push_rankOne, Repair.rankOneSeries, spatialLift_apply,
    spatialCoefficients_map] using hs.tsum_eq

/-- Naturality holds for every positive normal state, not only rank-one states. -/
theorem marginal_push {x : B.Trace (Lp H 2 μ)}
    (hx : x ∈ (B.realization (Lp H 2 μ)).rank.positive) :
    PhysicalPhotonMarginal.marginal B μ
        (B.push (spatialLift μ J).toContinuousLinearMap x) =
      B.push J.toContinuousLinearMap (PhysicalPhotonMarginal.marginal B μ x) := by
  obtain ⟨v, hv⟩ := (B.realization (Lp H 2 μ)).spectral x hx
  have h₁ := (PhysicalPhotonMarginal.marginal B μ).hasSum
    ((B.push (spatialLift μ J).toContinuousLinearMap).hasSum hv)
  have h₂ := (B.push J.toContinuousLinearMap).hasSum
    ((PhysicalPhotonMarginal.marginal B μ).hasSum hv)
  simp only [B.push_rankOne, LinearIsometry.coe_toContinuousLinearMap,
    marginal_rankOne] at h₁
  exact h₁.unique h₂

omit [IsSeparable μ] in
/-- Every bounded spatial density test is unchanged by insertion. -/
theorem density_rankOne (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (c : ℝ) (hc : ∀ᵐ x ∂μ, |a x| ≤ c) (u : Lp H 2 μ) :
    boundedTrace (B.realization (Lp K 2 μ)).functional
        (realL2Multiplier a ha c hc)
        ((B.realization (Lp K 2 μ)).rank.rankOne (spatialLift μ J u)) =
      boundedTrace (B.realization (Lp H 2 μ)).functional
        (realL2Multiplier a ha c hc) ((B.realization (Lp H 2 μ)).rank.rankOne u) := by
  rw [boundedTrace_multiplier_rankOne, boundedTrace_multiplier_rankOne]
  exact spatialLift_weighted_norm μ J a u

omit [IsSeparable μ] in
theorem density_push (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (c : ℝ) (hc : ∀ᵐ x ∂μ, |a x| ≤ c) {x : B.Trace (Lp H 2 μ)}
    (hx : x ∈ (B.realization (Lp H 2 μ)).rank.positive) :
    boundedTrace (B.realization (Lp K 2 μ)).functional (realL2Multiplier a ha c hc)
        (B.push (spatialLift μ J).toContinuousLinearMap x) =
      boundedTrace (B.realization (Lp H 2 μ)).functional (realL2Multiplier a ha c hc) x := by
  obtain ⟨v, hv⟩ := (B.realization (Lp H 2 μ)).spectral x hx
  have h₁ := (boundedTrace (B.realization (Lp K 2 μ)).functional
    (realL2Multiplier a ha c hc)).hasSum
    ((B.push (spatialLift μ J).toContinuousLinearMap).hasSum hv)
  have h₂ := (boundedTrace (B.realization (Lp H 2 μ)).functional
    (realL2Multiplier a ha c hc)).hasSum hv
  simp only [B.push_rankOne, LinearIsometry.coe_toContinuousLinearMap,
    density_rankOne] at h₁
  exact h₁.unique h₂

end Normal

section ElectronicLift

variable {I H K : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedSpace ℝ K] [IsScalarTower ℝ ℂ K]

theorem spatialLift_value (J : H →ₗᵢ[ℂ] K)
    (u : ElectronicH1Complex.ComplexH1 H I) :
    ElectronicH1Complex.value (ElectronicH1Map.map J.toContinuousLinearMap u) =
      spatialLift volume J (ElectronicH1Complex.value u) := rfl

theorem spatialLift_derivative (J : H →ₗᵢ[ℂ] K)
    (u : ElectronicH1Complex.ComplexH1 H I) (i : I) :
    ElectronicH1Complex.derivative i (ElectronicH1Map.map J.toContinuousLinearMap u) =
      spatialLift volume J (ElectronicH1Complex.derivative i u) := rfl

end ElectronicLift

attribute [local irreducible] spatialLift ElectronicH1Map.map
  ElectronicH1Complex.value ElectronicH1Complex.derivative

section Physical

variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  (BF : StandardSymmetricFockExponential) (κ : ℝ)

/-- Spatial soft-vacuum insertion through the actual hard/soft factorization. -/
def insertion :
    Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ →ₗᵢ[ℂ] Lp PhotonFock 2 μ :=
  spatialLift (H := ↥(generatedFockSubspace (hardOnePhoton κ))) (K := PhotonFock)
    μ (hardPhotonVacuumEmbedding BF κ)

theorem insertion_ae (u : Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ) :
    insertion μ BF κ u =ᵐ[μ] fun x => (u x).val := by
  simpa only [insertion, hardPhotonVacuumEmbedding_apply] using
    spatialLift_ae (H := ↥(generatedFockSubspace (hardOnePhoton κ))) (K := PhotonFock)
      μ (hardPhotonVacuumEmbedding BF κ) u

theorem insertion_marginal [IsSeparable μ] (B : StandardNormalTraceBackground)
    {x : B.Trace (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ)}
    (hx : x ∈ (B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ)).rank.positive) :
    PhysicalPhotonMarginal.marginal B μ (B.push (insertion μ BF κ).toContinuousLinearMap x) =
      B.push (hardPhotonVacuumEmbedding BF κ).toContinuousLinearMap
        (PhysicalPhotonMarginal.marginal B μ x) := by
  unfold insertion
  exact marginal_push (H := ↥(generatedFockSubspace (hardOnePhoton κ))) (K := PhotonFock)
    μ B (hardPhotonVacuumEmbedding BF κ) hx

end Physical

section Electronic

variable {I : Type} [Fintype I] [DecidableEq I]
  (BF : StandardSymmetricFockExponential) (κ : ℝ)

/-- Vacuum insertion maps the actual weak H1 graph into the full electronic graph. -/
def electronicInsertion :
    ElectronicH1Complex.ComplexH1 (generatedFockSubspace (hardOnePhoton κ)) I →L[ℂ]
      ElectronicH1Complex.ComplexH1 PhotonFock I :=
  ElectronicH1Map.map (I := I) (E := ↥(generatedFockSubspace (hardOnePhoton κ)))
    (F := PhotonFock) (hardPhotonVacuumEmbedding BF κ).toContinuousLinearMap

theorem electronicInsertion_value
    (u : ElectronicH1Complex.ComplexH1 (generatedFockSubspace (hardOnePhoton κ)) I) :
    ElectronicH1Complex.value (electronicInsertion BF κ u) =
      insertion volume BF κ (ElectronicH1Complex.value u) := by
  unfold insertion electronicInsertion spatialLift ElectronicH1Map.map ElectronicH1Complex.value
  rfl

theorem electronicInsertion_derivative
    (u : ElectronicH1Complex.ComplexH1 (generatedFockSubspace (hardOnePhoton κ)) I) (i : I) :
    ElectronicH1Complex.derivative i (electronicInsertion BF κ u) =
      insertion volume BF κ (ElectronicH1Complex.derivative i u) := by
  unfold insertion electronicInsertion spatialLift ElectronicH1Map.map ElectronicH1Complex.derivative
  rfl

end Electronic

end GptLean.PhysicalPFVacuumInsertion
