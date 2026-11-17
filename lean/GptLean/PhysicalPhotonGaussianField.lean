import GptLean.PhysicalPhotonGaussian
import GptLean.PhysicalFockSoftGaussianGraph
import GptLean.PhysicalFockHardField
import GptLean.PhysicalGaussianSource
import GptLean.PhysicalFockSpatialFieldParts

/-!
Multiplication by the scalar first chaos is proved for the actual full
photon field and its electronic L² lift. Only the universal scalar WIS
theorem is used. The hard coefficients and spatial source maps are the
constructed orthogonal split and Fubini maps.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory Filter Topology PhysicalGaussianCoordinates TensorCoordinates
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

private theorem segalGraph_replace_kernel {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] {f g : Lp ℂ 2 μ} {u v : Fock μ}
    (hfg : f = g) (h : SegalGraph μ f u v) : SegalGraph μ g u v :=
  (congrArg (fun k : Lp ℂ 2 μ => SegalGraph μ k u v) hfg).mp h

/-- Scalar WIS graph identities extend to the second tensor factor before
specializing that factor to the physical hard-photon space. -/
private theorem tensorLift_scalarWienerSegal {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] (V : Submodule ℂ (Lp ℂ 2 μ))
    (J : RealStructure V) (W : ScalarWienerSegal μ V J)
    {H ι η : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Countable η] (bS : HilbertBasis ι ℂ (generatedSubspace μ V))
    (bH : HilbertBasis η ℂ H) (g : J.fixedSpace) (f : Lp ℂ 2 μ)
    (hf : f = ((g : V) : Lp ℂ 2 μ))
    (u v : TensorSpace (generatedSubspace μ V) H)
    (hg : ∀ i, SegalGraph μ f (coefficients bH u i).val (coefficients bH v i).val) :
    tensorLift bS W.unitary v =ᵐ[W.space.measure]
      fun q => W.firstChaos g q • tensorLift bS W.unitary u q := by
  have h := tensorLift_intertwining bS W.unitary bH
    (fun q => (W.firstChaos g q : ℂ)) u v (fun i => by
      have hi := W.intertwining g (coefficients bH u i) (coefficients bH v i)
        (segalGraph_replace_kernel μ hf (hg i))
      simpa only [Complex.real_smul, smul_eq_mul] using hi)
  simpa only [Complex.coe_smul] using h

/-- Transport a real scalar multiplication identity between equal L²
representatives in an abstract complex Hilbert space. -/
private theorem ae_real_smul_of_eq {Q H : Type*} [MeasurableSpace Q] {μ : Measure Q}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a : Q → ℝ) (u v u' v' : Lp H 2 μ) (hu : u = u') (hv : v = v')
    (h : v' =ᵐ[μ] fun q => a q • u' q) : v =ᵐ[μ] fun q => a q • u q := by
  subst u'
  subst v'
  exact h

/-- A pointwise identity for two bounded graph maps passes to their
spatial L² lifts entirely at the level of abstract Hilbert spaces. -/
private theorem spatialUnitary_intertwining_compLpL
    {X Q E H K : Type*} [MeasurableSpace X] [MeasurableSpace Q]
    (ν : Measure X) (μ : Measure Q) [SFinite μ] [SFinite ν]
    [IsSeparable μ] [IsSeparable ν]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K]
    (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (L R : E →L[ℂ] H)
    (a : Q → ℝ) (ha : StronglyMeasurable a)
    (h : ∀ v, U (L v) =ᵐ[μ] fun q => a q • U (R v) q) (u : Lp E 2 ν) :
    spatialUnitary ν μ U (L.compLpL 2 ν u) =ᵐ[μ]
      fun q => a q • spatialUnitary ν μ U (R.compLpL 2 ν u) q := by
  refine spatialUnitary_intertwining ν μ U a ha
    (R.compLpL 2 ν u) (L.compLpL 2 ν u) ?_
  filter_upwards [L.coeFn_compLpL u, R.coeFn_compLpL u] with x hL hR
  exact (congrArg₂ (fun v w : H => U v =ᵐ[μ] fun q => a q • U w q)
    hL hR).mpr (h (u x))

def hardBasisIndex (κ : ℝ) : Set (HardPhotonFock κ) :=
  (exists_hilbertBasis ℂ (HardPhotonFock κ)).choose

def hardBasis (κ : ℝ) : HilbertBasis (hardBasisIndex κ) ℂ (HardPhotonFock κ) :=
  (exists_hilbertBasis ℂ (HardPhotonFock κ)).choose_spec.choose

instance hardBasisIndex_countable (κ : ℝ) : Countable (hardBasisIndex κ) :=
  PhysicalL2HilbertSum.basisIndex_countable (hardBasis κ)

attribute [local irreducible] photonGaussianUnitary spatialUnitary tensorLift
  supportedFockEquivalence coefficients radiationGraphInclusion

variable (BF : StandardSymmetricFockExponential) (κ : ℝ)
  {J : RealStructure (softOnePhoton κ)}
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)
  (C : CanonicalSectorCCR photonMeasure)

set_option maxHeartbeats 800000 in
/-- Actual soft fields become multiplication under the full photon unitary. -/
theorem photonGaussianUnitary_field (g : J.fixedSpace) (k : WeightedPhotonKernel)
    (hk : k.val.1 = ((g : softOnePhoton κ) : Lp ℂ 2 photonMeasure))
    (u : RadiationGraphSpace) :
    photonGaussianUnitary BF κ W (kernelField C k u) =ᵐ[W.space.measure]
      fun q => W.firstChaos g q • photonGaussianUnitary BF κ W (radiationGraphInclusion u) q := by
  have hs : k.val.1 ∈ softOnePhoton κ :=
    (congrArg (fun f : Lp ℂ 2 photonMeasure => f ∈ softOnePhoton κ) hk).mpr
      (g : softOnePhoton κ).property
  have h := tensorLift_scalarWienerSegal photonMeasure (softOnePhoton κ) J W
    (softBasis κ) (hardBasis κ) g k.val.1 hk
    (supportedFockEquivalence photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) (photonExponential BF) (radiationGraphInclusion u))
    (supportedFockEquivalence photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) (photonExponential BF) (kernelField C k u))
    (supportedFockEquivalence_soft_segalGraph κ (hardBasis κ) BF C k hs u)
  exact ae_real_smul_of_eq (W.firstChaos g)
    (photonGaussianUnitary BF κ W (radiationGraphInclusion u))
    (photonGaussianUnitary BF κ W (kernelField C k u)) _ _
    (photonGaussianUnitary_apply BF κ W (radiationGraphInclusion u))
    (photonGaussianUnitary_apply BF κ W (kernelField C k u)) h

section Spatial

local instance fieldHardNormedAddCommGroup : NormedAddCommGroup (HardPhotonFock κ) :=
  Submodule.normedAddCommGroup (𝕜 := ℂ) (E := PhotonFock) (HardPhotonFock κ)

-- Align the generic spatial unitary with the direct scalar actions on these fibers.
local instance fieldPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance fieldHardDirectInner : InnerProductSpace ℂ (HardPhotonFock κ) :=
  { (inferInstance : InnerProductSpace ℂ (HardPhotonFock κ)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (HardPhotonFock κ)) }

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [SFinite ν] [IsSeparable ν]

-- Cache the ordinary L² parents used by the outer representative and real multiplication.
local instance fieldHardL2NormedAddCommGroup :
    NormedAddCommGroup (Lp (HardPhotonFock κ) 2 ν) :=
  Lp.instNormedAddCommGroup (E := HardPhotonFock κ) (p := 2) (μ := ν)

local instance fieldHardL2RealNormedSpace :
    NormedSpace ℝ (Lp (HardPhotonFock κ) 2 ν) :=
  Lp.instNormedSpace (𝕜 := ℝ) (E := HardPhotonFock κ) (p := 2) (μ := ν)

set_option backward.isDefEq.respectTransparency.types true in
set_option diagnostics true in
set_option maxHeartbeats 800000 in
/-- The same multiplication identity holds after electronic Fubini slicing. -/
theorem spatialGaussianUnitary_field (g : J.fixedSpace) (k : WeightedPhotonKernel)
    (hk : k.val.1 = ((g : softOnePhoton κ) : Lp ℂ 2 photonMeasure))
    (u : SpatialRadiationGraph ν) :
    (fun q : W.space.Q =>
      (spatialUnitary (X := X) (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
        ν W.space.measure (photonGaussianUnitary BF κ W)
        ((kernelField C k).compLpL 2 ν u) q : Lp (HardPhotonFock κ) 2 ν)) =ᵐ[W.space.measure]
      fun q : W.space.Q =>
        (SMul.smul (M := ℝ) (α := Lp (HardPhotonFock κ) 2 ν) (W.firstChaos g q)
          (spatialUnitary (X := X) (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
            ν W.space.measure (photonGaussianUnitary BF κ W)
            (spatialRadiationInclusion ν u) q : Lp (HardPhotonFock κ) 2 ν) :
          Lp (HardPhotonFock κ) 2 ν) := by
  exact spatialUnitary_intertwining_compLpL
    (X := X) (Q := W.space.Q) (E := RadiationGraphSpace)
    (H := PhotonFock) (K := HardPhotonFock κ)
    ν W.space.measure (photonGaussianUnitary BF κ W)
    (kernelField C k) radiationGraphInclusion (W.firstChaos g) (Lp.stronglyMeasurable _)
    (fun q => photonGaussianUnitary_field BF κ W C g k hk q) u

end Spatial

end GptLean.PhysicalFock
