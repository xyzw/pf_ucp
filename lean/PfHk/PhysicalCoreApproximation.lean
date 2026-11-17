import PfHk.PhysicalOperatorDomain
import PfHk.SmoothCompactMultiplier
import PfHk.SmoothCutoffGeometry
import PfHk.C1ReferenceForm
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! Approximation with prescribed support (`ucp-core-lemma`).

The paper derives supported operator-core approximation from the plain
operator-core property by a cutoff argument. This module carries out that
argument for the actual free Pauli–Fierz graph.

The standard input is `GlobalCoreApproximation`, the operator-core
property of the smooth finite-photon core without any support information.
Multiplication by a smooth cutoff stays in that core. The free graph image
of the product is given by the exact product rule. Graph convergence gives
convergence of the covariant coordinates, so the localized sources
converge. Density of the form domain identifies their limit with the
original source. The conclusion is `AnnularCoreApproximation`, which the
Carleman chain previously took as a background. -/

noncomputable section
namespace PfHk.PhysicalCoreApproximation

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.ElectronicH1Multiplier GptLean.Representability
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCutoffCommutator PfHk.PhysicalOperatorDomain
  PfHk.SmoothCutoffBounds
open scoped Topology InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false

section Representatives

variable {X K : Type*} [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup K]

/-- An L² class with a continuous representative vanishing off `T`. -/
def SupportedRep (T : Set X) (f : Lp K 2 μ) : Prop :=
  ∃ F : X → K, Continuous F ∧ (∀ x, x ∉ T → F x = 0) ∧ f =ᵐ[μ] F

theorem SupportedRep.zero (T : Set X) : SupportedRep T (0 : Lp K 2 μ) :=
  ⟨0, continuous_zero, fun _ _ => rfl, Lp.coeFn_zero K 2 μ⟩

theorem SupportedRep.add {T : Set X} {f g : Lp K 2 μ} (hf : SupportedRep T f)
    (hg : SupportedRep T g) : SupportedRep T (f + g) := by
  rcases hf with ⟨F, hF, hF0, hfF⟩
  rcases hg with ⟨G, hG, hG0, hgG⟩
  refine ⟨fun x => F x + G x, hF.add hG, fun x hx => ?_, ?_⟩
  · show F x + G x = 0
    rw [hF0 x hx, hG0 x hx, add_zero]
  · filter_upwards [Lp.coeFn_add f g, hfF, hgG] with x h h₁ h₂
    rw [h, Pi.add_apply, h₁, h₂]

theorem SupportedRep.sum {ι : Type*} {T : Set X} (s : Finset ι) (f : ι → Lp K 2 μ)
    (hf : ∀ i ∈ s, SupportedRep T (f i)) : SupportedRep T (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using SupportedRep.zero (K := K) (μ := μ) T
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

variable [InnerProductSpace ℂ K]

theorem SupportedRep.smul {T : Set X} {f : Lp K 2 μ} (c : ℂ) (hf : SupportedRep T f) :
    SupportedRep T (c • f) := by
  rcases hf with ⟨F, hF, hF0, hfF⟩
  refine ⟨fun x => c • F x, hF.const_smul c, fun x hx => ?_, ?_⟩
  · show c • F x = 0
    rw [hF0 x hx, smul_zero]
  · filter_upwards [Lp.coeFn_smul c f, hfF] with x h h₁
    rw [h, Pi.smul_apply, h₁]

/-- A continuous real weight vanishing off `T` localizes every continuous
representative. -/
theorem SupportedRep.realMultiplier {T : Set X} (w : X → ℝ) (hw : Continuous w)
    (hwT : ∀ x, x ∉ T → w x = 0) (hm : AEStronglyMeasurable w μ) (B : ℝ)
    (hB : ∀ᵐ x ∂μ, |w x| ≤ B) {f : Lp K 2 μ} {F : X → K} (hF : Continuous F)
    (hfF : f =ᵐ[μ] F) :
    SupportedRep T (PhotonLocalization.realL2Multiplier w hm B hB f) := by
  refine ⟨fun x => w x • F x, hw.smul hF, fun x hx => ?_, ?_⟩
  · show w x • F x = 0
    rw [hwT x hx, zero_smul]
  · filter_upwards [PhotonLocalization.realL2Multiplier_apply w hm B hB f, hfF] with x h h₁
    rw [h, h₁]

theorem ofReal_smul_eq (r : ℝ) (v : K) : ((r : ℝ) : ℂ) • v = r • v :=
  Complex.coe_smul r v

end Representatives

section Scaling

variable {X F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Pointwise scaling of a vector-valued function by a real weight. -/
def realScale (z : X → ℝ) (f : X → F) : X → F := fun x => ((z x : ℝ) : ℂ) • f x

theorem realScale_eq_zero_of_weight (z : X → ℝ) (f : X → F) {x : X} (h : z x = 0) :
    realScale z f x = 0 := by
  show ((z x : ℝ) : ℂ) • f x = 0
  rw [h, Complex.ofReal_zero, zero_smul]

theorem realScale_eq_zero_of_value (z : X → ℝ) (f : X → F) {x : X} (h : f x = 0) :
    realScale z f x = 0 := by
  show ((z x : ℝ) : ℂ) • f x = 0
  rw [h, smul_zero]

theorem support_realScale_subset_left (z : X → ℝ) (f : X → F) :
    Function.support (realScale z f) ⊆ Function.support z :=
  fun _ hx => Function.mem_support.mpr fun hz =>
    Function.mem_support.mp hx (realScale_eq_zero_of_weight z f hz)

theorem support_realScale_subset_right (z : X → ℝ) (f : X → F) :
    Function.support (realScale z f) ⊆ Function.support f :=
  fun _ hx => Function.mem_support.mpr fun hf =>
    Function.mem_support.mp hx (realScale_eq_zero_of_value z f hf)

theorem map_realScale (T : F →L[ℂ] G) (z : X → ℝ) (f : X → F) (x : X) :
    T (realScale z f x) = ((z x : ℝ) : ℂ) • T (f x) :=
  map_smul T ((z x : ℝ) : ℂ) (f x)

theorem map_realScale_eq_zero (T : F →L[ℂ] G) (z : X → ℝ) (f : X → F) {x : X}
    (h : T (f x) = 0) : T (realScale z f x) = 0 := by
  rw [map_realScale, h, smul_zero]

theorem realScale_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] {z : E → ℝ} {f : E → F}
    (hz : ContDiff ℝ (⊤ : ℕ∞) z) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (realScale z f) :=
  (Complex.ofRealCLM.contDiff.comp hz).smul hf

end Scaling

/-- A smooth compactly supported function equal to one on a compact set
and supported in a given open neighborhood. -/
theorem exists_smooth_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K s : Set E} (hK : IsCompact K) (hs : IsOpen s) (hKs : K ⊆ s) :
    ∃ z : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) z ∧ HasCompactSupport z ∧ tsupport z ⊆ s ∧
      ∀ x ∈ K, z x = 1 := by
  obtain ⟨L, hL, hKL, hLs⟩ := exists_compact_between hK hs hKs
  obtain ⟨f, hf1, hf0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ E) (n := (⊤ : ℕ∞)) hK.isClosed hKL
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, HasCompactSupport.intro hL hf0, ?_, ?_⟩
  · exact (closure_minimal
      (fun x hx => by_contra fun hxL => Function.mem_support.mp hx (hf0 x hxL))
      hL.isClosed).trans hLs
  · intro x hx
    exact hf1.self_of_nhdsSet x hx

local instance coreApproximationPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

variable {I : Type} [Fintype I] [DecidableEq I]

local instance coreApproximationWaveDirectInner : InnerProductSpace ℂ (WaveSpace I) :=
  { (inferInstance : InnerProductSpace ℂ (WaveSpace I)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (WaveSpace I)) }

theorem coordinateDerivative_contDiff (f : EuclideanSpace ℝ I → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : I) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative f i) :=
  (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

theorem multiplier_ae (a : DifferentiableMultiplier I) (u : WaveSpace I) :
    a.multiplier (H := PhotonFock) u =ᵐ[volume] fun x => a.weight x • u x :=
  PhotonLocalization.realL2Multiplier_apply a.weight
    a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded) u

/-- A cutoff equal to one on the support of a wave function fixes it. -/
theorem multiplier_eq_self_of_supported (a : DifferentiableMultiplier I)
    {K : Set (Position I)} (h1 : ∀ x ∈ K, a.weight x = 1) (ψ : WaveSpace I)
    (hψ : ∀ᵐ x ∂volume, x ∉ K → ψ x = 0) :
    a.multiplier (H := PhotonFock) ψ = ψ := by
  apply Lp.ext
  filter_upwards [multiplier_ae a ψ, hψ] with x hx h0
  by_cases hxK : x ∈ K
  · rw [hx, h1 x hxK, one_smul]
  · rw [hx, h0 hxK, smul_zero]

omit [DecidableEq I] in
theorem compactSource_of_supportedRep {T s : Set (Position I)} (hT : IsCompact T)
    (hTs : T ⊆ s) {f : WaveSpace I} (h : SupportedRep T f) : Nonempty (CompactSource s f) := by
  rcases h with ⟨F, hF, hF0, hfF⟩
  have hsub : tsupport F ⊆ T :=
    closure_minimal (fun x hx => by_contra fun hxT => Function.mem_support.mp hx (hF0 x hxT))
      hT.isClosed
  exact ⟨⟨F, hF, HasCompactSupport.intro hT hF0, hsub.trans hTs, hfF⟩⟩

/-! ### Cutoff products in the smooth core -/

/-- Multiplication of a core vector by a smooth real cutoff. The product
stays in the smooth finite-photon core and is supported in the support of
the cutoff. -/
def coreCutoff {t s : Set (Position I)} (a : SmoothCore t) (z : Position I → ℝ)
    (hz : ContDiff ℝ (⊤ : ℕ∞) z) (hs : tsupport z ⊆ s) : SmoothCore s where
  representative := realScale z a.representative
  smooth := realScale_contDiff hz a.smooth
  compact := a.compact.mono (support_realScale_subset_right z a.representative)
  support := (closure_mono (support_realScale_subset_left z a.representative)).trans hs
  photonCutoff := a.photonCutoff
  photonFinite := fun x n hn => by
    let T : FullRadiationGraph →L[ℂ] Sector photonMeasure n :=
      (lp.evalCLM ℂ (Sector photonMeasure) 2 n).comp fullRadiationInclusion
    exact map_realScale_eq_zero T z a.representative (x := x) (a.photonFinite x n hn)

omit [DecidableEq I] in
theorem coreCutoff_value {t s : Set (Position I)} (a : SmoothCore t) (z : Position I → ℝ)
    (hz : ContDiff ℝ (⊤ : ℕ∞) z) (hs : tsupport z ⊆ s) (x : Position I) :
    fullRadiationInclusion ((coreCutoff a z hz hs).representative x) =
      z x • fullRadiationInclusion (a.representative x) :=
  (map_realScale fullRadiationInclusion z a.representative x).trans
    (ofReal_smul_eq (z x) (fullRadiationInclusion (a.representative x)))

/-- The reference vector of the cutoff product is the scalar multiple of
the original reference vector. -/
theorem coreCutoff_reference {t s : Set (Position I)} (a : SmoothCore t)
    (ζ : DifferentiableMultiplier I) (hz : ContDiff ℝ (⊤ : ℕ∞) ζ.weight)
    (hs : tsupport ζ.weight ⊆ s) :
    (coreCutoff a ζ.weight hz hs).reference =
      PhysicalPFScalarMultiplier.multiply (fun _ => 0) ζ a.reference := by
  apply inclusion_injective I (fun _ => 0)
  apply Lp.ext
  have hv := PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) ζ a.reference
  have h₄ := Filter.EventuallyEq.of_eq (l := ae (volume : Measure (Position I)))
    (congrArg (fun w : WaveSpace I => (w : Position I → PhotonFock)) hv)
  filter_upwards [(coreCutoff a ζ.weight hz hs).reference_value_ae, a.reference_value_ae,
    multiplier_ae ζ (inclusion I (fun _ => 0) a.reference), h₄] with x h₁ h₂ h₃ h₄'
  exact h₁.trans ((coreCutoff_value a ζ.weight hz hs x).trans
    (h₄'.trans (h₃.trans (congrArg (fun q : PhotonFock => ζ.weight x • q) h₂))).symm)

/-! ### The free graph under cutoff multiplication -/

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

/-- The cutoff commutator `-i ∇ζ·D - (Δζ)/2` of the free operator. -/
def freeCommutator (ζ : TwiceDifferentiableMultiplier I) (u : Reference I (fun _ => 0)) :
    WaveSpace I :=
  scalarCommutator (H := PhotonFock) ζ (inclusion I (fun _ => 0) u)
    (fun i => covariant I (fun _ => 0) C κ hκ M hbound e i u)

/-- Product rule in the free operator graph. -/
theorem freeGraph_localize (ζ : TwiceDifferentiableMultiplier I)
    {u : Reference I (fun _ => 0)} {f : WaveSpace I}
    (hu : FreeGraph C κ hκ M hbound e u f) :
    FreeGraph C κ hκ M hbound e (PhysicalPFScalarMultiplier.multiply (fun _ => 0) ζ.scalar u)
      (ζ.scalar.multiplier (H := PhotonFock) f + freeCommutator C κ hκ M hbound e ζ u) := by
  unfold FreeGraph OperatorGraph at hu ⊢
  rcases hu with ⟨h, hp⟩
  refine ⟨h.localize (fun _ => 0) ζ.scalar, ?_⟩
  have hl := operatorPair_localize (fun _ => 0) C κ hκ M hbound e
    (fun _ _ => 0) (fun _ => 0) (fun _ => 0) ζ hp
  have hc : PhysicalCutoffCommutator.commutator (fun _ => 0) C κ hκ M hbound e
      (fun _ _ => 0) (fun _ => 0) (fun _ => 0) ζ u h = freeCommutator C κ hκ M hbound e ζ u := by
    unfold PhysicalCutoffCommutator.commutator freeCommutator
    exact congrArg (scalarCommutator (H := PhotonFock) ζ (inclusion I (fun _ => 0) u))
      (funext fun i => by simp only [externalCovariant, roughMultiply_zero, add_zero])
  exact (congrArg (fun w : WaveSpace I =>
    IsOperatorPair (fun _ => 0) C κ hκ M hbound e (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
      (PhysicalPFScalarMultiplier.multiply (fun _ => 0) ζ.scalar u)
      (h.localize (fun _ => 0) ζ.scalar) (ζ.scalar.multiplier (H := PhotonFock) f + w)) hc).mp hl

/-- The commutator depends continuously on the wave function and its
covariant coordinates. -/
theorem freeCommutator_tendsto (ζ : TwiceDifferentiableMultiplier I)
    {u : ℕ → Reference I (fun _ => 0)} {v : Reference I (fun _ => 0)}
    (hψ : Tendsto (fun n => inclusion I (fun _ => 0) (u n)) atTop
      (𝓝 (inclusion I (fun _ => 0) v)))
    (hD : ∀ i, Tendsto (fun n => covariant I (fun _ => 0) C κ hκ M hbound e i (u n)) atTop
      (𝓝 (covariant I (fun _ => 0) C κ hκ M hbound e i v))) :
    Tendsto (fun n => freeCommutator C κ hκ M hbound e ζ (u n)) atTop
      (𝓝 (freeCommutator C κ hκ M hbound e ζ v)) := by
  unfold freeCommutator scalarCommutator singleCutoffError
  apply tendsto_finsetSum
  intro i _
  exact (((((ζ.derivative i).multiplier (H := PhotonFock)).continuous.tendsto _).comp
      (hD i)).const_smul _).add
    (((((ζ.derivative i).derivativeMultiplier (H := PhotonFock) i).continuous.tendsto _).comp
      hψ).const_smul _)

/-- The free graph is single valued once the form domain is dense. -/
theorem freeGraph_source_unique (hdense : DenseRange (inclusion I (fun _ => 0)))
    {u : Reference I (fun _ => 0)} {f f' : WaveSpace I}
    (h : FreeGraph C κ hκ M hbound e u f) (h' : FreeGraph C κ hκ M hbound e u f') :
    f = f' := by
  have h₁ := (freeGraph_iff C κ hκ M hbound e u f).mp h
  have h₂ := (freeGraph_iff C κ hκ M hbound e u f').mp h'
  exact hdense.eq_of_inner_right ℂ fun v => (h₁ v).symm.trans (h₂ v)

/-! ### Continuous representatives of the localized sources -/

theorem core_covariant_ae {t : Set (Position I)} (a : SmoothCore t) (j : I) :
    covariant I (fun _ => 0) C κ hκ M hbound e j a.reference =ᵐ[volume]
      C1ReferenceCore.covariantFunction C κ e a.rootWave j := by
  unfold SmoothCore.reference
  exact C1ReferenceCore.reference_covariant C κ hκ M hbound e a.rootWave a.rootWave_memLp
    a.value_smooth a.value_compact j

theorem covariantFunction_continuous (hκc : ∀ i, Continuous (κ i))
    {t : Set (Position I)} (a : SmoothCore t) (j : I) :
    Continuous (C1ReferenceCore.covariantFunction C κ e a.rootWave j) := by
  unfold C1ReferenceCore.covariantFunction C1ReferenceCore.derivativeFunction
  exact (((a.value_smooth.continuous_fderiv (by simp)).clm_apply continuous_const).const_smul
      (-Complex.I)).sub
    ((((kernelField_continuous C).comp (hκc j)).clm_apply
      a.rootWave_smooth.continuous).const_smul (e : ℂ))

/-- The localized source of a core vector has a continuous representative
vanishing wherever the cutoff vanishes on a neighborhood. -/
theorem localized_source_supportedRep (hκc : ∀ i, Continuous (κ i))
    (ζ : TwiceDifferentiableMultiplier I) {T : Set (Position I)}
    (hT : ∀ x, x ∉ T → ζ.scalar.weight =ᶠ[𝓝 x] fun _ => (0 : ℝ))
    (hsecond : ∀ i, Continuous ((ζ.derivative i).gradient i))
    {t : Set (Position I)} (a : SmoothCore t) {g : WaveSpace I}
    (G : CompactSource (Set.univ : Set (Position I)) g) :
    SupportedRep T (ζ.scalar.multiplier (H := PhotonFock) g +
      freeCommutator C κ hκ M hbound e ζ a.reference) := by
  have h₁ : SupportedRep T (ζ.scalar.multiplier (H := PhotonFock) g) :=
    SupportedRep.realMultiplier ζ.scalar.weight ζ.scalar.differentiable.continuous
      (fun x hx => (hT x hx).eq_of_nhds) _ _ _ G.continuous G.agrees
  have hvalue : Continuous (fun x => fullRadiationInclusion (a.representative x)) :=
    fullRadiationInclusion.continuous.comp a.smooth.continuous
  have h₂ : SupportedRep T (freeCommutator C κ hκ M hbound e ζ a.reference) := by
    unfold freeCommutator scalarCommutator singleCutoffError
    apply SupportedRep.sum
    intro i _
    apply SupportedRep.add
    · apply SupportedRep.smul
      exact SupportedRep.realMultiplier (ζ.derivative i).weight
        (ζ.derivative i).differentiable.continuous
        (fun x hx => (congrFun (ζ.derivative_weight i) x).trans
          (gradient_eq_zero_of_eventually_constant ζ.scalar (hT x hx) i)) _ _ _
        (covariantFunction_continuous C κ e hκc a i) (core_covariant_ae C κ hκ M hbound e a i)
    · apply SupportedRep.smul
      exact SupportedRep.realMultiplier ((ζ.derivative i).gradient i) (hsecond i)
        (fun x hx => second_gradient_eq_zero_of_eventually_constant ζ (hT x hx) i i) _ _ _
        hvalue a.reference_value_ae
  exact h₁.add h₂

/-! ### Supported approximation from unlocalized approximation -/

/-- Standard operator-core property of the smooth finite-photon core for
the free Pauli–Fierz graph. No support information is retained, so this
is the statement that the core is an operator core. -/
structure GlobalCoreApproximation : Prop where
  approximate : ∀ (u : Reference I (fun _ => 0)) (f : WaveSpace I),
    FreeGraph C κ hκ M hbound e u f →
    ∃ a : ℕ → SmoothCore (Set.univ : Set (Position I)), ∃ g : ℕ → WaveSpace I,
      (∀ n, FreeGraph C κ hκ M hbound e (a n).reference (g n)) ∧
      (∀ n, Nonempty (CompactSource (Set.univ : Set (Position I)) (g n))) ∧
      Tendsto (fun n => inclusion I (fun _ => 0) (a n).reference) atTop
        (𝓝 (inclusion I (fun _ => 0) u)) ∧ Tendsto g atTop (𝓝 f)

/-- The cutoff argument for one cutoff. The cutoff equals one on the
compact set carrying the wave function and is supported in the prescribed
open neighborhood. -/
theorem localize_approximation (hκc : ∀ i, Continuous (κ i))
    (hdense : DenseRange (inclusion I (fun _ => 0)))
    (ζ : TwiceDifferentiableMultiplier I) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ.scalar.weight)
    (hζc : HasCompactSupport ζ.scalar.weight)
    (hsecond : ∀ i, Continuous ((ζ.derivative i).gradient i))
    {K s : Set (Position I)} (hζs : tsupport ζ.scalar.weight ⊆ s)
    (hζ1 : ∀ x ∈ K, ζ.scalar.weight x = 1)
    {u : Reference I (fun _ => 0)} {f : WaveSpace I}
    (hu : FreeGraph C κ hκ M hbound e u f)
    (hsupp : ∀ᵐ x ∂volume, x ∉ K → inclusion I (fun _ => 0) u x = 0)
    (a : ℕ → SmoothCore (Set.univ : Set (Position I))) (g : ℕ → WaveSpace I)
    (hag : ∀ n, FreeGraph C κ hκ M hbound e (a n).reference (g n))
    (hgc : ∀ n, Nonempty (CompactSource (Set.univ : Set (Position I)) (g n)))
    (ha : Tendsto (fun n => inclusion I (fun _ => 0) (a n).reference) atTop
      (𝓝 (inclusion I (fun _ => 0) u)))
    (hgf : Tendsto g atTop (𝓝 f)) :
    ∃ b : ℕ → SmoothCore s, ∃ g' : ℕ → WaveSpace I,
      (∀ n, FreeGraph C κ hκ M hbound e (b n).reference (g' n)) ∧
      (∀ n, Nonempty (CompactSource s (g' n))) ∧
      Tendsto (fun n => inclusion I (fun _ => 0) (b n).reference) atTop
        (𝓝 (inclusion I (fun _ => 0) u)) ∧ Tendsto g' atTop (𝓝 f) := by
  have hfix : ζ.scalar.multiplier (H := PhotonFock) (inclusion I (fun _ => 0) u) =
      inclusion I (fun _ => 0) u :=
    multiplier_eq_self_of_supported ζ.scalar hζ1 _ hsupp
  have hu' : PhysicalPFScalarMultiplier.multiply (fun _ => 0) ζ.scalar u = u :=
    inclusion_injective I (fun _ => 0)
      ((PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) ζ.scalar u).trans hfix)
  have hform := freeGraph_form_convergence C κ hκ M hbound e
    (u := fun n => (a n).reference) (v := u) (f := g) (g := f) hag hu ha hgf
  have hloc := freeGraph_localize C κ hκ M hbound e ζ hu
  have hlimit : ζ.scalar.multiplier (H := PhotonFock) f +
      freeCommutator C κ hκ M hbound e ζ u = f :=
    (freeGraph_source_unique C κ hκ M hbound e hdense hu
      ((congrArg (fun w : Reference I (fun _ => 0) => FreeGraph C κ hκ M hbound e w
        (ζ.scalar.multiplier (H := PhotonFock) f + freeCommutator C κ hκ M hbound e ζ u))
        hu').mp hloc)).symm
  have hvalue (n : ℕ) : inclusion I (fun _ => 0) (coreCutoff (a n) ζ.scalar.weight hζ hζs).reference =
      ζ.scalar.multiplier (H := PhotonFock) (inclusion I (fun _ => 0) (a n).reference) :=
    (congrArg (inclusion I (fun _ => 0)) (coreCutoff_reference (a n) ζ.scalar hζ hζs)).trans
      (PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) ζ.scalar (a n).reference)
  refine ⟨fun n => coreCutoff (a n) ζ.scalar.weight hζ hζs,
    fun n => ζ.scalar.multiplier (H := PhotonFock) (g n) +
      freeCommutator C κ hκ M hbound e ζ (a n).reference, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (congrArg (fun w : Reference I (fun _ => 0) => FreeGraph C κ hκ M hbound e w
      (ζ.scalar.multiplier (H := PhotonFock) (g n) +
        freeCommutator C κ hκ M hbound e ζ (a n).reference))
      (coreCutoff_reference (a n) ζ.scalar hζ hζs)).mpr
        (freeGraph_localize C κ hκ M hbound e ζ (hag n))
  · intro n
    have hG := hgc n
    rcases hG with ⟨G⟩
    exact compactSource_of_supportedRep hζc hζs
      (localized_source_supportedRep C κ hκ M hbound e hκc ζ
        (fun x hx => notMem_tsupport_iff_eventuallyEq.mp hx) hsecond (a n) G)
  · have hc := ((ζ.scalar.multiplier (H := PhotonFock)).continuous.tendsto
      (inclusion I (fun _ => 0) u)).comp ha
    exact Filter.Tendsto.congr (fun n => (hvalue n).symm)
      (hc.mono_right (le_of_eq (congrArg (fun w : WaveSpace I => 𝓝 w) hfix)))
  · have hc := (((ζ.scalar.multiplier (H := PhotonFock)).continuous.tendsto f).comp hgf).add
      (freeCommutator_tendsto C κ hκ M hbound e ζ ha hform.1)
    exact hc.mono_right (le_of_eq (congrArg (fun w : WaveSpace I => 𝓝 w) hlimit))

/-- Approximation with prescribed support, the paper's `ucp-core-lemma` in
the graph of the free Pauli–Fierz operator. The form factors are
continuous, the form domain is dense, and the smooth finite-photon core is
an operator core. Then every operator vector with compact support is a
graph limit of core vectors supported in any prescribed open neighborhood
of its support, with continuous compactly supported images. -/
theorem annular_of_global (hκc : ∀ i, Continuous (κ i))
    (hdense : DenseRange (inclusion I (fun _ => 0)))
    (hglobal : GlobalCoreApproximation C κ hκ M hbound e) :
    AnnularCoreApproximation C κ hκ M hbound e := by
  refine ⟨fun u f K s hu hK hs hKs hsupp => ?_⟩
  have hcut := exists_smooth_cutoff hK hs hKs
  rcases hcut with ⟨z, hz, hzc, hzs, hz1⟩
  have hw : (compactMultiplier z hz hzc).scalar.weight = z := compactMultiplier_weight z hz hzc
  have hgl := hglobal.approximate u f hu
  rcases hgl with ⟨a, g, hag, hgc, ha, hgf⟩
  exact localize_approximation C κ hκ M hbound e hκc hdense (compactMultiplier z hz hzc)
    ((congrArg (ContDiff ℝ (⊤ : ℕ∞)) hw).mpr hz)
    ((congrArg HasCompactSupport hw).mpr hzc)
    (fun i => (congrArg Continuous (funext fun x => compactMultiplier_second z hz hzc i i x)).mpr
      (coordinateDerivative_contDiff _ (coordinateDerivative_contDiff z hz i) i).continuous)
    ((congrArg (fun w : Position I → ℝ => tsupport w ⊆ s) hw).mpr hzs)
    (fun x hx => (congrFun hw x).trans (hz1 x hx))
    hu hsupp a g hag hgc ha hgf

end PfHk.PhysicalCoreApproximation
