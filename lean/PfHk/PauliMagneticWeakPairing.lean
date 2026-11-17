import PfHk.PauliMagneticWeakCore
import PfHk.PauliMagneticCoreDensity

/-! The weak spatial field product rule on the actual free reference
domain. The proof transports graph-core representatives to L2 and then
uses ordinary core approximation. -/

noncomputable section
namespace PfHk.PauliMagneticWeakPairing

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalWeyl GptLean.Representability PfHk.PhysicalOperatorDomain
  PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference
open scoped Topology ContDiff InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local instance]
  PfHk.PhysicalFormProductRules.instInnerProductSpaceRealSubtypePreLpNatSectorPhotonModePhotonMeasureMemAddSubgroupPhotonFock_pfHk
  PfHk.PauliMagneticWeakCore.weakCoreRadiationComplex
  PfHk.PauliMagneticWeakCore.weakCoreRadiationReal

attribute [local irreducible] PhysicalPFReference.referenceSubspace inclusion ordinary
  radiationSource radiationRoot weightedKernelSubspace radiationGraphInclusion
  radiationGraphDerivative SmoothCore.reference

/-- The exact weak identity
`⟪A u, T v⟫_ℂ + ⟪T u, A v⟫_ℂ = -⟪J u, DT v⟫_ℂ`.
The four maps are the derivative, field, inclusion and differentiated field. -/
def Pairing {Q H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A T J DT : Q → H) (u v : Q) : Prop :=
  inner ℂ (A u) (T v) + inner ℂ (T u) (A v) = -inner ℂ (J u) (DT v)

private theorem pairing_of_equalities {Q H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A T J DT : Q → H) (u v : Q) {a b c : ℂ}
    (h₁ : inner ℂ (A u) (T v) = a) (h₂ : inner ℂ (T u) (A v) = b)
    (h₃ : inner ℂ (J u) (DT v) = c) (h : a + b = -c) :
    Pairing A T J DT u v :=
  (congrArg₂ (fun z w : ℂ => z + w) h₁ h₂).trans
    (h.trans (congrArg (fun z : ℂ => -z) h₃).symm)

private theorem pairing_scalar_limit {a b c : ℕ → ℂ} {x y z : ℂ}
    (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 y))
    (hc : Tendsto c atTop (𝓝 z)) (hseq : ∀ n, a n + b n = -c n) :
    x + y = -z :=
  tendsto_nhds_unique (ha.add hb)
    (Filter.Tendsto.congr (fun n => (hseq n).symm) hc.neg)

variable {I : Type} [Fintype I] [DecidableEq I]

local instance referenceComplex : NormedSpace ℂ (Reference I (fun _ => 0)) :=
  referenceNormedSpace I (fun _ => 0)

set_option maxHeartbeats 30000 in
def field (C : CanonicalSectorCCR photonMeasure)
    (k : Position I → WeightedPhotonKernel) (hk : Continuous k)
    (M : ℝ) (hM : ∀ x, ‖k x‖ ≤ M) :=
  (spatialField (X := Position I) volume C k hk.aestronglyMeasurable M (ae_of_all _ hM)).comp
    (radiationSource I (fun _ => 0))

attribute [local irreducible] field

theorem core_value_ae {s : Set (Position I)} (a : SmoothCore s) :
    inclusion I (fun _ => 0) a.reference =ᵐ[volume]
      fun x => radiationGraphInclusion (a.rootWave x) := a.reference_value_ae

theorem core_graph_ae {s : Set (Position I)} (a : SmoothCore s) :
    radiationSource I (fun _ => 0) a.reference =ᵐ[volume] a.rootWave := by
  have hm := radiation_matches I (fun _ => 0) a.reference
  filter_upwards [core_value_ae (I := I) a, radiationGraphInclusion.coeFn_compLpL
    (radiationSource I (fun _ => 0) a.reference)] with x hx hq
  apply radiationGraphInclusion_injective_weyl
  exact hq.symm.trans ((congrArg (fun v : WaveSpace I => v x) hm).trans hx)

set_option maxHeartbeats 30000 in
theorem core_ordinary_ae {s : Set (Position I)} (a : SmoothCore s) (i : I) :
    ordinary I (fun _ => 0) i a.reference =ᵐ[volume]
      fun (x : Position I) => radiationGraphInclusion
        (fderiv ℝ (a.rootWave : Position I → RadiationGraphSpace) x (EuclideanSpace.single i 1)) := by
  apply (a.reference_ordinary_ae i).trans
  apply Filter.EventuallyEq.of_eq
  funext x
  exact PauliMagneticWeakCore.fderiv_map_apply
    (E := Position I) (Q := RadiationGraphSpace) (H := PhotonFock)
    radiationGraphInclusion a.rootWave x (EuclideanSpace.single i 1)
    ((a.rootWave_smooth.differentiable (by simp)) x)

theorem core_field_ae (C : CanonicalSectorCCR photonMeasure)
    (k : Position I → WeightedPhotonKernel) (hk : Continuous k)
    (M : ℝ) (hM : ∀ x, ‖k x‖ ≤ M) {s : Set (Position I)} (a : SmoothCore s) :
    field (I := I) C k hk M hM a.reference =ᵐ[volume]
      fun x => kernelField C (k x) (a.rootWave x) := by
  have hf := spatialField_ae (X := Position I) volume C k hk.aestronglyMeasurable M
    (ae_of_all _ hM) (radiationSource I (fun _ => 0) a.reference)
  unfold field
  filter_upwards [hf, core_graph_ae (I := I) a] with x hx hq
  exact hx.trans (congrArg (kernelField C (k x)) hq)

private theorem pair_rep {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ν : Measure X}
    (u v : Lp H 2 ν) (f g : X → H)
    (hu : u =ᵐ[ν] f) (hv : v =ᵐ[ν] g) :
    inner ℂ (E := Lp H 2 ν) u v = ∫ x, inner ℂ (E := H) (f x) (g x) ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu, hv] with x hx hy
  rw [hx, hy]

variable (C : CanonicalSectorCCR photonMeasure)
  (k dk : Position I → WeightedPhotonKernel) (hk : Continuous k) (hdk : Continuous dk)
  (M Md : ℝ) (hM : ∀ x, ‖k x‖ ≤ M) (hMd : ∀ x, ‖dk x‖ ≤ Md)
  (i : I) (hderiv : ∀ x, HasLineDerivAt ℝ k (dk x) x (EuclideanSpace.single i 1))

include hderiv

theorem core_pairing {s t : Set (Position I)} (a : SmoothCore s) (b : SmoothCore t) :
    Pairing (Q := Reference I (fun _ => 0)) (H := WaveSpace I)
      (ordinary I (fun _ => 0) i) (field (I := I) C k hk M hM)
      (inclusion I (fun _ => 0)) (field (I := I) C dk hdk Md hMd)
      a.reference b.reference := by
  have h₁ := pair_rep (X := Position I) (H := PhotonFock) (ν := volume)
    _ _ _ _ (core_ordinary_ae (I := I) a i) (core_field_ae (I := I) C k hk M hM b)
  have h₂ := pair_rep (X := Position I) (H := PhotonFock) (ν := volume)
    _ _ _ _ (core_field_ae (I := I) C k hk M hM a) (core_ordinary_ae (I := I) b i)
  have h₃ := pair_rep (X := Position I) (H := PhotonFock) (ν := volume)
    _ _ _ _ (core_value_ae (I := I) a) (core_field_ae (I := I) C dk hdk Md hMd b)
  have h := PauliMagneticWeakCore.field_smooth_pairing (I := I) C
    k dk hk hdk (EuclideanSpace.single i 1) hderiv
    a.rootWave b.rootWave a.rootWave_smooth b.rootWave_smooth
    a.rootWave_compact b.rootWave_compact
  exact pairing_of_equalities (Q := Reference I (fun _ => 0)) (H := WaveSpace I)
    (ordinary I (fun _ => 0) i) (field (I := I) C k hk M hM)
    (inclusion I (fun _ => 0)) (field (I := I) C dk hdk Md hMd)
    a.reference b.reference h₁ h₂ h₃ h

set_option maxHeartbeats 100000 in
/-- The physical field product rule extends by the free H1/radiation
graph topology, with no derivative of a graph vector assumed. -/
theorem compact_pairing
    (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
    (D : StandardWeylFormCoreDensity W B)
    (s : Set (Position I)) (hs : IsOpen s)
    (u v : Reference I (fun _ => 0))
    (hu : CompactlySupportedIn s u) (hv : CompactlySupportedIn s v) :
    Pairing (Q := Reference I (fun _ => 0)) (H := WaveSpace I)
      (ordinary I (fun _ => 0) i) (field (I := I) C k hk M hM)
      (inclusion I (fun _ => 0)) (field (I := I) C dk hdk Md hMd) u v := by
  unfold Pairing
  have haEx : ∃ a : ℕ → SmoothCore s,
      Tendsto (fun n => (a n).reference) atTop (𝓝 u) :=
    @PauliMagneticCoreDensity.approximate I _ _ W B D s hs u hu
  obtain ⟨a, ha⟩ := haEx
  have hbEx : ∃ b : ℕ → SmoothCore s,
      Tendsto (fun n => (b n).reference) atTop (𝓝 v) :=
    @PauliMagneticCoreDensity.approximate I _ _ W B D s hs v hv
  obtain ⟨b, hb⟩ := hbEx
  have hAu := ((ordinary I (fun _ => 0) i).continuous.tendsto u).comp ha
  have hTv := ((field (I := I) C k hk M hM).continuous.tendsto v).comp hb
  have hl := hAu.inner (𝕜 := ℂ) (E := WaveSpace I) hTv
  have hm := (((field (I := I) C k hk M hM).continuous.tendsto u).comp ha).inner
    (𝕜 := ℂ) (E := WaveSpace I)
    (((ordinary I (fun _ => 0) i).continuous.tendsto v).comp hb)
  have hr := (((inclusion I (fun _ => 0)).continuous.tendsto u).comp ha).inner
    (𝕜 := ℂ) (E := WaveSpace I)
    (((field (I := I) C dk hdk Md hMd).continuous.tendsto v).comp hb)
  exact pairing_scalar_limit hl hm hr (fun n =>
    core_pairing (I := I) (C := C) (k := k) (dk := dk) (hk := hk) (hdk := hdk)
      (M := M) (Md := Md) (hM := hM) (hMd := hMd) (i := i) (hderiv := hderiv)
      (a n) (b n))

end PfHk.PauliMagneticWeakPairing

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
