import PfHk.PauliMagneticOperatorAlgebra
import PfHk.PauliMagneticOperatorForm
import PfHk.PauliMagneticRelative
import PfHk.PhysicalExternalRealization
import PfHk.PauliClassicalFormSymmetry
import PfHk.PauliQuantumFormSymmetry
import PfHk.PauliMagneticOperatorAmplification

/-! The global orbital and Zeeman form has the free comparison operator
domain. Its actual L2 perturbation is constructed from raw coefficient
multipliers, and ordinary Kato--Rellich identifies the weak graph. -/

noncomputable section
namespace PfHk.PauliMagneticOperatorRealization

open PfHk.KatoRellichBackground
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000



open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain PfHk.PhysicalFieldRegularity
  PfHk.PauliSpin PfHk.PauliMagneticRelative PfHk.PhysicalExternalSource
  PfHk.PhysicalExternalOperator PfHk.FriedrichsDivergenceBackground

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] inclusion ordinary radiation roughMultiply
  referenceSubspace FreeGraph IsComparisonPair total PauliMagneticOperator.quantum
  FiniteFiberL2.bundle PauliMagneticClassicalOperator.zeeman

variable {N : ℕ}
  (a : PhysicalExternalCoefficients.Data N)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
  (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)

variable (S : CoordinateSobolev.Data PhotonFock N)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
  (joint : CoordinateComparisonSpectral.Data spectral)
  (hD : HaslerHerbstDomain C κ hκ M hbound e)
  {p : ℝ} (hp : 2 < p) (hBp : ∀ n μ, MemLp (B n μ) (ENNReal.ofReal p) volume)

include hD in
theorem comparison (u : PauliReference.Ref N) (g : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hg : ∀ s, FreeGraph C κ hκ M hbound e (u s) (g s)) (s : SpinIndex N) :
    ComparisonDomain (fun _ => 0) (u s) := (hD (u s)).mp ⟨g s, hg s⟩

include S spectral joint hD in
theorem products (u : PauliReference.Ref N) (g : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hg : ∀ s, FreeGraph C κ hκ M hbound e (u s) (g s)) (s : SpinIndex N) :
    Products a C κ hκ M hbound e (u s) :=
  products_of_comparison a C κ hκ M hbound e (u s) S spectral joint
    (comparison C κ hκ M hbound e hD u g hg s)

include S spectral joint hD hp hBp in
theorem magneticMultipliers (u : PauliReference.Ref N)
    (g : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hg : ∀ s, FreeGraph C κ hκ M hbound e (u s) (g s)) :
    ∀ n μ s, HasMultiplier (CoordinateSobolev.coordinateCoefficient n (B n μ))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) :=
  classical_multipliers S spectral joint B hp hBp u
    (comparison C κ hκ M hbound e hD u g hg)

def perturbation (u : PauliReference.Ref N)
    (g : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hg : ∀ s, FreeGraph C κ hκ M hbound e (u s) (g s)) (s : SpinIndex N) :
    WaveSpace (Fin N × Fin 3) :=
  total a C κ hκ M hbound e (u s) (products a C κ hκ M hbound e S spectral joint hD u g hg s) +
    PauliMagneticClassicalOperator.zeeman B u
      (magneticMultipliers C κ hκ M hbound e B S spectral joint hD hp hBp u g hg) s +
    PauliMagneticOperator.quantum F χ hUV C e u s

def source (u : PauliReference.Ref N)
    (g : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hg : ∀ s, FreeGraph C κ hκ M hbound e (u s) (g s)) (s : SpinIndex N) :
    WaveSpace (Fin N × Fin 3) :=
  g s + perturbation a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp u g hg s


attribute [local irreducible] source perturbation

include S spectral joint hD hp hBp in
/-- Every source component is obtained from the actual weak form on the
free operator domain. The magnetic form is realized only at this step. -/
theorem source_pair
    (friedrichs : StandardFriedrichsDivergence) (KR : StandardKatoRellich)
    (hG : HaslerHerbstGraphNorm C κ hκ M hbound e)
    (hSA : SelfAdjointGraph (PhysicalExternalOperator.freeHilbertGraph
      (fun _ => 0) C κ hκ M hbound e))
    (u : PauliReference.Ref N) (g : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hg : ∀ s, FreeGraph C κ hκ M hbound e (u s) (g s))
    (hu : PauliGroundState.Domain a.vector a.positive a.negative u) :
    IsOperatorPair a C κ hκ M hbound e F χ hUV B u hu
      (source a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp u g hg) := by
  intro z hz
  have ho (s : SpinIndex N) :
      PhysicalCutoffCommutator.IsOperatorPair (fun _ => 0) C κ hκ M hbound e
        a.vector a.positive a.negative (u s) (hu s)
        (g s + total a C κ hκ M hbound e (u s)
          (products a C κ hκ M hbound e S spectral joint hD u g hg s)) :=
    (PhysicalExternalOperator.operatorPair_iff_free_total a S spectral joint friedrichs KR
      C κ hκ M hbound e hD hG hSA (u s) _ (hu s)).mpr ⟨g s, hg s, rfl⟩
  have hos : PauliOrbitalForm.form C κ hκ M hbound e a.vector a.positive a.negative
      z u hz hu = ∑ s, inner ℂ
        (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (g s + total a C κ hκ M hbound e (u s)
          (products a C κ hκ M hbound e S spectral joint hD u g hg s)) :=
    Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => ho s (z s) (hz s))
  have hc := classical_pairing B z u
    (magneticMultipliers C κ hκ M hbound e B S spectral joint hD hp hBp u g hg)
  unfold source perturbation
  exact assembled_source_pairing (H := WaveSpace (Fin N × Fin 3))
    (form a C κ hκ M hbound e F χ hUV B z u hz hu)
    (PauliOrbitalForm.form C κ hκ M hbound e a.vector a.positive a.negative z u hz hu)
    (PauliSquareForm.classicalForm B z u)
    (∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (PauliMagneticOperator.quantum F χ hUV C e u s))
    (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) g
    (fun s => total a C κ hκ M hbound e (u s)
      (products a C κ hκ M hbound e S spectral joint hD u g hg s))
    (PauliMagneticClassicalOperator.zeeman B u
      (magneticMultipliers C κ hκ M hbound e B S spectral joint hD hp hBp u g hg))
    (PauliMagneticOperator.quantum F χ hUV C e u) rfl hos hc rfl

omit S spectral joint hD hp hBp in
theorem form_hermitian (z u : PauliReference.Ref N)
    (hz : PauliGroundState.Domain a.vector a.positive a.negative z)
    (hu : PauliGroundState.Domain a.vector a.positive a.negative u) :
    star (form a C κ hκ M hbound e F χ hUV B z u hz hu) =
      form a C κ hκ M hbound e F χ hUV B u z hu hz := by
  have ho : star (PauliOrbitalForm.form C κ hκ M hbound e a.vector a.positive a.negative
      z u hz hu) = PauliOrbitalForm.form C κ hκ M hbound e a.vector a.positive a.negative
      u z hu hz := by
    unfold PauliOrbitalForm.form
    rw [star_sum]
    exact Finset.sum_congr rfl fun s _ =>
      externalForm_conj (fun _ => 0) C κ hκ M hbound e a.vector a.positive a.negative
        (z s) (u s) (hz s) (hu s)
  simp only [form, star_add, ho,
    PauliClassicalFormSymmetry.classicalForm_hermitian,
    PauliMagneticFormRules.quantum_pairing_hermitian]

abbrev SpinWave (N : ℕ) := PiLp 2 (fun _ : SpinIndex N => WaveSpace (Fin N × Fin 3))

def spinInclusion (u : PauliReference.Ref N) : SpinWave N :=
  WithLp.toLp 2 (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s))

theorem spinInclusion_injective : Function.Injective (spinInclusion (N := N)) := by
  intro u v h
  funext s
  exact inclusion_injective (Fin N × Fin 3) (fun _ => 0)
    (congrArg (fun w : SpinWave N => w s) h)

private theorem toLp_norm (v : SpinIndex N → WaveSpace (Fin N × Fin 3)) :
    ‖WithLp.toLp 2 v‖ = ‖FiniteFiberL2.bundle v‖ :=
  (FiniteFiberL2.isometry.norm_map (WithLp.toLp 2 v)).symm

private theorem spinInclusion_norm (u : PauliReference.Ref N) :
    ‖spinInclusion u‖ = ‖PauliReference.wave u‖ := toLp_norm _

include S spectral joint hD hp hBp in
theorem perturbation_free_relative
    (hG : HaslerHerbstGraphNorm C κ hκ M hbound e) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (u : PauliReference.Ref N) (g : SpinIndex N → WaveSpace (Fin N × Fin 3))
        (hg : ∀ s, FreeGraph C κ hκ M hbound e (u s) (g s)),
      ‖FiniteFiberL2.bundle
        (perturbation a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp u g hg)‖ ≤
        ε * ‖FiniteFiberL2.bundle g‖ + K * ‖PauliReference.wave u‖ := by
  let X := {q : PauliReference.Ref N × (SpinIndex N → WaveSpace (Fin N × Fin 3)) //
    ∀ s, FreeGraph C κ hκ M hbound e (q.1 s) (q.2 s)}
  let u : X → PauliReference.Ref N := fun x => x.val.1
  let g : X → SpinIndex N → WaveSpace (Fin N × Fin 3) := fun x => x.val.2
  let L (x : X) (s : SpinIndex N) : WaveSpace (Fin N × Fin 3) := Classical.choose
    (comparison C κ hκ M hbound e hD (u x) (g x) x.property s)
  have hL (x : X) (s : SpinIndex N) :
      IsComparisonPair (fun _ => 0) (u x s) (L x s) := Classical.choose_spec
    (comparison C κ hκ M hbound e hD (u x) (g x) x.property s)
  have ht := total_comparison_relative F χ hUV C e a S spectral joint κ hκ M hbound
    B hp hBp u L hL
    (fun x => products a C κ hκ M hbound e S spectral joint hD (u x) (g x) x.property)
    (fun x => magneticMultipliers C κ hκ M hbound e B S spectral joint hD hp hBp
      (u x) (g x) x.property)
  have hf := InfinitesimalBound.comparison
    (mul_nonneg hG.bound_nonneg (Nat.cast_nonneg (Fintype.card (SpinIndex N))))
    (fun x : X => norm_nonneg (FiniteFiberL2.bundle (g x)))
    (fun x : X => norm_nonneg (PauliReference.wave (u x)))
    (fun x : X => finite_comparison_le C e κ hκ M hbound hG (u x) (g x) (L x)
      x.property (hL x)) ht
  intro ε hε
  have hex := hf ε hε
  let K := Classical.choose hex
  have hdata := Classical.choose_spec hex
  have hK : 0 ≤ K := hdata.1
  have hk := hdata.2
  refine ⟨K, hK, ?_⟩
  intro v f hv
  let x : X := ⟨(v, f), hv⟩
  unfold perturbation
  exact hk x

def weakHilbertGraph (x f : SpinWave N) : Prop :=
  ∃ (u : PauliReference.Ref N)
    (hu : PauliGroundState.Domain a.vector a.positive a.negative u),
    spinInclusion u = x ∧ IsOperatorPair a C κ hκ M hbound e F χ hUV B u hu (fun s => f s)

def sumHilbertGraph (x f : SpinWave N) : Prop :=
  ∃ (u : PauliReference.Ref N) (g : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hg : ∀ s, FreeGraph C κ hκ M hbound e (u s) (g s)),
    spinInclusion u = x ∧
    f = WithLp.toLp 2 (source a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp u g hg)

private theorem weak_graph_intro (u : PauliReference.Ref N)
    (hu : PauliGroundState.Domain a.vector a.positive a.negative u)
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hf : IsOperatorPair a C κ hκ M hbound e F χ hUV B u hu f) :
    weakHilbertGraph a C κ hκ M hbound e F χ hUV B (spinInclusion u) (WithLp.toLp 2 f) :=
  ⟨u, hu, rfl, hf⟩

private theorem spin_inner (u : PauliReference.Ref N) (f : SpinWave N) :
    inner ℂ (spinInclusion u) f =
      ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (f s) :=
  PiLp.inner_apply _ _

private theorem weakHilbertGraph_symmetric :
    SymmetricGraphExtension.Symmetric (weakHilbertGraph a C κ hκ M hbound e F χ hUV B) := by
  rintro x f y g ⟨u, hu, hux, huf⟩ ⟨v, hv, hvy, hvg⟩
  subst x
  subst y
  have huf' : form a C κ hκ M hbound e F χ hUV B v u hv hu =
      inner ℂ (spinInclusion v) f := (huf v hv).trans (spin_inner v f).symm
  have hvg' : form a C κ hκ M hbound e F χ hUV B u v hu hv =
      inner ℂ (spinInclusion u) g := (hvg u hu).trans (spin_inner u g).symm
  exact hvg'.symm.trans ((form_hermitian a C κ hκ M hbound e F χ hUV B v u hv hu).symm.trans
    ((congrArg star huf').trans (inner_conj_symm _ _)))

private theorem freeGraph_intro (u : PauliReference.Ref N)
    (g : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hg : ∀ s, FreeGraph C κ hκ M hbound e (u s) (g s)) :
    finiteGraph (S := SpinIndex N) (PhysicalExternalOperator.freeHilbertGraph (fun _ => 0) C κ hκ M hbound e)
      (spinInclusion u) (WithLp.toLp 2 g) :=
  fun s => ⟨u s, rfl, (freeGraph_iff C κ hκ M hbound e (u s) (g s)).mp (hg s)⟩

include S spectral joint hD hp hBp in
private theorem sum_graph_domain (x : SpinWave N) :
    (∃ f, finiteGraph (S := SpinIndex N) (PhysicalExternalOperator.freeHilbertGraph
      (fun _ => 0) C κ hκ M hbound e) x f) ↔
    ∃ f, sumHilbertGraph a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp x f := by
  constructor
  · rintro ⟨f, hf⟩
    choose u hu hfree using hf
    have hg (s : SpinIndex N) : FreeGraph C κ hκ M hbound e (u s) (f s) :=
      (freeGraph_iff C κ hκ M hbound e (u s) (f s)).mpr (hfree s)
    exact ⟨_, u, (fun s => f s), hg, PiLp.ext fun s => hu s, rfl⟩
  · rintro ⟨f, u, g, hg, hux, hfg⟩
    exact ⟨WithLp.toLp 2 g, hux ▸ freeGraph_intro C κ hκ M hbound e u g hg⟩

include S spectral joint hD hp hBp in
private theorem sum_graph_weak
    (friedrichs : StandardFriedrichsDivergence) (KR : StandardKatoRellich)
    (hG : HaslerHerbstGraphNorm C κ hκ M hbound e)
    (hSA : SelfAdjointGraph (PhysicalExternalOperator.freeHilbertGraph
      (fun _ => 0) C κ hκ M hbound e))
    (x f : SpinWave N)
    (h : sumHilbertGraph a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp x f) :
    weakHilbertGraph a C κ hκ M hbound e F χ hUV B x f := by
  rcases h with ⟨u, g, hg, hux, hfg⟩
  let hu : PauliGroundState.Domain a.vector a.positive a.negative u := fun s =>
    (a.operatorMultipliers S spectral joint C κ hκ M hbound e (u s)
      (comparison C κ hκ M hbound e hD u g hg s)).domain
  refine ⟨u, hu, hux, ?_⟩
  rw [hfg]
  exact source_pair a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp
    friedrichs KR hG hSA u g hg hu

attribute [local irreducible] weakHilbertGraph sumHilbertGraph

include S spectral joint hD hp hBp in
/-- Ordinary Kato--Rellich identifies the global weak spin graph with the
actual algebraic source on the componentwise free operator domain. -/
theorem graph_eq_sum
    (friedrichs : StandardFriedrichsDivergence) (KR : StandardKatoRellich)
    (hG : HaslerHerbstGraphNorm C κ hκ M hbound e)
    (hSA : SelfAdjointGraph (PhysicalExternalOperator.freeHilbertGraph
      (fun _ => 0) C κ hκ M hbound e)) :
    ∀ x f, weakHilbertGraph a C κ hκ M hbound e F χ hUV B x f ↔
      sumHilbertGraph a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp x f := by
  have hex := perturbation_free_relative
    a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp hG (1 / 2) (by norm_num)
  let K := Classical.choose hex
  have hdata := Classical.choose_spec hex
  have hK : 0 ≤ K := hdata.1
  have hrel := hdata.2
  apply KatoRellichBackground.weak_graph_eq (H := SpinWave N) KR
    (finiteGraph (S := SpinIndex N) (PhysicalExternalOperator.freeHilbertGraph (fun _ => 0) C κ hκ M hbound e))
    (sumHilbertGraph a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp)
    (weakHilbertGraph a C κ hκ M hbound e F χ hUV B)
    (finite_selfAdjoint (S := SpinIndex N) _ hSA) (weakHilbertGraph_symmetric a C κ hκ M hbound e F χ hUV B)
    (sum_graph_weak a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp
      friedrichs KR hG hSA)
    (sum_graph_domain a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp)
    (1 / 2) K (by norm_num) (by norm_num) hK
  intro x v w hv hw
  unfold sumHilbertGraph at hw
  rcases hw with ⟨u, g, hg, hux, hw⟩
  have hgv : WithLp.toLp 2 g = v := (finite_selfAdjoint (S := SpinIndex N) _ hSA).single_valued
    (hux ▸ freeGraph_intro C κ hκ M hbound e u g hg) hv
  have he : w - v = WithLp.toLp 2
      (perturbation a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp u g hg) := by
    rw [hw, ← hgv]
    apply PiLp.ext
    intro s
    unfold source
    exact add_sub_cancel_left _ _
  have hb : ‖WithLp.toLp 2
      (perturbation a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp u g hg)‖ ≤
      (1 / 2 : ℝ) * ‖WithLp.toLp 2 g‖ + K * ‖spinInclusion u‖ :=
    (toLp_norm _).trans_le ((hrel u g hg).trans_eq
      (congrArg₂ (fun r m : ℝ => (1 / 2 : ℝ) * r + K * m)
        (toLp_norm g).symm (spinInclusion_norm u).symm))
  exact (congrArg (fun z : SpinWave N => ‖z‖) he).trans_le
    (hb.trans_eq (congrArg₂ (fun r m : ℝ => (1 / 2 : ℝ) * r + K * m)
      (congrArg (fun z : SpinWave N => ‖z‖) hgv)
      (congrArg (fun z : SpinWave N => ‖z‖) hux)))

include S spectral joint hD hp hBp in
theorem operatorPair_iff_free_total
    (friedrichs : StandardFriedrichsDivergence) (KR : StandardKatoRellich)
    (hG : HaslerHerbstGraphNorm C κ hκ M hbound e)
    (hSA : SelfAdjointGraph (PhysicalExternalOperator.freeHilbertGraph
      (fun _ => 0) C κ hκ M hbound e))
    (u : PauliReference.Ref N)
    (hu : PauliGroundState.Domain a.vector a.positive a.negative u)
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3)) :
    IsOperatorPair a C κ hκ M hbound e F χ hUV B u hu f ↔
    ∃ (g : SpinIndex N → WaveSpace (Fin N × Fin 3))
      (hg : ∀ s, FreeGraph C κ hκ M hbound e (u s) (g s)),
      f = source a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp u g hg := by
  constructor
  · intro hf
    have hh := (graph_eq_sum a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp
      friedrichs KR hG hSA (spinInclusion u) (WithLp.toLp 2 f)).mp
      (weak_graph_intro a C κ hκ M hbound e F χ hUV B u hu f hf)
    unfold sumHilbertGraph at hh
    rcases hh with ⟨v, g, hg, hvu, hfg⟩
    have hv : v = u := spinInclusion_injective hvu
    subst v
    exact ⟨g, hg, congrArg WithLp.ofLp hfg⟩
  · rintro ⟨g, hg, rfl⟩
    exact source_pair a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp
      friedrichs KR hG hSA u g hg hu

include S spectral joint hD hp hBp in
theorem operatorPair_comparison_domain
    (friedrichs : StandardFriedrichsDivergence) (KR : StandardKatoRellich)
    (hG : HaslerHerbstGraphNorm C κ hκ M hbound e)
    (hSA : SelfAdjointGraph (PhysicalExternalOperator.freeHilbertGraph
      (fun _ => 0) C κ hκ M hbound e))
    (u : PauliReference.Ref N)
    (hu : PauliGroundState.Domain a.vector a.positive a.negative u)
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hf : IsOperatorPair a C κ hκ M hbound e F χ hUV B u hu f) :
    ∀ s, ComparisonDomain (fun _ => 0) (u s) := by
  obtain ⟨g, hg, he⟩ := (operatorPair_iff_free_total a C κ hκ M hbound e F χ hUV B
    S spectral joint hD hp hBp friedrichs KR hG hSA u hu f).mp hf
  exact comparison C κ hκ M hbound e hD u g hg


include S spectral joint hD hp hBp in
/-- The global spin operator has exactly the finite-spin comparison domain. -/
theorem operator_domain_iff_comparison
    (friedrichs : StandardFriedrichsDivergence) (KR : StandardKatoRellich)
    (hG : HaslerHerbstGraphNorm C κ hκ M hbound e)
    (hSA : SelfAdjointGraph (PhysicalExternalOperator.freeHilbertGraph
      (fun _ => 0) C κ hκ M hbound e))
    (u : PauliReference.Ref N)
    (hu : PauliGroundState.Domain a.vector a.positive a.negative u) :
    (∃ f : SpinIndex N → WaveSpace (Fin N × Fin 3),
      IsOperatorPair a C κ hκ M hbound e F χ hUV B u hu f) ↔
      ∀ s, ComparisonDomain (fun _ => 0) (u s) := by
  constructor
  · rintro ⟨f, hf⟩
    exact operatorPair_comparison_domain a C κ hκ M hbound e F χ hUV B
      S spectral joint hD hp hBp friedrichs KR hG hSA u hu f hf
  · intro hucomp
    have hfree (s : SpinIndex N) : ∃ g, FreeGraph C κ hκ M hbound e (u s) g :=
      (hD (u s)).mpr (hucomp s)
    choose g hg using hfree
    exact ⟨source a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp u g hg,
      source_pair a C κ hκ M hbound e F χ hUV B S spectral joint hD hp hBp
        friedrichs KR hG hSA u g hg hu⟩

end PfHk.PauliMagneticOperatorRealization

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
