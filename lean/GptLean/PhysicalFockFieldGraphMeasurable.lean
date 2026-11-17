import GptLean.PhysicalFockFieldGraph
import GptLean.PhysicalFockKernelLinearity

/-!
The actual Segal graph is closed jointly in its one-photon kernel and its
two Fock vectors. Its pullback by almost-everywhere strongly measurable
kernel and vector families is therefore null measurable. This supplies
the measurable graph event needed for spatially varying field kernels.
-/

noncomputable section

set_option Elab.async false

namespace GptLean

open MeasureTheory Filter

/-- Fubini for an event measurable modulo the product measure. -/
theorem ae_prod_iff_ae_ae₀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite ν] {p : X × Y → Prop}
    (hp : NullMeasurableSet {z | p z} (μ.prod ν)) :
    (∀ᵐ z ∂μ.prod ν, p z) ↔ ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p (x, y) := by
  constructor
  · exact Measure.ae_ae_of_ae_prod
  · intro h
    have he := hp.toMeasurable_ae_eq
    have hsections := Measure.ae_ae_of_ae_prod he
    have hmeas : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν,
        (x, y) ∈ toMeasurable (μ.prod ν) {z | p z} := by
      filter_upwards [h, hsections] with x hx hex
      filter_upwards [hx, hex] with y hy hey
      exact Eq.mpr hey hy
    have hprod := (Measure.ae_prod_iff_ae_ae
      (measurableSet_toMeasurable (μ.prod ν) {z | p z})).mpr hmeas
    filter_upwards [hprod, he] with z hz hez
    exact Eq.mp hez hz

end GptLean

namespace GptLean.PhysicalFock

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

/-- Kernel dependence of the actual adjacent-sector creation operator. -/
def creationSectorKernelMap (n : ℕ) :
    Lp ℂ 2 μ →L[ℂ] (Sector μ n →L[ℂ] Sector μ (n + 1)) :=
  LinearMap.mkContinuous
    { toFun := creationSector μ n
      map_add' := creationSector_add μ n
      map_smul' c f := creationSector_smul μ n f c }
    (Real.sqrt (n + 1 : ℝ)) (creationSector_opNorm_le μ n)

theorem creationSector_continuous_kernel (n : ℕ) :
    Continuous (creationSector μ n) :=
  (creationSectorKernelMap μ n).continuous

theorem annihilationSector_continuous_kernel (n : ℕ) :
    Continuous (annihilationSector μ n) :=
  ContinuousLinearMap.adjoint.continuous.comp (creationSector_continuous_kernel μ n)

theorem segalCoordinate_joint_continuous (n : ℕ) :
    Continuous (fun p : Lp ℂ 2 μ × Fock μ => segalCoordinate μ p.1 n p.2) := by
  cases n with
  | zero =>
    exact ((annihilationSector_continuous_kernel μ 0).comp continuous_fst).clm_apply
      ((lp.evalCLM ℂ (Sector μ) 2 1).continuous.comp continuous_snd)
  | succ n =>
    exact (((annihilationSector_continuous_kernel μ (n + 1)).comp continuous_fst).clm_apply
      ((lp.evalCLM ℂ (Sector μ) 2 (n + 1 + 1)).continuous.comp continuous_snd)).add
      (((creationSector_continuous_kernel μ n).comp continuous_fst).clm_apply
        ((lp.evalCLM ℂ (Sector μ) 2 n).continuous.comp continuous_snd))

attribute [local irreducible] segalCoordinate

/-- No graph-matching assumption is needed when the kernel also varies. -/
theorem segalGraph_joint_closed :
    IsClosed {p : Lp ℂ 2 μ × (Fock μ × Fock μ) | SegalGraph μ p.1 p.2.1 p.2.2} := by
  change IsClosed {p : Lp ℂ 2 μ × (Fock μ × Fock μ) | ∀ n,
    (lp.evalCLM ℂ (Sector μ) 2 n) p.2.2 = segalCoordinate μ p.1 n p.2.1}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro n
  have hpair : Continuous (fun p : Lp ℂ 2 μ × (Fock μ × Fock μ) => (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hcoord := (segalCoordinate_joint_continuous μ n).comp hpair
  exact isClosed_eq
    ((lp.evalCLM ℂ (Sector μ) 2 n).continuous.comp
      (continuous_snd.comp continuous_snd)) hcoord

theorem segalGraph_joint_limit {f : Lp ℂ 2 μ} {u v : Fock μ}
    {fn : ℕ → Lp ℂ 2 μ} {un vn : ℕ → Fock μ}
    (hf : Tendsto fn atTop (𝓝 f)) (hu : Tendsto un atTop (𝓝 u))
    (hv : Tendsto vn atTop (𝓝 v)) (h : ∀ n, SegalGraph μ (fn n) (un n) (vn n)) :
    SegalGraph μ f u v :=
  (segalGraph_joint_closed μ).mem_of_tendsto
    (hf.prodMk_nhds (hu.prodMk_nhds hv)) (Eventually.of_forall h)

/-- The joint field graph event is measurable modulo the given measure. -/
theorem segalGraph_nullMeasurableSet {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f : X → Lp ℂ 2 μ} {u v : X → Fock μ}
    (hf : AEStronglyMeasurable f ν) (hu : AEStronglyMeasurable u ν)
    (hv : AEStronglyMeasurable v ν) :
    NullMeasurableSet {x | SegalGraph μ (f x) (u x) (v x)} ν := by
  let : MeasurableSpace (Lp ℂ 2 μ × (Fock μ × Fock μ)) := borel _
  have : BorelSpace (Lp ℂ 2 μ × (Fock μ × Fock μ)) := ⟨rfl⟩
  exact (hf.prodMk (hu.prodMk hv)).aemeasurable.nullMeasurable
    (segalGraph_joint_closed μ).measurableSet

end GptLean.PhysicalFock
