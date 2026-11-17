import GptLean.PhysicalFockKernelField

/-!
The ordinary Segal field graph is fixed by the actual adjacent-sector
creation and annihilation operators. It is closed in Fock × Fock, and the
constructed radiation-domain field belongs to this graph. These identities
provide the model-independent operator used in the WIS theorem.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

/-- Each output sector of the ordinary field is a bounded function of the
full Fock vector. The full operator is generally unbounded. -/
def segalCoordinate (f : Lp ℂ 2 μ) : (n : ℕ) → Fock μ →L[ℂ] Sector μ n
  | 0 => (annihilationSector μ 0 f).comp (lp.evalCLM ℂ (Sector μ) 2 1)
  | n + 1 => (annihilationSector μ (n + 1) f).comp
      (lp.evalCLM ℂ (Sector μ) 2 (n + 1 + 1)) +
      (creationSector μ n f).comp (lp.evalCLM ℂ (Sector μ) 2 n)

/-- The maximal field graph uses the concrete sector actions. -/
def SegalGraph (f : Lp ℂ 2 μ) (u v : Fock μ) : Prop :=
  ∀ n, v n = segalCoordinate μ f n u

theorem segalGraph_closed (f : Lp ℂ 2 μ) :
    IsClosed {p : Fock μ × Fock μ | SegalGraph μ f p.1 p.2} := by
  change IsClosed {p : Fock μ × Fock μ | ∀ n,
    (lp.evalCLM ℂ (Sector μ) 2 n) p.2 = segalCoordinate μ f n p.1}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun n => isClosed_eq
    ((lp.evalCLM ℂ (Sector μ) 2 n).continuous.comp continuous_snd)
    ((segalCoordinate μ f n).continuous.comp continuous_fst))

theorem segalGraph_unique (f : Lp ℂ 2 μ) {u v w : Fock μ}
    (hv : SegalGraph μ f u v) (hw : SegalGraph μ f u w) : v = w := by
  apply lp.ext
  funext n
  exact (hv n).trans (hw n).symm

theorem segalGraph_limit (f : Lp ℂ 2 μ) {u v : Fock μ} {un vn : ℕ → Fock μ}
    (hu : Tendsto un atTop (𝓝 u)) (hv : Tendsto vn atTop (𝓝 v))
    (h : ∀ n, SegalGraph μ f (un n) (vn n)) : SegalGraph μ f u v :=
  (segalGraph_closed μ f).mem_of_tendsto (hu.prodMk_nhds hv) (Eventually.of_forall h)

/-- The actual weighted-kernel field has exactly the ordinary sector graph. -/
theorem kernelField_segalGraph (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    SegalGraph photonMeasure k.val.1 (radiationGraphInclusion q) (kernelField C k q) := by
  intro n
  cases n with
  | zero =>
    change annihilationSector photonMeasure 0 k.val.1 (radiationGraphInclusion q 1) + 0 = _
    exact add_zero _
  | succ n => rfl

end GptLean.PhysicalFock
