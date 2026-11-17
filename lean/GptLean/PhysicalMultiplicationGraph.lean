import GptLean.Repair.TraceChannel
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
The maximal scalar multiplication graph on Hilbert-valued L2. Both
coordinates are actual L2 classes. Closedness comes from almost-everywhere
subsequences, and the output norm is the nonnegative potential integral.
-/

noncomputable section

namespace GptLean.PhysicalMultiplicationGraph

open MeasureTheory Filter Topology Repair
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

section Multiplication

variable {X H : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup H] [NormedSpace ℂ H]

def graph (a : X → ℂ) : Submodule ℂ (Lp H 2 μ × Lp H 2 μ) where
  carrier := {uv | ∀ᵐ x ∂μ, uv.2 x = a x • uv.1 x}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero H 2 μ] with x hx
    simp only [Prod.fst_zero, Prod.snd_zero, hx, Pi.zero_apply, smul_zero]
  add_mem' := by
    intro u v hu hv
    filter_upwards [hu, hv, Lp.coeFn_add u.1 v.1, Lp.coeFn_add u.2 v.2]
      with x hux hvx hx hy
    change (u.2 + v.2) x = a x • (u.1 + v.1) x
    rw [hx, hy, Pi.add_apply, Pi.add_apply, hux, hvx, smul_add]
  smul_mem' := by
    intro c u hu
    filter_upwards [hu, Lp.coeFn_smul c u.1, Lp.coeFn_smul c u.2] with x hux hx hy
    change (c • u.2) x = a x • (c • u.1) x
    rw [hx, hy, Pi.smul_apply, Pi.smul_apply, hux, smul_comm]

theorem graph_fst_zero (a : X → ℂ) (uv : Lp H 2 μ × Lp H 2 μ)
    (huv : uv ∈ graph μ a) (hzero : uv.1 = 0) : uv.2 = 0 := by
  apply Lp.ext
  filter_upwards [huv, Lp.coeFn_zero H 2 μ] with x hx hz
  rw [hzero, hz, Pi.zero_apply, smul_zero] at hx
  exact hx.trans (by rw [hz, Pi.zero_apply])

theorem graph_closed (a : X → ℂ) : IsClosed (graph μ (H := H) a : Set (Lp H 2 μ × Lp H 2 μ)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro uv z huv hz
  have hfst := (continuous_fst.tendsto z).comp hz
  have hsnd := (continuous_snd.tendsto z).comp hz
  obtain ⟨ns, hns, hfstAE⟩ := (tendstoInMeasure_of_tendsto_Lp hfst).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hsndAE⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hsnd.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [hfstAE, hsndAE, ae_all_iff.mpr huv] with x hfx hgx hgraph
  have hm : Tendsto (fun j => a x • (uv (ns (ms j))).1 x) atTop (𝓝 (a x • z.1 x)) :=
    tendsto_const_nhds.smul (hfx.comp hms.tendsto_atTop)
  exact tendsto_nhds_unique hgx (hm.congr fun j => (hgraph (ns (ms j))).symm)

def multiplier (a : X → ℂ) : Lp H 2 μ →ₗ.[ℂ] Lp H 2 μ := (graph μ a).toLinearPMap

theorem multiplier_graph (a : X → ℂ) : (multiplier μ (H := H) a).graph = graph μ a :=
  Submodule.toLinearPMap_graph_eq _ (graph_fst_zero μ a)

theorem multiplier_graph_iff (a : X → ℂ) (u v : Lp H 2 μ) :
    (u, v) ∈ (multiplier μ a).graph ↔ ∀ᵐ x ∂μ, v x = a x • u x := by
  rw [multiplier_graph]
  rfl

theorem multiplier_closed (a : X → ℂ) : (multiplier μ (H := H) a).IsClosed := by
  change IsClosed ((multiplier μ (H := H) a).graph : Set (Lp H 2 μ × Lp H 2 μ))
  rw [multiplier_graph]
  exact graph_closed μ a

abbrev GraphSpace (a : X → ℂ) := ↥(graph μ (H := H) a)

instance graphCompleteSpace [CompleteSpace H] (a : X → ℂ) : CompleteSpace (GraphSpace μ (H := H) a) :=
  (graph_closed μ a).isComplete.completeSpace_coe

def inclusion (a : X → ℂ) : GraphSpace μ (H := H) a →L[ℂ] Lp H 2 μ :=
  (ContinuousLinearMap.fst ℂ (Lp H 2 μ) (Lp H 2 μ)).comp (graph μ a).subtypeL

def output (a : X → ℂ) : GraphSpace μ (H := H) a →L[ℂ] Lp H 2 μ :=
  (ContinuousLinearMap.snd ℂ (Lp H 2 μ) (Lp H 2 μ)).comp (graph μ a).subtypeL

theorem inclusion_injective (a : X → ℂ) : Function.Injective (inclusion μ (H := H) a) := by
  intro u v huv
  have hz : (u - v).val.1 = 0 := by change inclusion μ a u - inclusion μ a v = 0; exact sub_eq_zero.mpr huv
  have ho := graph_fst_zero μ a (u - v).val (u - v).property hz
  apply Subtype.ext
  apply Prod.ext
  · exact huv
  · exact sub_eq_zero.mp ho

end Multiplication

variable {X H : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sqrt_output_energy (V : X → ℝ) (hV : ∀ x, 0 ≤ V x)
    (u : GraphSpace μ (H := H) (fun x => (Real.sqrt (V x) : ℂ))) :
    ENNReal.ofReal (‖output μ _ u‖ ^ 2) =
      ∫⁻ x, ENNReal.ofReal (V x) * ENNReal.ofReal (‖inclusion μ _ u x‖ ^ 2) ∂μ := by
  have hn := toL2_norm_sq (Lp.memLp (output μ _ u))
  simp only [Lp.toLp_coeFn] at hn
  rw [hn, ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (output μ _ u))).mp (Lp.memLp _))
    (ae_of_all _ fun _ => sq_nonneg _)]
  apply lintegral_congr_ae
  filter_upwards [u.property] with x hx
  change ENNReal.ofReal (‖u.val.2 x‖ ^ 2) =
    ENNReal.ofReal (V x) * ENNReal.ofReal (‖u.val.1 x‖ ^ 2)
  rw [hx]
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hV x), ENNReal.ofReal_mul (hV x)]

end GptLean.PhysicalMultiplicationGraph
