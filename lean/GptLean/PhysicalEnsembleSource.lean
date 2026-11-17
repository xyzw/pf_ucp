import GptLean.PhysicalSourceFubini
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
The spectral index of a mixed state is an actual counting-measure Hilbert
factor. Square-summable L2 wave functions define a product-space wave
function and hence one Hilbert-valued source. Its density and current
pairings are the pointwise sums of the original ensemble expressions.
-/

noncomputable section

namespace GptLean.PhysicalEnsembleSource

open MeasureTheory Filter Repair
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {X H : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

abbrev Fiber (H : Type*) [NormedAddCommGroup H] :=
  Lp H 2 (Measure.count : Measure ℕ)

def ensembleFunction (v : ℕ → Lp H 2 μ) (z : X × ℕ) : H := v z.2 z.1

omit [SFinite μ] [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H] in
theorem ensembleFunction_stronglyMeasurable (v : ℕ → Lp H 2 μ) :
    StronglyMeasurable (ensembleFunction v) := by
  exact (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun _ => continuous_of_discreteTopology) (fun n => Lp.stronglyMeasurable (v n))).comp_measurable
      measurable_swap

omit [TopologicalSpace.SeparableSpace H] in
theorem ensembleFunction_memLp (v : ℕ → Lp H 2 μ)
    (hv : Summable (fun n => ‖v n‖ ^ 2)) :
    MemLp (ensembleFunction v) 2 (μ.prod Measure.count) := by
  have hc : Integrable (fun n => ‖v n‖ ^ 2) Measure.count :=
    integrable_count_iff.mpr (by simpa only [norm_pow, norm_norm] using hv)
  have heq : (fun n : ℕ => ∫ x, ‖‖ensembleFunction v (x, n)‖ ^ 2‖ ∂μ) =
      (fun n => ‖v n‖ ^ 2) := by
    funext n
    simp only [ensembleFunction, norm_pow, norm_norm]
    simpa only [Lp.toLp_coeFn] using (toL2_norm_sq (Lp.memLp (v n))).symm
  have hsections : ∀ᵐ n ∂(Measure.count : Measure ℕ),
      Integrable (fun x => ‖ensembleFunction v (x, n)‖ ^ 2) μ :=
    ae_of_all _ fun n =>
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (v n))).mp (Lp.memLp (v n))
  have hm : AEStronglyMeasurable (fun z => ‖ensembleFunction v z‖ ^ 2)
      (μ.prod (Measure.count : Measure ℕ)) :=
    ((ensembleFunction_stronglyMeasurable v).norm.pow 2).aestronglyMeasurable
  have hi : Integrable (fun z => ‖ensembleFunction v z‖ ^ 2)
      (μ.prod (Measure.count : Measure ℕ)) :=
    (integrable_prod_iff' hm).mpr ⟨hsections, heq ▸ hc⟩
  exact (memLp_two_iff_integrable_sq_norm
    (ensembleFunction_stronglyMeasurable v).aestronglyMeasurable).mpr hi

def product (v : ℕ → Lp H 2 μ) (hv : Summable (fun n => ‖v n‖ ^ 2)) :
    Lp H 2 (μ.prod (Measure.count : Measure ℕ)) :=
  (ensembleFunction_memLp v hv).toLp (ensembleFunction v)

omit [TopologicalSpace.SeparableSpace H] in
theorem product_ae (v : ℕ → Lp H 2 μ) (hv : Summable (fun n => ‖v n‖ ^ 2)) :
    (product v hv : X × ℕ → H) =ᵐ[μ.prod Measure.count] ensembleFunction v :=
  (ensembleFunction_memLp v hv).coeFn_toLp

omit [TopologicalSpace.SeparableSpace H] in
theorem product_norm_sq (v : ℕ → Lp H 2 μ) (hv : Summable (fun n => ‖v n‖ ^ 2)) :
    ‖product v hv‖ ^ 2 = ∑' n, ‖v n‖ ^ 2 := by
  have hi : Integrable (fun z => ‖ensembleFunction v z‖ ^ 2) (μ.prod Measure.count) :=
    (memLp_two_iff_integrable_sq_norm
      (ensembleFunction_stronglyMeasurable v).aestronglyMeasurable).mp (ensembleFunction_memLp v hv)
  rw [product, toL2_norm_sq, integral_prod_symm _ hi]
  have heq (n : ℕ) : (∫ x, ‖ensembleFunction v (x, n)‖ ^ 2 ∂μ) = ‖v n‖ ^ 2 := by
    simpa only [ensembleFunction, Lp.toLp_coeFn] using (toL2_norm_sq (Lp.memLp (v n))).symm
  simp_rw [heq]
  have hc : Integrable (fun n => ‖v n‖ ^ 2) Measure.count :=
    integrable_count_iff.mpr (by simpa only [norm_pow, norm_norm] using hv)
  rw [integral_countable hc]
  simp only [count_real_singleton, one_smul]

def ensemble (v : ℕ → Lp H 2 μ) (hv : Summable (fun n => ‖v n‖ ^ 2)) :
    Lp (Fiber H) 2 μ := PhysicalSourceFubini.curry (product v hv)

theorem ensemble_norm_sq (v : ℕ → Lp H 2 μ) (hv : Summable (fun n => ‖v n‖ ^ 2)) :
    ‖ensemble v hv‖ ^ 2 = ∑' n, ‖v n‖ ^ 2 := by
  rw [ensemble, PhysicalSourceFubini.norm_curry, product_norm_sq]

theorem ensemble_represents_ae (v : ℕ → Lp H 2 μ)
    (hv : Summable (fun n => ‖v n‖ ^ 2)) :
    ∀ᵐ x ∂μ, ∀ n, ensemble v hv x n = v n x := by
  filter_upwards [PhysicalSourceFubini.curry_ae (product v hv),
    PhysicalSourceFubini.section_represents_ae (product v hv),
    Measure.ae_ae_of_ae_prod (product_ae v hv)] with x hx hs hp
  have hall : ∀ᵐ n ∂(Measure.count : Measure ℕ), ensemble v hv x n = v n x := by
    filter_upwards [hs, hp] with n hn hpn
    rw [ensemble, hx, hn, hpn]
    rfl
  exact Measure.ae_count_iff.mp hall

theorem ensemble_norm_sq_ae (v : ℕ → Lp H 2 μ)
    (hv : Summable (fun n => ‖v n‖ ^ 2)) :
    (fun x => ‖ensemble v hv x‖ ^ 2) =ᵐ[μ] (fun x => ∑' n, ‖v n x‖ ^ 2) := by
  filter_upwards [ensemble_represents_ae v hv] with x hx
  have hi := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (ensemble v hv x))).mp (Lp.memLp (ensemble v hv x))
  have hn := toL2_norm_sq (Lp.memLp (ensemble v hv x))
  simp only [Lp.toLp_coeFn] at hn
  rw [hn, integral_countable hi]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul, hx]

theorem ensemble_inner_ae (v w : ℕ → Lp H 2 μ)
    (hv : Summable (fun n => ‖v n‖ ^ 2)) (hw : Summable (fun n => ‖w n‖ ^ 2)) :
    (fun x => inner ℂ (ensemble v hv x) (ensemble w hw x)) =ᵐ[μ]
      (fun x => ∑' n, inner ℂ (v n x) (w n x)) := by
  filter_upwards [ensemble_represents_ae v hv, ensemble_represents_ae w hw] with x hx hy
  rw [L2.inner_def, integral_countable (L2.integrable_inner (ensemble v hv x) (ensemble w hw x))]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul, hx, hy]

end GptLean.PhysicalEnsembleSource
