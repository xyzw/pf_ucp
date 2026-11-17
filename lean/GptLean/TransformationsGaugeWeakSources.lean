import GptLean.TransformationsGaugeWeak
import GptLean.PhysicalSourcePair

/-!
L3 + Linfinity gauge gradients multiply every electronic H1 source into L2.
The proof uses the proved L6 estimate for the selected-particle marginal and
transfers the weighted norm back to the actual configuration-space source.
-/

noncomputable section

namespace GptLean.TransformationsGauge

open MeasureTheory Filter Repair PhysicalSourceFubini PhysicalSourceCoordinates PhysicalSourceMarginal
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

section Product

variable {X Y H : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] [IsSeparable ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H]

/-- A scalar depending on the first variable is square integrable against a
product-space wave function exactly when it is so against its marginal. -/
theorem memLp_smul_of_curry (u : Lp H 2 (μ.prod ν)) {a : X → ℝ}
    (ha : AEStronglyMeasurable a μ)
    (hw : MemLp (fun x => a x • curry u x) 2 μ) :
    MemLp (fun z : X × Y => a z.1 • u z) 2 (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun z : X × Y => a z.1 • u z) (μ.prod ν) :=
    ha.comp_fst.smul (Lp.aestronglyMeasurable u)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (integrable_prod_iff (hm.norm.pow 2)).mpr
  refine ⟨?_, ?_⟩
  · filter_upwards [section_memLp_ae u] with x hx
    exact (hx.const_smul (a x)).integrable_norm_pow (by norm_num)
  · have hi := hw.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    refine hi.congr ?_
    filter_upwards [curry_norm_sq_ae u] with x hx
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [hx, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      change a x ^ 2 * ‖u (x, y)‖ ^ 2 = |(|a x| * ‖u (x, y)‖) ^ 2|
      rw [abs_of_nonneg (sq_nonneg _), mul_pow, sq_abs]

end Product

theorem InLpThreeAddTop.smul_memLp_two {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : InLpThreeAddTop f) {u : EuclideanSpace ℝ (Fin 3) → H}
    (hu₂ : MemLp u 2 volume) (hu₆ : MemLp u 6 volume) :
    MemLp (fun x => f x • u x) 2 volume := by
  obtain ⟨a, b, ha, hb, he⟩ := hf
  let : ENNReal.HolderTriple 3 6 2 :=
    ENNReal.HolderTriple.of_toReal ⟨by norm_num, by norm_num, by norm_num⟩
  have ha' : MemLp (fun x => a x • u x) 2 volume := hu₆.smul ha
  have hb' : MemLp (fun x => b x • u x) 2 volume := hu₂.smul hb
  refine (ha'.add hb').ae_eq ?_
  filter_upwards [he] with x hx
  simp only [Pi.add_apply, hx, add_smul]

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- The L3 + Linfinity condition is sufficient for the actual, possibly
singular, many-electron H1 source. -/
theorem particle_gradient_smul_memLp (i : Fin N)
    (u : ElectronicH1Space.H1 H (Fin N × Fin 3))
    {g : PhysicalSourceCoordinates.Position → ℝ} (hg : InLpThreeAddTop g) :
    MemLp (fun x => g ((split i x).1) • ElectronicH1Space.value u x) 2 volume := by
  have hgm : AEStronglyMeasurable g volume :=
    (finite_localMemLp_two_locallyIntegrable hg.local_memLp_two).aestronglyMeasurable
  have hsource := hg.smul_memLp_two (Lp.memLp (particleMap i (ElectronicH1Space.value u)))
    (particleSource_memLp_six i u)
  have hp := memLp_smul_of_curry
    (productMap (split i) (split_symm_measurePreserving i) (ElectronicH1Space.value u))
    hgm hsource
  have hpull := hp.comp_measurePreserving (split_measurePreserving i)
  apply hpull.ae_eq
  have hrep := (split_measurePreserving i).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving (ElectronicH1Space.value u) (split_symm_measurePreserving i))
  filter_upwards [hrep] with x hx
  change g ((split i x).1) •
    productMap (split i) (split_symm_measurePreserving i) (ElectronicH1Space.value u) (split i x) = _
  have hx' : productMap (split i) (split_symm_measurePreserving i)
      (ElectronicH1Space.value u) (split i x) = ElectronicH1Space.value u x := by
    change (Lp.compMeasurePreserving (split i).symm (split_symm_measurePreserving i)
      (ElectronicH1Space.value u)) (split i x) = _
    simpa only [Function.comp_apply, (split i).symm_apply_apply] using hx
  exact congrArg (fun v : H => g ((split i x).1) • v) hx' 

end GptLean.TransformationsGauge
