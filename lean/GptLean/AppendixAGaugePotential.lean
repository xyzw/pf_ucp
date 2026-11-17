import GptLean.TransformationsGaugeWeakStates

/-!
Appendix A gauge identities for the full weak gauge class. The Lieb identity
uses the already proved equality of the physical mixed search and Lieb dual.
The external energy calculation permits L3 + Linfinity vector potentials.
-/

noncomputable section

namespace GptLean.TransformationsGauge

open MeasureTheory PhysicalPairSpace
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 800000

namespace InLpThreeAddTop

theorem sub {a b : Position → ℝ} (ha : InLpThreeAddTop a) (hb : InLpThreeAddTop b) :
    InLpThreeAddTop (fun x => a x - b x) := by
  obtain ⟨a₃, aTop, ha₃, haTop, hea⟩ := ha
  obtain ⟨b₃, bTop, hb₃, hbTop, heb⟩ := hb
  refine ⟨a₃ - b₃, aTop - bTop, ha₃.sub hb₃, haTop.sub hbTop, ?_⟩
  filter_upwards [hea, heb] with x hx hy
  simp only [hx, hy, Pi.sub_apply]
  ring

end InLpThreeAddTop

/-- The vector-potential contribution to the ordinary external energy. -/
def vectorEnergy (A : Fin 3 → Position → ℝ) (p : Pair) : ℝ :=
  ∑ a, ∫ x, A a x * currentL1 p x a + (1 / 2 : ℝ) * A a x ^ 2 * densityL1 p x

theorem vectorEnergy_integrable (A : Fin 3 → Position → ℝ)
    (hA : ∀ a, InLpThreeAddTop (A a)) (p : Pair) (a : Fin 3) :
    Integrable (fun x => A a x * currentL1 p x a +
      (1 / 2 : ℝ) * A a x ^ 2 * densityL1 p x) volume := by
  have hc := memLp_one_iff_integrable.mp ((hA a).mul_memLp_one
    ((Lp.memLp (currentL1 p)).eval_piLp a)
    ((SpatialGauge.current_memLp_three_halves p).eval_piLp a))
  have hq := ((hA a).square_mul_integrable (Lp.memLp (densityL1 p))
    (SpatialGauge.density_memLp_three p)).const_mul (1 / 2 : ℝ)
  exact hc.add (hq.congr (ae_of_all _ fun x => by ring))

namespace WeakSpatialGauge

variable (g : WeakSpatialGauge)

theorem energyShift_eq_vectorEnergy (p : Pair) :
    g.energyShift p = vectorEnergy g.gradient p := by
  have hsum : (∫ x, (∑ a, g.gradient a x ^ 2) * densityL1 p x) =
      ∑ a, ∫ x, g.gradient a x ^ 2 * densityL1 p x := by
    simp_rw [Finset.sum_mul]
    exact integral_finsetSum _ (fun a _ => g.gradient_square_density_integrable p a)
  unfold energyShift vectorEnergy
  rw [hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hq : Integrable (fun x => (1 / 2 : ℝ) * g.gradient a x ^ 2 * densityL1 p x) :=
    ((g.gradient_square_density_integrable p a).const_mul (1 / 2 : ℝ)).congr
      (ae_of_all _ fun x => by ring)
  rw [integral_add (g.gradient_current_integrable p a) hq]
  congr 1
  exact (integral_const_mul (1 / 2 : ℝ) _).symm.trans
    (integral_congr_ae (ae_of_all _ fun x => by ring))

/-- The physical current is invariant under simultaneous state and potential gauge action. -/
theorem physical_current_gauge (p : Pair) (A : Fin 3 → Position → ℝ) (a : Fin 3) :
    (fun x => currentL1 (g.shiftPair p) x a +
      densityL1 (g.shiftPair p) x * (A a x - g.gradient a x)) =ᵐ[volume]
      fun x => currentL1 p x a + densityL1 p x * A a x := by
  filter_upwards [g.currentL1_shiftPair p] with x hx
  rw [g.densityL1_shiftPair, hx, PiLp.add_apply, PiLp.smul_apply, gradientVector_apply]
  change currentL1 p x a + densityL1 p x * g.gradient a x +
    densityL1 p x * (A a x - g.gradient a x) = _
  ring

/-- Exact cancellation of the external vector energy and internal gauge shift. -/
theorem vectorEnergy_gauge (A : Fin 3 → Position → ℝ)
    (hA : ∀ a, InLpThreeAddTop (A a)) (p : Pair) :
    g.energyShift p + vectorEnergy (fun a x => A a x - g.gradient a x) (g.shiftPair p) =
      vectorEnergy A p := by
  rw [g.energyShift_eq_vectorEnergy]
  unfold vectorEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← integral_add (vectorEnergy_integrable g.gradient g.gradient_in_sum p a)
    (vectorEnergy_integrable (fun a x => A a x - g.gradient a x)
      (fun a => (hA a).sub (g.gradient_in_sum a)) (g.shiftPair p) a)]
  apply integral_congr_ae
  filter_upwards [g.currentL1_shiftPair p] with x hx
  rw [g.densityL1_shiftPair, hx, PiLp.add_apply, PiLp.smul_apply, gradientVector_apply]
  change g.gradient a x * currentL1 p x a + 1 / 2 * g.gradient a x ^ 2 * densityL1 p x +
    ((A a x - g.gradient a x) * (currentL1 p x a + densityL1 p x * g.gradient a x) +
      1 / 2 * (A a x - g.gradient a x) ^ 2 * densityL1 p x) = _
  ring

end WeakSpatialGauge

end GptLean.TransformationsGauge
