import PfHk.CoordinateMultiplication

/-! Lq convergence of ordinary coefficients implies convergence of their
actual L² products on a fixed coordinate Sobolev vector. -/

noncomputable section
namespace PfHk.CoordinateSobolev

open MeasureTheory Filter GptLean.ElectronicH1Space
open GptLean.PhysicalSourceCoordinates
open scoped ENNReal Topology

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem coordinate_product_norm (S : Data H N) {q : ℝ} (hq : 2 < q)
    (n : Fin N) (b : Position → ℝ) (hb : MemLp b (ENNReal.ofReal q) volume)
    (u v w : L2 H (Fin N × Fin 3)) (hv : BesselPair n (3 / q) u v)
    (hw : w =ᵐ[volume] fun x => coordinateCoefficient n b x • u x) :
    ‖w‖ ≤ S.constant q * (eLpNorm b (ENNReal.ofReal q) volume).toReal * ‖v‖ := by
  have hex := coordinate_multiplier S hq n b hb u v hv
  let hm := Classical.choose hex
  have he : w = hm.toLp _ := Lp.ext (hw.trans hm.coeFn_toLp.symm)
  rw [he]
  exact Classical.choose_spec hex

theorem coordinate_product_tendsto_zero (S : Data H N) {q : ℝ} (hq : 2 < q)
    (n : Fin N) (b : ℕ → Position → ℝ)
    (hb : ∀ k, MemLp (b k) (ENNReal.ofReal q) volume)
    (hzero : Tendsto (fun k => (eLpNorm (b k) (ENNReal.ofReal q) volume).toReal)
      atTop (𝓝 0))
    (u v : L2 H (Fin N × Fin 3)) (hv : BesselPair n (3 / q) u v)
    (w : ℕ → L2 H (Fin N × Fin 3))
    (hw : ∀ k, w k =ᵐ[volume] fun x => coordinateCoefficient n (b k) x • u x) :
    Tendsto w atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim : Tendsto
      (fun k => S.constant q * (eLpNorm (b k) (ENNReal.ofReal q) volume).toReal * ‖v‖)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (tendsto_const_nhds.mul hzero).mul tendsto_const_nhds
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k =>
    coordinate_product_norm S hq n (b k) (hb k) u v (w k) hv (hw k)) hlim

end PfHk.CoordinateSobolev
