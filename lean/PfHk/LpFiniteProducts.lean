import Mathlib.MeasureTheory.Function.L2Space

/-! Finite linear combinations of actual scalar multiplication outputs. -/

noncomputable section
namespace PfHk.LpFiniteProducts

open MeasureTheory

variable {X H J : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [NormedSpace ℝ H] [Fintype J]

theorem sum (b : J → X → ℝ) (u : Lp H 2 μ)
    (hb : ∀ j, MemLp (fun x => b j x • u x) 2 μ)
    (hs : MemLp (fun x => (∑ j, b j x) • u x) 2 μ) :
    hs.toLp _ = ∑ j, (hb j).toLp _ := by
  apply Lp.ext
  have hall : ∀ᵐ x ∂μ, ∀ j, (hb j).toLp _ x = b j x • u x :=
    ae_all_iff.mpr fun j => (hb j).coeFn_toLp
  filter_upwards [hs.coeFn_toLp,
    Lp.coeFn_fun_finsetSum Finset.univ (fun j => (hb j).toLp _), hall] with x hx hs hj
  rw [hx, hs]
  simp only [hj, ← Finset.sum_smul]

theorem add (b c : X → ℝ) (u : Lp H 2 μ)
    (hb : MemLp (fun x => b x • u x) 2 μ)
    (hc : MemLp (fun x => c x • u x) 2 μ)
    (hs : MemLp (fun x => (b x + c x) • u x) 2 μ) :
    hs.toLp _ = hb.toLp _ + hc.toLp _ := by
  apply Lp.ext
  filter_upwards [hs.coeFn_toLp, hb.coeFn_toLp, hc.coeFn_toLp,
    Lp.coeFn_add (hb.toLp _) (hc.toLp _)] with x hs hb hc ha
  rw [hs, ha]
  simp only [Pi.add_apply, hb, hc, add_smul]

end PfHk.LpFiniteProducts
