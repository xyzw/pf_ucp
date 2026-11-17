import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Joint representatives of measurable L² families. The construction selects
rapidly converging simple approximations and sums their differences. It
does not assume jointly measurable representatives of the input family.
In particular it applies to the first-chaos image of a measurable family
of one-photon kernels.
-/

noncomputable section

namespace GptLean.Gaussian

open MeasureTheory Filter
open scoped ENNReal Topology

variable {X Q : Type*} [MeasurableSpace X] [MeasurableSpace Q] {μ : Measure Q}

/-- Every strongly measurable family of real L² elements admits one jointly
measurable representative, with equality almost everywhere for every fixed
parameter. The parameter measure need not be specified. -/
theorem exists_jointly_measurable_L2_representative
    (F : X → Lp ℝ 2 μ) (hF : StronglyMeasurable F) :
    ∃ f : X → Q → ℝ, Measurable (Function.uncurry f) ∧
      ∀ x, f x =ᵐ[μ] (F x : Q → ℝ) := by
  classical
  borelize ↥(Lp ℝ 2 μ)
  let ε : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  have hε : ∀ n, 0 < ε n := fun n => pow_pos (by norm_num) n
  have hex : ∀ n x, ∃ m, ‖hF.approx m x - F x‖ < ε n := by
    intro n x
    have h := (hF.tendsto_approx x).sub (tendsto_const_nhds (x := F x))
    have hn : Tendsto (fun m => ‖hF.approx m x - F x‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero] using h.norm
    exact (hn.eventually (gt_mem_nhds (hε n))).exists
  let a : ℕ → X → Lp ℝ 2 μ := fun n x => hF.approx (Nat.find (hex n x)) x
  have hab : ∀ n x, ‖a n x - F x‖ < ε n := fun n x => Nat.find_spec (hex n x)
  have hp : ∀ n m, MeasurableSet {x | ‖hF.approx m x - F x‖ < ε n} := by
    intro n m
    exact measurableSet_lt (((hF.approx m).stronglyMeasurable.sub hF).norm.measurable)
      measurable_const
  have ham : ∀ n, Measurable (fun z : X × Q => a n z.1 z.2) := by
    intro n
    have hm : ∀ m, Measurable (fun z : X × Q => hF.approx m z.1 z.2) := by
      intro m
      exact ((hF.approx m).comp Prod.fst measurable_fst).measurable_bind
        (fun v z => v z.2) (fun v => (Lp.stronglyMeasurable v).measurable.comp measurable_snd)
    exact Measurable.find hm (fun m => (hp n m).preimage measurable_fst)
      (fun z => hex n z.1)
  have halim (x : X) : Tendsto (fun n => a n x) atTop (𝓝 (F x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hab n x).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  let d : ℕ → X → Lp ℝ 2 μ := fun n x => a (n + 1) x - a n x
  have hds (x : X) : Summable (fun n => ‖d n x‖) := by
    have heps : Summable ε := summable_geometric_of_norm_lt_one (by norm_num)
    apply (heps.comp_injective (fun _ _ h => Nat.add_right_cancel h)).add heps |>.of_nonneg_of_le
      (fun n => norm_nonneg (d n x))
    intro n
    calc
      ‖d n x‖ = ‖(a (n + 1) x - F x) - (a n x - F x)‖ := by
        congr 1
        dsimp only [d]
        abel
      _ ≤ ‖a (n + 1) x - F x‖ + ‖a n x - F x‖ := norm_sub_le _ _
      _ ≤ ε (n + 1) + ε n := add_le_add (hab _ _).le (hab _ _).le
  have hsum (x : X) : (∑' n, d n x) = F x - a 0 x := by
    apply HasSum.tsum_eq
    apply (hasSum_iff_tendsto_nat_of_summable_norm (hds x)).mpr
    have hs : (fun n => ∑ i ∈ Finset.range n, d i x) =
        (fun n => a n x - a 0 x) :=
      funext (fun n => Finset.sum_range_sub (fun m => a m x) n)
    rw [hs]
    exact (halim x).sub_const (a 0 x)
  let f : X → Q → ℝ := fun x q => a 0 x q + ∑' n, (a (n + 1) x q - a n x q)
  refine ⟨f, (ham 0).add (Measurable.tsum (fun n => (ham (n + 1)).sub (ham n))), ?_⟩
  intro x
  have hnorm : (∑' n, ‖d n x‖ₑ) ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr (hds x)
  have hcoe := Lp.coeFn_tsum hnorm
  have hsub : ∀ᵐ q ∂μ, ∀ n, d n x q = a (n + 1) x q - a n x q :=
    ae_all_iff.mpr (fun n => Lp.coeFn_sub _ _)
  have hlast := Lp.coeFn_sub (F x) (a 0 x)
  filter_upwards [hcoe, hsub, hlast] with q hq hd hl
  rw [hsum x] at hq
  dsimp only [f]
  rw [← tsum_congr (fun n => hd n), ← hq, hl]
  simp only [Pi.sub_apply]
  ring

end GptLean.Gaussian
