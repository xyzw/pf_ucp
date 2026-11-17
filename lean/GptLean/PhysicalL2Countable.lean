import GptLean.PhysicalL2HilbertSum
import GptLean.Repair.CountableFrame
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
A countable spatial coefficient isometry is chosen from an actual scalar L²
Hilbert basis. Separability proves the basis index countable. Padding handles
finite bases as well, so this construction needs no infinite-dimensional
basis assumption and no restriction on the electronic particle count.
-/

noncomputable section
namespace GptLean.PhysicalL2HilbertSum

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

section Countability
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [TopologicalSpace.SeparableSpace E]

theorem basisIndex_countable (b : HilbertBasis ι ℂ E) : Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (b i) (1 / 2 : ℝ))
      (Metric.ball (b j) (1 / 2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have he : dist (b i) (b j) ^ 2 = 2 := by
      rw [dist_eq_norm, norm_sub_sq (𝕜 := ℂ)]
      simp only [b.orthonormal.norm_eq_one, b.orthonormal.2 hij, map_zero]
      norm_num
    have hnon : 0 ≤ dist (b i) (b j) := dist_nonneg
    nlinarith
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨b i, Metric.mem_ball_self (by norm_num)⟩)
end Countability

section Padding
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (e : ι ↪ ℕ)

def singleIsometry (n : ℕ) : H →ₗᵢ[ℂ] lp (fun _ : ℕ => H) 2 where
  toLinearMap := (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 n).toLinearMap
  norm_map' v := lp.norm_single (E := fun _ : ℕ => H) (p := 2) (by norm_num) n v

omit [CompleteSpace H] in
@[simp] theorem singleIsometry_apply (n : ℕ) (v : H) : singleIsometry n v = lp.single 2 n v := rfl

omit [CompleteSpace H] in
theorem padding_orthogonal : OrthogonalFamily ℂ (fun _ : ι => H) (fun i => singleIsometry (e i)) := by
  intro i j hij v w
  simp only [singleIsometry_apply, lp.inner_single_left]
  have hji : e j ≠ e i := fun h => hij (e.injective h.symm)
  simp [lp.single_apply, hji]

def padding : lp (fun _ : ι => H) 2 →ₗᵢ[ℂ] lp (fun _ : ℕ => H) 2 :=
  (padding_orthogonal (H := H) e).linearIsometry

theorem padding_at (u : lp (fun _ : ι => H) 2) (i : ι) : padding e u (e i) = u i := by
  classical
  have hs := (lp.evalCLM ℂ (fun _ : ℕ => H) 2 (e i)).hasSum
    ((padding_orthogonal (H := H) e).hasSum_linearIsometry u)
  change HasSum (fun j => lp.single (E := fun _ : ℕ => H) 2 (e j) (u j) (e i))
    (padding e u (e i)) at hs
  have he (j : ι) : lp.single (E := fun _ : ℕ => H) 2 (e j) (u j) (e i) =
      if j = i then u i else 0 := by
    by_cases hji : j = i
    · subst j; simp
    · have hj : e j ≠ e i := fun h => hji (e.injective h)
      simp [lp.single_apply, hji, hj]
  simp only [he] at hs
  exact hs.unique (hasSum_ite_eq i (u i))

theorem padding_off (u : lp (fun _ : ι => H) 2) (n : ℕ) (hn : n ∉ Set.range e) :
    padding e u n = 0 := by
  have hs := (lp.evalCLM ℂ (fun _ : ℕ => H) 2 n).hasSum
    ((padding_orthogonal (H := H) e).hasSum_linearIsometry u)
  change HasSum (fun j => lp.single (E := fun _ : ℕ => H) 2 (e j) (u j) n) (padding e u n) at hs
  have hz (j : ι) : lp.single (E := fun _ : ℕ => H) 2 (e j) (u j) n = 0 := by
    have hj : e j ≠ n := fun h => hn ⟨j, h⟩
    simp [lp.single_apply, hj]
  simp only [hz] at hs
  exact hs.unique hasSum_zero
end Padding

section Spatial
variable {X H ι : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (e : ι ↪ ℕ)

def countableCoefficients : Lp H 2 μ →ₗᵢ[ℂ] lp (fun _ : ℕ => H) 2 :=
  (padding (H := H) e).comp (coefficients b).toLinearIsometry

theorem countableCoefficients_compLpL (B : H →L[ℂ] H) (u : Lp H 2 μ) (n : ℕ) :
    countableCoefficients b e (B.compLpL 2 μ u) n = B (countableCoefficients b e u n) := by
  classical
  by_cases hn : n ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hn
    change padding e (coefficients b (B.compLpL 2 μ u)) (e i) =
      B (padding e (coefficients b u) (e i))
    rw [padding_at, padding_at, coefficients_compLpL]
  · change padding e (coefficients b (B.compLpL 2 μ u)) n = B (padding e (coefficients b u) n)
    rw [padding_off e _ n hn, padding_off e _ n hn, map_zero]

theorem countableCoefficients_observable_hasSum (B : H →L[ℂ] H) (u : Lp H 2 μ) :
    HasSum (fun n => ⟪countableCoefficients b e u n, B (countableCoefficients b e u n)⟫_ℂ)
      ⟪u, B.compLpL 2 μ u⟫_ℂ := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (countableCoefficients b e u)
    (countableCoefficients b e (B.compLpL 2 μ u))
  rw [(countableCoefficients (H := H) b e).inner_map_map u (B.compLpL 2 μ u)] at h
  simpa only [countableCoefficients_compLpL] using h
end Spatial

section Choice
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ]

def spatialIndex : Set (Lp ℂ 2 μ) := (exists_hilbertBasis ℂ (Lp ℂ 2 μ)).choose

def spatialBasis : HilbertBasis (spatialIndex μ) ℂ (Lp ℂ 2 μ) :=
  (exists_hilbertBasis ℂ (Lp ℂ 2 μ)).choose_spec.choose

instance spatialIndex_countable : Countable (spatialIndex μ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  exact basisIndex_countable (spatialBasis μ)

def spatialIndexEmbedding : spatialIndex μ ↪ ℕ := Repair.countableIndexEmbedding _

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def spatialCoefficients : Lp H 2 μ →ₗᵢ[ℂ] lp (fun _ : ℕ => H) 2 :=
  countableCoefficients (spatialBasis μ) (spatialIndexEmbedding μ)

theorem spatialCoefficients_compLpL (B : H →L[ℂ] H) (u : Lp H 2 μ) (n : ℕ) :
    spatialCoefficients μ H (B.compLpL 2 μ u) n = B (spatialCoefficients μ H u n) :=
  countableCoefficients_compLpL _ _ B u n

theorem spatialCoefficients_observable_hasSum (B : H →L[ℂ] H) (u : Lp H 2 μ) :
    HasSum (fun n => ⟪spatialCoefficients μ H u n, B (spatialCoefficients μ H u n)⟫_ℂ)
      ⟪u, B.compLpL 2 μ u⟫_ℂ :=
  countableCoefficients_observable_hasSum _ _ B u
end Choice
end GptLean.PhysicalL2HilbertSum
