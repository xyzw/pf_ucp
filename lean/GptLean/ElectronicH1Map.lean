import GptLean.ElectronicH1Complex
import GptLean.SymmetricLift.L2Dominated
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
Bounded maps of the value space act on the actual weak H1 graph.
Uniformly bounded strong convergence lifts to both L2 and H1.
-/

noncomputable section

namespace GptLean.ElectronicH1Map

open MeasureTheory Filter Topology ElectronicH1Complex
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

section Lp

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compLpL_tendsto (L : ℕ → E →L[ℂ] E)
    (hbound : ∀ n, ‖L n‖ ≤ 1) (hlim : ∀ x, Tendsto (fun n => L n x) atTop (𝓝 x))
    (u : Lp E 2 μ) :
    Tendsto (fun n => (L n).compLpL 2 μ u) atTop (𝓝 u) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ u).mpr
  apply SymmetricLift.tendsto_eLpNorm_two_of_dominated_sq
    (b := fun x => ‖u x‖ ^ 2)
    (fun n => Lp.aestronglyMeasurable ((L n).compLpL 2 μ u))
    (Lp.aestronglyMeasurable u)
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u))
  · intro n
    filter_upwards [(L n).coeFn_compLpL u] with x hx
    rw [hx]
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa only [one_mul] using (L n).le_of_opNorm_le (hbound n) (u x)
  · exact ae_of_all _ fun _ => le_rfl
  · filter_upwards [ae_all_iff.mpr (fun n => (L n).coeFn_compLpL u)] with x hx
    simpa only [hx] using hlim (u x)

theorem compLpL_comp {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : F →L[ℂ] G) (K : E →L[ℂ] F) (u : Lp E 2 μ) :
    L.compLpL 2 μ (K.compLpL 2 μ u) = (L.comp K).compLpL 2 μ u := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (K.compLpL 2 μ u), K.coeFn_compLpL u,
    (L.comp K).coeFn_compLpL u] with x hL hK hLK
  rw [hL, hK, hLK]
  rfl

end Lp

variable {I E F : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

private theorem map_weak (L : E →L[ℂ] F) (u : ComplexH1 E I) :
    SymmetricLift.HasWeakH1Local
      (fun x => L.compLpL 2 volume (value u) x)
      (fun i x => L.compLpL 2 volume (derivative i u) x) := by
  exact (Repair.weakH1Local_map (L.restrictScalars ℝ) (weak u)).congr
    (L.coeFn_compLpL (value u)).symm
    (fun i => (L.coeFn_compLpL (derivative i u)).symm)

/-- A bounded map commutes with all actual distributional derivatives. -/
def map (L : E →L[ℂ] F) : ComplexH1 E I →L[ℂ] ComplexH1 F I :=
  (((L.compLpL 2 volume).comp value).prod
    (ContinuousLinearMap.pi fun i => (L.compLpL 2 volume).comp (derivative i))).codRestrict
      (complexWeakGraph F I) (map_weak L)

@[simp] theorem value_map (L : E →L[ℂ] F) (u : ComplexH1 E I) :
    value (map L u) = L.compLpL 2 volume (value u) := rfl

@[simp] theorem derivative_map (L : E →L[ℂ] F) (u : ComplexH1 E I) (i : I) :
    derivative i (map L u) = L.compLpL 2 volume (derivative i u) := rfl

theorem map_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G] [CompleteSpace G]
    (L : F →L[ℂ] G) (K : E →L[ℂ] F) (u : ComplexH1 E I) :
    map L (map K u) = map (L.comp K) u := by
  apply value_injective
  exact compLpL_comp L K (value u)

theorem map_tendsto (L : ℕ → E →L[ℂ] E)
    (hbound : ∀ n, ‖L n‖ ≤ 1) (hlim : ∀ x, Tendsto (fun n => L n x) atTop (𝓝 x))
    (u : ComplexH1 E I) :
    Tendsto (fun n => map (L n) u) atTop (𝓝 u) := by
  apply tendsto_subtype_rng.mpr
  exact (compLpL_tendsto L hbound hlim (value u)).prodMk_nhds
    (tendsto_pi_nhds.mpr fun i => compLpL_tendsto L hbound hlim (derivative i u))

/-- The actual weak H1 domain is dense in its L2 value space. -/
theorem value_denseRange : DenseRange (value (E := E) (I := I)) := by
  apply (Lp.dense_hasCompactSupport_contDiff
    (μ := (volume : Measure (EuclideanSpace ℝ I))) (F := E)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mono
  rintro u ⟨f, huf, hs, hf⟩
  refine ⟨(realEquiv (E := E) (I := I)).symm
    (ElectronicH1Space.ofSmoothCompact f hf hs), ?_⟩
  apply Lp.ext
  exact (hf.continuous.memLp_of_hasCompactSupport hs).coeFn_toLp.trans huf.symm

end GptLean.ElectronicH1Map
