import GptLean.SymmetricLift.PairEnergyIntegrability
import GptLean.SymmetricLift.L2Dominated
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! Local L2 convergence under surjective finite-dimensional linear maps.
Compact product bounds keep the unused coordinate measure finite. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace GptLean.SymmetricLift

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal Topology

variable {E F W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup W]
  {μ : Measure E} {ν : Measure F} [IsAddHaarMeasure μ] [IsAddHaarMeasure ν]

omit [FiniteDimensional ℝ F] in
theorem quasiMeasurePreserving_surjective_linearMap (L : E →ₗ[ℝ] F)
    (hL : Function.Surjective L) : QuasiMeasurePreserving L μ ν := by
  refine ⟨L.continuous_of_finiteDimensional.measurable, ?_⟩
  obtain ⟨c, _, hc⟩ := L.exists_map_addHaar_eq_smul_addHaar μ ν hL
  rw [hc]
  exact smul_absolutelyContinuous

omit [FiniteDimensional ℝ E] in
theorem tendsto_eLpNorm_two_comp_linearEquiv (e : E ≃L[ℝ] F)
    {f : ℕ → F → W}
    (hf : ∀ C : Set F, IsCompact C →
      Tendsto (fun n => eLpNorm (f n) 2 (ν.restrict C)) atTop (𝓝 0))
    {K : Set E} (hK : IsCompact K) :
    Tendsto (fun n => eLpNorm (f n ∘ e) 2 (μ.restrict K)) atTop (𝓝 0) := by
  let c : ℝ≥0 := addHaarScalarFactor (μ.map e) ν
  have hc : μ.map e = c • ν := isAddLeftInvariant_eq_smul _ _
  have hmap : (μ.restrict K).map e = (μ.map e).restrict (e '' K) := by
    change (μ.restrict K).map e.toHomeomorph =
      (μ.map e.toHomeomorph).restrict (e '' K)
    rw [e.toHomeomorph.measurableEmbedding.restrict_map]
    change (μ.restrict K).map e = (μ.restrict (e ⁻¹' (e '' K))).map e
    rw [e.injective.preimage_image]
  have heq (n : ℕ) : eLpNorm (f n ∘ e) 2 (μ.restrict K) =
      c ^ ((2 : ℝ≥0∞).toReal⁻¹) • eLpNorm (f n) 2 (ν.restrict (e '' K)) := by
    have he := e.toHomeomorph.measurableEmbedding.eLpNorm_map_measure (g := f n)
      (μ := μ.restrict K) (p := 2)
    change eLpNorm (f n) 2 ((μ.restrict K).map e) =
      eLpNorm (f n ∘ e) 2 (μ.restrict K) at he
    rw [← he, hmap, hc,
      Measure.restrict_smul, eLpNorm_smul_measure_of_ne_top' (by norm_num)]
  simp_rw [heq]
  have ht := ENNReal.Tendsto.const_mul (hf (e '' K) (hK.image e.continuous))
    (a := ((c ^ ((2 : ℝ≥0∞).toReal⁻¹) : ℝ≥0) : ℝ≥0∞)) (Or.inr ENNReal.coe_ne_top)
  simpa only [ENNReal.smul_def, smul_eq_mul, mul_zero] using ht

omit [BorelSpace E] [BorelSpace F] in
theorem tendsto_eLpNorm_two_comp_snd {f : ℕ → F → W}
    (hmeas : ∀ n, AEStronglyMeasurable (f n) ν)
    (hf : ∀ C : Set F, IsCompact C →
      Tendsto (fun n => eLpNorm (f n) 2 (ν.restrict C)) atTop (𝓝 0))
    {K : Set (E × F)} (hK : IsCompact K) :
    Tendsto (fun n => eLpNorm (fun x : E × F => f n x.2) 2 ((μ.prod ν).restrict K))
      atTop (𝓝 0) := by
  let A := Prod.fst '' K
  let C := Prod.snd '' K
  have hA : IsCompact A := hK.image continuous_fst
  have hC : IsCompact C := hK.image continuous_snd
  let c : ℝ≥0∞ := μ A
  have hc : c ≠ ∞ := hA.measure_lt_top.ne
  have hrect (n : ℕ) :
      eLpNorm (fun x : E × F => f n x.2) 2 ((μ.prod ν).restrict (A ×ˢ C)) =
        c ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm (f n) 2 (ν.restrict C) := by
    rw [← Measure.prod_restrict]
    have hm : AEStronglyMeasurable (f n)
        (((μ.restrict A).prod (ν.restrict C)).map Prod.snd) := by
      rw [Measure.map_snd_prod]
      exact (hmeas n).restrict.smul_measure _
    change eLpNorm (f n ∘ Prod.snd) 2 _ = _
    rw [← eLpNorm_map_measure hm measurable_snd.aemeasurable, Measure.map_snd_prod,
      eLpNorm_smul_measure_of_ne_top (by norm_num)]
    simp [c]
  have hbound (n : ℕ) :
      eLpNorm (fun x : E × F => f n x.2) 2 ((μ.prod ν).restrict K) ≤
        c ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm (f n) 2 (ν.restrict C) := by
    rw [← hrect]
    apply eLpNorm_mono_measure
    apply Measure.restrict_mono
    · intro x hx
      exact ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
    · exact le_rfl
  have ht := ENNReal.Tendsto.const_mul (hf C hC)
    (a := c ^ (1 / (2 : ℝ≥0∞)).toReal)
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hc))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ht) (fun _ => zero_le) hbound

/-- Local L2 errors remain small after surjective linear pullback. -/
theorem tendsto_eLpNorm_two_comp_surjective_linearMap (L : E →ₗ[ℝ] F)
    (hL : Function.Surjective L) {f : ℕ → F → W}
    (hmeas : ∀ n, AEStronglyMeasurable (f n) ν)
    (hf : ∀ C : Set F, IsCompact C →
      Tendsto (fun n => eLpNorm (f n) 2 (ν.restrict C)) atTop (𝓝 0))
    {K : Set E} (hK : IsCompact K) :
    Tendsto (fun n => eLpNorm (f n ∘ L) 2 (μ.restrict K)) atTop (𝓝 0) := by
  let S : Submodule ℝ E := LinearMap.ker L
  obtain ⟨T, hT⟩ : ∃ T : Submodule ℝ E, IsCompl S T := Submodule.exists_isCompl S
  let M : (S × T) ≃ₗ[ℝ] E := Submodule.prodEquivOfIsCompl S T hT
  have hbij : Function.Bijective (LinearMap.domRestrict L T) :=
    ⟨LinearMap.injective_domRestrict_iff.2 hT.disjoint.symm,
      (LinearMap.surjective_domRestrict_iff hL).2 hT.symm.codisjoint⟩
  let L' : T ≃ₗ[ℝ] F := LinearEquiv.ofBijective (LinearMap.domRestrict L T) hbij
  have heq : ∀ x, L x = L' (M.symm x).2 := by
    intro x
    obtain ⟨y, z, hyz⟩ : ∃ (y : S) (z : T), M.symm x = (y, z) := ⟨_, _, rfl⟩
    have hx : x = M (y, z) := by
      rw [← hyz]
      simp only [LinearEquiv.apply_symm_apply]
    simp [L', M, hx]
  have hmeas' (n : ℕ) : AEStronglyMeasurable (f n ∘ L') (addHaar : Measure T) :=
    (hmeas n).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_surjective_linearMap L'.toLinearMap L'.surjective)
  have hfirst : ∀ C : Set T, IsCompact C → Tendsto
      (fun n => eLpNorm (f n ∘ L') 2 ((addHaar : Measure T).restrict C)) atTop (𝓝 0) :=
    fun _ hC => tendsto_eLpNorm_two_comp_linearEquiv L'.toContinuousLinearEquiv hf hC
  have hsecond : ∀ C : Set (S × T), IsCompact C → Tendsto
      (fun n => eLpNorm (fun p : S × T => f n (L' p.2)) 2
        (((addHaar : Measure S).prod (addHaar : Measure T)).restrict C)) atTop (𝓝 0) :=
    fun _ hC => tendsto_eLpNorm_two_comp_snd hmeas' hfirst hC
  have hfinal := tendsto_eLpNorm_two_comp_linearEquiv
    (μ := μ) M.toContinuousLinearEquiv.symm hsecond hK
  change Tendsto (fun n => eLpNorm (fun x => f n (L' (M.symm x).2)) 2 (μ.restrict K))
    atTop (𝓝 0) at hfinal
  simpa only [Function.comp_def, ← heq] using hfinal

/-- Local L2 membership also pulls back, using the already proved scalar
local-integrability theorem on the squared norm. -/
theorem memLp_two_comp_surjective_linearMap_on_compact (L : E →ₗ[ℝ] F)
    (hL : Function.Surjective L) {f : F → W} (hmeas : AEStronglyMeasurable f ν)
    (hf : ∀ C : Set F, IsCompact C → MemLp f 2 (ν.restrict C))
    {K : Set E} (hK : IsCompact K) : MemLp (f ∘ L) 2 (μ.restrict K) := by
  have hsq : LocallyIntegrable (fun y => ‖f y‖ ^ 2) ν := by
    rw [locallyIntegrable_iff]
    intro C hC
    exact (hf C hC).integrable_norm_pow (by norm_num)
  have hpull := locallyIntegrable_comp_surjective_linearMap (μ := μ) L hL hsq
  have hm := hmeas.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_surjective_linearMap (μ := μ) L hL)
  exact (memLp_two_iff_integrable_sq_norm hm.restrict).mpr
    (hpull.integrableOn_isCompact hK)

end GptLean.SymmetricLift
