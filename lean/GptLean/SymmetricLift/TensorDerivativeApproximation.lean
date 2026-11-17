import GptLean.SymmetricLift.TensorApproximation
import GptLean.SymmetricLift.LocalL2Pullback

/-! Strong local L2 convergence of the tensor insertion fields that represent
coordinate derivatives. One-particle approximation assumptions are explicit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace GptLean.SymmetricLift

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Topology BigOperators

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [SeparableSpace V]
  {B : TensorBackground V} {N : ℕ}

def configurationTensorInsertion (B : TensorBackground V) (i : Fin N)
    (t g : EuclideanSpace ℝ (Fin 3) → V) (x : Configuration N) : B.H N :=
  B.pure N (Function.update (fun j => t (particle x j)) i (g (particle x i)))

omit [InnerProductSpace ℂ V] [SeparableSpace V] in
theorem aestronglyMeasurable_comp_particle {t : EuclideanSpace ℝ (Fin 3) → V}
    (ht : AEStronglyMeasurable t volume) (i : Fin N) :
    AEStronglyMeasurable (fun x : Configuration N => t (particle x i)) volume := by
  have h := ht.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_surjective_linearMap (μ := volume)
      (particleLinear i) (particleLinear_surjective i))
  simpa only [Function.comp_def, particleLinear] using! h

namespace TensorMultilinearData

variable (M : TensorMultilinearData B)
include M

theorem aestronglyMeasurable_configurationTensor
    {t : EuclideanSpace ℝ (Fin 3) → V} (ht : AEStronglyMeasurable t volume) :
    AEStronglyMeasurable (configurationTensor B t (N := N)) volume := by
  let : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  apply (M.pure_continuous N).comp_aestronglyMeasurable
  exact (aemeasurable_pi_lambda _ fun i =>
    (aestronglyMeasurable_comp_particle ht i).aemeasurable).aestronglyMeasurable

theorem pure_update_norm_le (u : Fin N → V) (hu : ∀ j, ‖u j‖ ≤ 1)
    (i : Fin N) (v : V) : ‖B.pure N (Function.update u i v)‖ ≤ ‖v‖ := by
  classical
  rw [M.pure_norm]
  have he : (fun j => ‖Function.update u i v j‖) =
      Function.update (fun j => ‖u j‖) i ‖v‖ := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ i)]
  exact mul_le_of_le_one_right (norm_nonneg v)
    (Finset.prod_le_one (fun j _ => norm_nonneg (u j)) (fun j _ => hu j))

theorem configurationTensorInsertion_norm_le (i : Fin N)
    (t g : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ ≤ 1)
    (x : Configuration N) :
    ‖configurationTensorInsertion B i t g x‖ ≤ ‖g (particle x i)‖ :=
  M.pure_update_norm_le _ (fun _ => ht _) i _

theorem configurationTensorInsertion_sub (i : Fin N)
    (t g h : EuclideanSpace ℝ (Fin 3) → V) (x : Configuration N) :
    configurationTensorInsertion B i t g x - configurationTensorInsertion B i t h x =
      configurationTensorInsertion B i t (g - h) x := by
  classical
  simpa only [configurationTensorInsertion, ← M.pure_eq, Pi.sub_apply] using
    ((M.pureMap N).map_update_sub
      (fun j => t (particle x j)) i (g (particle x i)) (h (particle x i))).symm

theorem aestronglyMeasurable_configurationTensorInsertion (i : Fin N)
    {t g : EuclideanSpace ℝ (Fin 3) → V}
    (ht : AEStronglyMeasurable t volume) (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (configurationTensorInsertion B i t g) volume := by
  classical
  let : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  apply (M.pure_continuous N).comp_aestronglyMeasurable
  apply AEMeasurable.aestronglyMeasurable
  apply aemeasurable_pi_lambda
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self] using (aestronglyMeasurable_comp_particle hg i).aemeasurable
  · simpa only [Function.update_of_ne hj] using
      (aestronglyMeasurable_comp_particle ht j).aemeasurable

theorem ae_configurationTensorInsertion_tendsto (i : Fin N)
    {t : ℕ → EuclideanSpace ℝ (Fin 3) → V} {t₀ g : EuclideanSpace ℝ (Fin 3) → V}
    (ht : ∀ᵐ y ∂volume, Tendsto (fun k => t k y) atTop (𝓝 (t₀ y))) :
    ∀ᵐ x ∂volume, Tendsto (fun k => configurationTensorInsertion B i (t k) g x)
      atTop (𝓝 (configurationTensorInsertion B i t₀ g x)) := by
  classical
  filter_upwards [ae_all_particles (N := N) ht] with x hx
  apply ((M.pure_continuous N).tendsto _).comp
  apply tendsto_pi_nhds.2
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self] using tendsto_const_nhds (x := g (particle x i))
  · simpa only [Function.update_of_ne hj] using hx j

theorem memLp_configurationTensorInsertion (i : Fin N)
    {t g : EuclideanSpace ℝ (Fin 3) → V}
    (htm : AEStronglyMeasurable t volume) (hgm : AEStronglyMeasurable g volume)
    (ht : ∀ y, ‖t y‖ ≤ 1)
    (hg : ∀ C : Set (EuclideanSpace ℝ (Fin 3)), IsCompact C → MemLp g 2 (volume.restrict C))
    {K : Set (Configuration N)} (hK : IsCompact K) :
    MemLp (configurationTensorInsertion B i t g) 2 (volume.restrict K) := by
  have hp := memLp_two_comp_surjective_linearMap_on_compact (μ := volume)
    (particleLinear i) (particleLinear_surjective i) hgm hg hK
  have hp' : MemLp (fun x : Configuration N => g (particle x i)) 2 (volume.restrict K) := by
    simpa only [Function.comp_def, particleLinear] using! hp
  exact hp'.mono (M.aestronglyMeasurable_configurationTensorInsertion i htm hgm).restrict
    (Eventually.of_forall fun x => M.configurationTensorInsertion_norm_le i t g ht x)

/-- Varying the bounded factors with a fixed inserted derivative is covered
by dominated convergence and local L2 membership of that derivative. -/
theorem tendsto_eLpNorm_configurationTensorInsertion_fixed (i : Fin N)
    {t : ℕ → EuclideanSpace ℝ (Fin 3) → V} {t₀ g : EuclideanSpace ℝ (Fin 3) → V}
    (htm : ∀ k, AEStronglyMeasurable (t k) volume)
    (ht₀m : AEStronglyMeasurable t₀ volume) (hgm : AEStronglyMeasurable g volume)
    (ht : ∀ k y, ‖t k y‖ ≤ 1) (ht₀ : ∀ y, ‖t₀ y‖ ≤ 1)
    (hg : ∀ C : Set (EuclideanSpace ℝ (Fin 3)), IsCompact C → MemLp g 2 (volume.restrict C))
    (hlim : ∀ᵐ y ∂volume, Tendsto (fun k => t k y) atTop (𝓝 (t₀ y)))
    {K : Set (Configuration N)} (hK : IsCompact K) :
    Tendsto (fun k => eLpNorm (configurationTensorInsertion B i (t k) g -
      configurationTensorInsertion B i t₀ g) 2 (volume.restrict K)) atTop (𝓝 0) := by
  have hp := memLp_two_comp_surjective_linearMap_on_compact (μ := volume)
    (particleLinear i) (particleLinear_surjective i) hgm hg hK
  have hp' : MemLp (fun x : Configuration N => g (particle x i)) 2 (volume.restrict K) := by
    simpa only [Function.comp_def, particleLinear] using! hp
  apply tendsto_eLpNorm_two_of_dominated_sq
    (fun k => (M.aestronglyMeasurable_configurationTensorInsertion i (htm k) hgm).restrict)
    (M.aestronglyMeasurable_configurationTensorInsertion i ht₀m hgm).restrict
    (hp'.integrable_norm_pow (by norm_num))
  · intro k
    exact Eventually.of_forall fun x => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
      (M.configurationTensorInsertion_norm_le i (t k) g (ht k) x)
  · exact Eventually.of_forall fun x => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
      (M.configurationTensorInsertion_norm_le i t₀ g ht₀ x)
  · exact ae_restrict_of_ae (M.ae_configurationTensorInsertion_tendsto i hlim)

/-- Local L2 convergence of one-particle derivatives implies local L2
convergence of the actual tensor insertion fields. -/
theorem tendsto_eLpNorm_configurationTensorInsertion (i : Fin N)
    {t g : ℕ → EuclideanSpace ℝ (Fin 3) → V} {t₀ g₀ : EuclideanSpace ℝ (Fin 3) → V}
    (htm : ∀ k, AEStronglyMeasurable (t k) volume)
    (ht₀m : AEStronglyMeasurable t₀ volume)
    (hgm : ∀ k, AEStronglyMeasurable (g k) volume)
    (hg₀m : AEStronglyMeasurable g₀ volume)
    (ht : ∀ k y, ‖t k y‖ ≤ 1) (ht₀ : ∀ y, ‖t₀ y‖ ≤ 1)
    (hg₀ : ∀ C : Set (EuclideanSpace ℝ (Fin 3)), IsCompact C → MemLp g₀ 2 (volume.restrict C))
    (hlim : ∀ᵐ y ∂volume, Tendsto (fun k => t k y) atTop (𝓝 (t₀ y)))
    (hgconv : ∀ C : Set (EuclideanSpace ℝ (Fin 3)), IsCompact C →
      Tendsto (fun k => eLpNorm (g k - g₀) 2 (volume.restrict C)) atTop (𝓝 0))
    {K : Set (Configuration N)} (hK : IsCompact K) :
    Tendsto (fun k => eLpNorm (configurationTensorInsertion B i (t k) (g k) -
      configurationTensorInsertion B i t₀ g₀) 2 (volume.restrict K)) atTop (𝓝 0) := by
  let a k := configurationTensorInsertion B i (t k) (g k) -
    configurationTensorInsertion B i (t k) g₀
  let b k := configurationTensorInsertion B i (t k) g₀ -
    configurationTensorInsertion B i t₀ g₀
  have hcomp := tendsto_eLpNorm_two_comp_surjective_linearMap (μ := volume)
    (particleLinear i) (particleLinear_surjective i)
    (fun k => (hgm k).sub hg₀m) hgconv hK
  have hcomp' : Tendsto
      (fun k => eLpNorm (fun x : Configuration N => (g k - g₀) (particle x i))
        2 (volume.restrict K)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, particleLinear] using! hcomp
  have ha : Tendsto (fun k => eLpNorm (a k) 2 (volume.restrict K)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcomp'
      (fun _ => zero_le)
    intro k
    apply eLpNorm_mono_ae
    exact Eventually.of_forall fun x => by
      change ‖configurationTensorInsertion B i (t k) (g k) x -
        configurationTensorInsertion B i (t k) g₀ x‖ ≤ _
      rw [M.configurationTensorInsertion_sub]
      exact M.configurationTensorInsertion_norm_le i (t k) (g k - g₀) (ht k) x
  have hb : Tendsto (fun k => eLpNorm (b k) 2 (volume.restrict K)) atTop (𝓝 0) :=
    M.tendsto_eLpNorm_configurationTensorInsertion_fixed i htm ht₀m hg₀m ht ht₀ hg₀ hlim hK
  have hab := ha.add hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using hab) (fun _ => zero_le)
  intro k
  have he : configurationTensorInsertion B i (t k) (g k) -
      configurationTensorInsertion B i t₀ g₀ = a k + b k := by
    dsimp [a, b]
    abel
  dsimp only
  rw [he]
  apply eLpNorm_add_le
  · exact ((M.aestronglyMeasurable_configurationTensorInsertion i (htm k) (hgm k)).sub
      (M.aestronglyMeasurable_configurationTensorInsertion i (htm k) hg₀m)).restrict
  · exact ((M.aestronglyMeasurable_configurationTensorInsertion i (htm k) hg₀m).sub
      (M.aestronglyMeasurable_configurationTensorInsertion i ht₀m hg₀m)).restrict
  · norm_num

end TensorMultilinearData
end GptLean.SymmetricLift
