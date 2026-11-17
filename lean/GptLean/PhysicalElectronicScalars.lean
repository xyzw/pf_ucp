import GptLean.ElectronicH1DifferentiableMultiplier
import GptLean.PhotonLocalizationElectronicCalculus
import GptLean.SymmetricLift.L2Dominated
import GptLean.SymmetricLift.PermutationMetric

/-!
The actual symmetric electronic partition acts on the Euclidean
configuration space. Every branch is a bounded differentiable H1
multiplier. The selected branch is the existing retained product, and
its operators converge strongly to the identity.
-/

noncomputable section

namespace GptLean.PhysicalElectronicScalars

open MeasureTheory Filter Topology SymmetricLift PhotonLocalization
  PhotonLocalizationKernelCutoffs ElectronicLocalization ElectronicH1Multiplier
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
set_option Elab.async false

variable (N : ℕ)

def weight (l : ℕ) (a : Fin N → Bool) (x : Configuration N) : ℝ :=
  symmetricMultiplier (electronicPair ((l : ℝ) + 1)) a (electronicPositions x)

theorem differentiable (l : ℕ) (a : Fin N → Bool) : Differentiable ℝ (weight N l a) :=
  (symmetricElectronicPartition_differentiable _ a).comp electronicPositions.differentiable

theorem nonneg (l : ℕ) (a : Fin N → Bool) (x : Configuration N) : 0 ≤ weight N l a x :=
  symmetricElectronicPartition_nonneg _ a (electronicPositions x)

theorem square_partition (l : ℕ) (x : Configuration N) :
    HasSum (fun a : Fin N → Bool => weight N l a x ^ 2) 1 :=
  symmetricElectronicPartition_hasSum_sq _ (electronicPositions x)

theorem abs_le_one (l : ℕ) (a : Fin N → Bool) (x : Configuration N) :
    |weight N l a x| ≤ 1 := by
  have hp := (square_partition N l x).tsum_eq
  rw [tsum_fintype] at hp
  have hsq : weight N l a x ^ 2 ≤ 1 := by
    rw [← hp]
    exact Finset.single_le_sum (fun b _ => sq_nonneg (weight N l b x)) (Finset.mem_univ a)
  exact (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp (by simpa only [sq_abs, one_pow] using hsq)

theorem derivative (l : ℕ) (a : Fin N → Bool) (x : Configuration N) (i : Fin N × Fin 3) :
    fderiv ℝ (weight N l a) x (EuclideanSpace.single i 1) =
      fderiv ℝ (symmetricMultiplier (electronicPair ((l : ℝ) + 1)) a)
        (electronicPositions x) (Pi.single i.1 (EuclideanSpace.single i.2 1)) := by
  have h := (symmetricElectronicPartition_differentiable ((l : ℝ) + 1) a
    (electronicPositions x)).hasFDerivAt.comp x electronicPositions.hasFDerivAt
  change fderiv ℝ (symmetricMultiplier (electronicPair ((l : ℝ) + 1)) a ∘ electronicPositions) x _ = _
  rw [h.fderiv, ContinuousLinearMap.comp_apply, electronicPositions_single]

def branch (l : ℕ) (a : Fin N → Bool) : DifferentiableMultiplier (Fin N × Fin 3) where
  weight := weight N l a
  differentiable := differentiable N l a
  bound := 1
  bounded := abs_le_one N l a
  derivativeBound := (symmetricElectronicPartition_admissible N l a).2.choose
  derivative_bounded i x := by
    rw [derivative]
    exact (symmetricElectronicPartition_admissible N l a).2.choose_spec.2.2
      (electronicPositions x) i

@[simp] theorem branch_weight (l : ℕ) (a : Fin N → Bool) (x : Configuration N) :
    (branch N l a).weight x = weight N l a x := rfl

def cost (l : ℕ) : ℝ :=
  3 * N * electronicPartitionConstant / (2 * ((l : ℝ) + 1) ^ 2)

theorem cost_nonneg (l : ℕ) : 0 ≤ cost N l := by
  have := electronicPartitionConstant_nonneg
  unfold cost
  positivity

theorem cost_zero : Tendsto (cost N) atTop (𝓝 0) := physicalElectronicFamily_ims_cost_zero

theorem metric (l : ℕ) (x : Configuration N) :
    (1 / 2 : ℝ) * ∑ i : Fin N × Fin 3, ∑ a : Fin N → Bool,
      fderiv ℝ (weight N l a) x (EuclideanSpace.single i 1) ^ 2 ≤ cost N l := by
  simp only [derivative]
  exact symmetricElectronicPartition_ims_metric l (electronicPositions x)

theorem permutation (l : ℕ) (a : Fin N → Bool)
    (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    weight N l a (permuteConfiguration π x) = weight N l a x := by
  have hp : electronicPositions (permuteConfiguration π x) = electronicPositions x ∘ π.symm := by
    funext i
    exact particle_permute π x i
  unfold weight
  rw [hp]
  exact symmetricElectronicPartition_perm _ a _ π.symm

def selected : Fin N → Bool := fun _ => false

theorem selected_weight (l : ℕ) (x : Configuration N) :
    weight N l (selected N) x = (physicalElectronicFamily l).multiplier x :=
  symmetricElectronicPartition_physical l x

theorem selected_support (l : ℕ) (x : Configuration N)
    (hx : x ∉ electronicConfigurationRegion ((l : ℝ) + 1)) :
    weight N l (selected N) x = 0 := by
  rw [selected_weight]
  exact physicalElectronicCutoff_support (by positivity) x hx

theorem selected_eventually_one (x : Configuration N) :
    ∀ᶠ l in atTop, weight N l (selected N) x = 1 := by
  obtain ⟨R, hR⟩ := exists_nat_ge (∑ i : Fin N, ‖particle x i‖)
  filter_upwards [eventually_ge_atTop R] with l hl
  change symmetricMultiplier (electronicPair ((l : ℝ) + 1))
    (fun _ : Fin N => false) (electronicPositions x) = 1
  rw [symmetricElectronicPartition_retained]
  apply electronicProduct_eq_one (by positivity)
  intro i
  change ‖particle x i‖ ≤ (l : ℝ) + 1
  exact (Finset.single_le_sum (fun j _ => norm_nonneg (particle x j))
    (Finset.mem_univ i)).trans
      (hR.trans ((by exact_mod_cast hl : (R : ℝ) ≤ l).trans (le_add_of_nonneg_right zero_le_one)))

theorem selected_tendsto (x : Configuration N) :
    Tendsto (fun l => weight N l (selected N) x) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' ((selected_eventually_one N x).mono fun _ h => h.symm)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem multiplier_contraction (l : ℕ) (a : Fin N → Bool)
    (u : Lp H 2 (volume : Measure (Configuration N))) :
    ‖(branch N l a).multiplier u‖ ≤ ‖u‖ := by
  exact (realL2Multiplier_norm_le _ _ _ _ u).trans_eq (one_mul _)

theorem selected_operator (l : ℕ) :
    (branch N l (selected N)).multiplier (H := H) = (physicalElectronicFamily l).operator := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [realL2Multiplier_apply (weight N l (selected N))
      (differentiable N l (selected N)).continuous.aestronglyMeasurable 1
      (ae_of_all _ (abs_le_one N l (selected N))) u,
    (physicalElectronicFamily l).operator_apply (K := H) u] with x h₁ h₂
  exact h₁.trans ((congrArg (· • u x) (selected_weight N l x)).trans h₂.symm)

theorem selected_wave_ae_zero (l : ℕ)
    (u : Lp H 2 (volume : Measure (Configuration N))) :
    ∀ᵐ x ∂volume, x ∉ electronicConfigurationRegion ((l : ℝ) + 1) →
      (branch N l (selected N)).multiplier u x = 0 := by
  filter_upwards [realL2Multiplier_apply (weight N l (selected N))
    (differentiable N l (selected N)).continuous.aestronglyMeasurable 1
    (ae_of_all _ (abs_le_one N l (selected N))) u] with x hx
  intro hs
  exact hx.trans (by rw [selected_support N l x hs, zero_smul])

theorem selected_strong (u : Lp H 2 (volume : Measure (Configuration N))) :
    Tendsto (fun l => (branch N l (selected N)).multiplier u) atTop (𝓝 u) := by
  have hnorm : Tendsto (fun l => eLpNorm
      ((fun x => weight N l (selected N) x • u x) - (fun x => u x)) 2 volume)
      atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_of_dominated_sq
      (b := fun x => ‖u x‖ ^ 2)
      (fun l => (differentiable N l (selected N)).continuous.aestronglyMeasurable.smul
        (Lp.aestronglyMeasurable u))
      (Lp.aestronglyMeasurable u)
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u))
    · intro l
      exact ae_of_all _ fun x => by
        apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        rw [Pi.smul_apply', norm_smul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right (abs_le_one N l (selected N) x)
          (norm_nonneg _)).trans_eq (one_mul _)
    · exact ae_of_all _ fun _ => le_rfl
    · exact ae_of_all _ fun x => by
        simpa only [Pi.smul_apply', one_smul] using (selected_tendsto N x).smul_const (u x)
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun l x => weight N l (selected N) x • u x)
    (fun l => (branch N l (selected N)).weighted_memLp u) u (Lp.memLp u)).mpr hnorm
  have he (l : ℕ) : ((branch N l (selected N)).weighted_memLp u).toLp
      (fun x => weight N l (selected N) x • u x) = (branch N l (selected N)).multiplier u := by
    apply Lp.ext
    exact ((branch N l (selected N)).weighted_memLp u).coeFn_toLp.trans
      (realL2Multiplier_apply _ _ _ _ _).symm
  simpa only [he, Lp.toLp_coeFn] using ht

end GptLean.PhysicalElectronicScalars
