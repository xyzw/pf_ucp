import GptLean.SymmetricLift.CollisionGeometry
import GptLean.SymmetricLift.PermutationGeometry
import Mathlib.Analysis.Convex.PathConnected

/-!
The regular configuration space used for continuation. Its full-measure and
open properties are inherited from the concrete collision geometry in
`gpt_lean`. Path connectedness is proved by joining two configurations through
a generic third configuration. Each forbidden direction lies in a proper
linear hyperplane.
-/

noncomputable section
namespace PfHk.ConfigurationGeometry

open MeasureTheory GptLean.SymmetricLift Set
open scoped Convex

theorem regular_isOpen (N : ℕ) : IsOpen (distinctConfigurations N) :=
  distinctConfigurations_isOpen N

theorem regular_ae (N : ℕ) :
    ∀ᵐ x : Configuration N ∂volume, x ∈ distinctConfigurations N :=
  ae_distinctConfigurations N

private theorem ae_pair_direction {N : ℕ} {x : Configuration N}
    {i j : Fin N} (hij : i ≠ j) {a : Fin 3}
    (ha : x (i, a) ≠ x (j, a)) :
    ∀ᵐ z : Configuration N ∂volume, ∀ s t : ℝ, t ≠ 0 →
      ∃ b : Fin 3, (s • x + t • z) (i, b) ≠ (s • x + t • z) (j, b) := by
  obtain ⟨b, hba⟩ : ∃ b : Fin 3, b ≠ a := exists_ne a
  let da := x (i, a) - x (j, a)
  let db := x (i, b) - x (j, b)
  let L : Configuration N →ₗ[ℝ] ℝ :=
    da • (EuclideanSpace.projₗ (i, b) - EuclideanSpace.projₗ (j, b)) -
      db • (EuclideanSpace.projₗ (i, a) - EuclideanSpace.projₗ (j, a))
  have hL : L.ker ≠ ⊤ := by
    intro h
    have hz : EuclideanSpace.single (i, b) 1 ∈ L.ker := by rw [h]; trivial
    have he : L (EuclideanSpace.single (i, b) 1) = 0 := hz
    have hba' : a ≠ b := Ne.symm hba
    simp [L, da, db, Ne.symm hij, hba'] at he
    exact ha (sub_eq_zero.mp he)
  have hnull := MeasureTheory.Measure.addHaar_submodule
    (volume : Measure (Configuration N)) L.ker hL
  have hae : ∀ᵐ z : Configuration N ∂volume, z ∉ L.ker := by
    exact measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [hae] with z hz
  intro s t ht
  by_contra h
  push Not at h
  have h₁ := h a
  have h₂ := h b
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h₁ h₂
  apply hz
  change L z = 0
  change da * (z (i, b) - z (j, b)) - db * (z (i, a) - z (j, a)) = 0
  apply (mul_eq_zero.mp (show t * (da * (z (i, b) - z (j, b)) -
      db * (z (i, a) - z (j, a))) = 0 from by
        have h₃ := congrArg (fun q : ℝ => db * q) h₁
        have h₄ := congrArg (fun q : ℝ => da * q) h₂
        dsimp [da, db] at *
        nlinarith only [h₃, h₄])).resolve_left ht

/-- Almost every endpoint can be joined to a fixed regular configuration by
a straight segment avoiding every collision diagonal. -/
theorem ae_segment_regular {N : ℕ} {x : Configuration N}
    (hx : x ∈ distinctConfigurations N) :
    ∀ᵐ z : Configuration N ∂volume, segment ℝ x z ⊆ distinctConfigurations N := by
  have hpair : ∀ i j : Fin N, ∀ hij : i ≠ j,
      ∀ᵐ z : Configuration N ∂volume, ∀ s t : ℝ, t ≠ 0 →
        ∃ b : Fin 3, (s • x + t • z) (i, b) ≠ (s • x + t • z) (j, b) := by
    intro i j hij
    obtain ⟨a, ha⟩ := hx i j hij
    exact ae_pair_direction hij ha
  have hall : ∀ᵐ z : Configuration N ∂volume, ∀ i j : Fin N, ∀ hij : i ≠ j,
      ∀ s t : ℝ, t ≠ 0 →
        ∃ b : Fin 3, (s • x + t • z) (i, b) ≠ (s • x + t • z) (j, b) := by
    simpa only [ae_all_iff] using hpair
  filter_upwards [hall] with z hz
  intro y hy
  rcases hy with ⟨s, t, hs, ht, hst, rfl⟩
  by_cases ht0 : t = 0
  · have hs1 : s = 1 := by linarith
    simpa [ht0, hs1] using hx
  · intro i j hij
    exact hz i j hij s t ht0

/-- The collision-free configuration space is path connected in every particle
number, including zero particles. -/
theorem regular_isPathConnected (N : ℕ) : IsPathConnected (distinctConfigurations N) := by
  obtain ⟨x, hx⟩ := (regular_ae N).exists
  refine ⟨x, hx, ?_⟩
  intro y hy
  obtain ⟨z, hz₁, hz₂⟩ := ((ae_segment_regular hx).and (ae_segment_regular hy)).exists
  exact (JoinedIn.of_segment_subset hz₁).trans (JoinedIn.of_segment_subset hz₂).symm

theorem regular_isConnected (N : ℕ) : IsConnected (distinctConfigurations N) :=
  (regular_isPathConnected N).isConnected

end PfHk.ConfigurationGeometry
