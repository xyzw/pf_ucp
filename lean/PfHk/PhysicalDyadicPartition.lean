import PfHk.PhysicalDyadicEnergy
import PfHk.WeightedDyadicFiniteSupport
import PfHk.AeDyadicPartition
import PfHk.DyadicScalarNorm

/-! The actual weighted source integral is controlled by the constructed
finite dyadic localization. Only almost-everywhere annular support is used. -/

noncomputable section
namespace PfHk.PhysicalDyadicPartition

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference GptLean.SymmetricLift
  PfHk.PhysicalCarlemanInput PfHk.PhysicalCutoffCommutator PfHk.PhysicalLocalEnergy
  PfHk.PhysicalDyadicEnergy PfHk.SmoothCutoffBounds PfHk.SmoothDyadicCutoffs
  PfHk.CarlemanWeights

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

attribute [local irreducible] inclusion PhysicalPFScalarMultiplier.multiply

variable {N : ℕ}

def exponential (O : Configuration N) (τ α : ℝ) (X : Configuration N) : ℝ :=
  Real.exp (τ * weight α (-Real.log (dist X O)))

def localizedField {O : Configuration N} (family : BufferedFamily O)
    (R : ℝ) (hR : 0 < R) (τ α : ℝ) (j : ℕ)
    (g : WaveSpace (Fin N × Fin 3)) : WaveSpace (Fin N × Fin 3) :=
  (weightedCutoff family R hR τ α j).scalar.multiplier g

attribute [local irreducible] localizedField
  GptLean.ElectronicH1Multiplier.DifferentiableMultiplier.multiplier

theorem sourceEnergy_eq (O : Configuration N) (τ α : ℝ)
    (g : WaveSpace (Fin N × Fin 3)) (X : Configuration N) :
    sourceEnergy O τ α g X = exponential O τ α X ^ 2 * dist X O ^ 2 * ‖g X‖ ^ 2 := by
  have he : exponential O τ α X ^ 2 = Real.exp (2 * τ * weight α (-Real.log (dist X O))) := by
    unfold exponential
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  simp only [sourceEnergy, centeredSourceWeight, CarlemanSpatialDensity.sourceWeight, ← dist_eq_norm]

theorem source_integrable {O : Configuration N} {R : ℝ}
    (hR : R < 1) (τ α : ℝ) (g : WaveSpace (Fin N × Fin 3))
    (hsupp : AnnularSupport g O R) : Integrable (sourceEnergy O τ α g) := by
  obtain ⟨ρ, R', hρ, hρR, hR', hsupp⟩ := hsupp
  have hs : ∀ᵐ X ∂volume, X ∉ centeredAnnulus O ρ R' → ‖g X‖ ^ 2 = 0 := by
    filter_upwards [hsupp] with X hx hnot
    have hz : g X = 0 := by
      apply hx
      by_cases hlo : dist X O < ρ
      · exact Or.inl hlo
      · right
        by_contra! hhi
        exact hnot ⟨hhi, hlo⟩
    rw [hz]
    simp
  exact centered_annular_mul_integrable O ρ R' _ _
    (centered_weights_continuousOn O τ α hρ (hR'.trans hR)).2.2.2
    (Lp.memLp g).norm.integrable_sq hs

theorem annularSupport_of_zero_preserving
    {O : Configuration N} {R : ℝ} {u g : WaveSpace (Fin N × Fin 3)}
    (hu : AnnularSupport u O R)
    (hg : ∀ᵐ X ∂volume, u X = 0 → g X = 0) : AnnularSupport g O R := by
  obtain ⟨ρ, R', hρ, hρR, hR, hs⟩ := hu
  refine ⟨ρ, R', hρ, hρR, hR, ?_⟩
  filter_upwards [hs, hg] with X hx hgx hX
  exact hgx (hx hX)

theorem annularSupport_of_compact_annulus
    {O : Configuration N} {R ρ R' : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hR' : R' < R)
    (g : WaveSpace (Fin N × Fin 3))
    (hs : ∀ᵐ X ∂volume, X ∉ centeredAnnulus O ρ R' → g X = 0) :
    AnnularSupport g O R := by
  let lo := min (ρ / 2) (R / 4)
  let hi := (max R' (R / 2) + R) / 2
  have hlo : 0 < lo := lt_min (by positivity) (by positivity)
  have hloρ : lo < ρ := (min_le_left _ _).trans_lt (by linarith)
  have hloR : lo ≤ R / 4 := min_le_right _ _
  have hmax : max R' (R / 2) < R := max_lt hR' (by linarith)
  have hhiR : hi < R := by dsimp [hi]; linarith
  have hR'hi : R' < hi := by
    have hm := le_max_left R' (R / 2)
    dsimp [hi]
    linarith
  have hlohi : lo < hi := by
    have hm := le_max_right R' (R / 2)
    dsimp [hi]
    linarith
  refine ⟨lo, hi, hlo, hlohi, hhiR, ?_⟩
  filter_upwards [hs] with X hx hX
  apply hx
  intro hmem
  have hdist := centeredAnnulus_dist hmem
  rcases hX with hX | hX <;> linarith

theorem roughMultiply_annularSupport (b : Configuration N → ℝ)
    (u : WaveSpace (Fin N × Fin 3)) (hb : HasMultiplier b u)
    {O : Configuration N} {R : ℝ} (hu : AnnularSupport u O R) :
    AnnularSupport (roughMultiply b u hb) O R := by
  apply annularSupport_of_zero_preserving hu
  filter_upwards [roughMultiply_ae b u hb] with X hx hzero
  rw [hx, hzero, smul_zero]

theorem localizedField_norm_sq_ae {O : Configuration N} (family : BufferedFamily O)
    {R : ℝ} (hR : 0 < R) (hsmall : 2 * R ≤ Real.exp (-2))
    (τ α : ℝ) (j : ℕ) (g : WaveSpace (Fin N × Fin 3)) :
    (fun X : Configuration N => ‖localizedField family R hR τ α j g X‖ ^ 2) =ᵐ[volume]
      fun X => (cutoff family R j).scalar.weight X ^ 2 *
        exponential O τ α X ^ 2 * ‖g X‖ ^ 2 := by
  simpa only [localizedField, exponential] using
    DyadicScalarNorm.multiplier_product_norm_sq_ae (H := PhotonFock)
      (weightedCutoff family R hR τ α j).scalar
      (fun X => (cutoff family R j).scalar.weight X)
      (fun X => Real.exp (τ * weight α (-Real.log (dist X O)))) g
      (weightedCutoff_actual_weight family hR hsmall τ α j)

set_option maxHeartbeats 60000 in
/-- A finite part of the actual telescoping family gives the source
estimate with overlap factor three and radius factor four. -/
theorem source_partition_bound {O : Configuration N} (family : BufferedFamily O)
    {R : ℝ} (hR : 0 < R) (hsmall : 2 * R ≤ Real.exp (-2))
    (τ α : ℝ) (g : WaveSpace (Fin N × Fin 3)) (hsupp : AnnularSupport g O R) :
    ∃ J : ℕ, Integrable (sourceEnergy O τ α g) ∧
      (∫ X, sourceEnergy O τ α g X) ≤
        12 * ∑ j ∈ Finset.range J, radius R j ^ 2 * ‖localizedField family R hR τ α j g‖ ^ 2 := by
  classical
  have hR1 : R < 1 := by
    have h := Real.exp_lt_one_iff.mpr (by norm_num : (-2 : ℝ) < 0)
    linarith only [h, hsmall, hR]
  have hsource := source_integrable hR1 τ α g hsupp
  obtain ⟨ρ, R', hρ, hρR, hR', hg⟩ := hsupp
  obtain ⟨J, hJ⟩ := exists_inner_radius (R := R) hρ
  let η : ℕ → Configuration N → ℝ := fun j X => (cutoff family R j).scalar.weight X
  have hpart : ∀ᵐ X ∂volume, ‖g X‖ ^ 2 ≠ 0 →
      1 ≤ 3 * (∑ j ∈ Finset.range J, η j X ^ 2) := by
    filter_upwards [hg] with X hx hn
    have hnonzero : g X ≠ 0 := fun hz => hn (by simp [hz])
    have hlo : ρ ≤ dist X O := by
      by_contra! h
      exact hnonzero (hx (Or.inl h))
    have hhi : dist X O ≤ R' := by
      by_contra! h
      exact hnonzero (hx (Or.inr h))
    apply DyadicFractional.square_lower_of_sum_one (Finset.range J) (fun j => η j X)
      (sum_one_on_annulus family hR J hJ X hlo (hhi.trans hR'.le))
    exact_mod_cast overlap_card_le_three family hR (Finset.range J) X
  have hscale : ∀ᵐ X ∂volume, ∀ j ∈ Finset.range J,
      η j X ≠ 0 → dist X O ^ 2 ≤ 4 * radius R j ^ 2 := by
    filter_upwards [] with X j hj hη
    have h := weight_supported family hR j X hη
    have hs := pow_le_pow_left₀ dist_nonneg h.2.le 2
    norm_num [mul_pow] at hs
    exact hs
  have hint (j : ℕ) : Integrable (fun X => η j X ^ 2 *
      exponential O τ α X ^ 2 * ‖g X‖ ^ 2) :=
    (Lp.memLp (localizedField family R hR τ α j g)).norm.integrable_sq.congr
      (localizedField_norm_sq_ae family hR hsmall τ α j g)
  have hsource_eq : sourceEnergy O τ α g = fun X =>
      exponential O τ α X ^ 2 * dist X O ^ 2 * ‖g X‖ ^ 2 :=
    funext fun X => sourceEnergy_eq O τ α g X
  have hh := AeDyadicPartition.partition_radius_integral_bound_of_lower
    (μ := volume) (Finset.range J) η (exponential O τ α) (fun X => dist X O)
    (fun X => ‖g X‖ ^ 2) (radius R) (m := 3) (K := 4) (by norm_num)
    (ae_of_all _ fun X => sq_nonneg _) hpart hscale
    (by rw [← hsource_eq]; exact hsource.aestronglyMeasurable) (fun j _ => hint j)
  refine ⟨J, hsource, ?_⟩
  rw [hsource_eq]
  apply hh.2.trans_eq
  norm_num only
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_congr_ae (localizedField_norm_sq_ae family hR hsmall τ α j g), ← l2_norm_sq]

end PfHk.PhysicalDyadicPartition
