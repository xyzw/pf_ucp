import PfHk.PhysicalDyadicScalarPerturbation
import PfHk.DyadicWeightedPartition

/-! The lower magnetic endpoint also controls the actual kinetic-weight
error needed when replacing the free covariant derivative. -/

noncomputable section
namespace PfHk.PhysicalDyadicKineticPerturbation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference GptLean.SymmetricLift
  PfHk.PhysicalCarlemanInput PfHk.PhysicalLocalEnergy PfHk.PhysicalDyadicEnergy
  PfHk.SmoothCutoffBounds PfHk.SmoothDyadicCutoffs PfHk.PhysicalDyadicPartition
  PfHk.PhysicalOperatorDomain PfHk.PhysicalDyadicIntegralFractional PfHk.DyadicFractional
  PfHk.PhysicalDyadicScalarPerturbation PfHk.CarlemanWeights

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

attribute [local irreducible] inclusion PhysicalPFScalarMultiplier.multiply roughMultiply
  PfHk.PhysicalDyadicPartition.localizedField GptLean.ElectronicH1Multiplier.DifferentiableMultiplier.multiplier

variable {N : ℕ}

def kineticFieldEnergy (O : Configuration N) (τ α : ℝ)
    (g : WaveSpace (Fin N × Fin 3)) (X : Configuration N) : ℝ :=
  positiveKineticWeight O τ α X * ‖g X‖ ^ 2

theorem kinetic_integrable {O : Configuration N} {R : ℝ}
    (hR : R < 1) (τ α : ℝ) (g : WaveSpace (Fin N × Fin 3))
    (hsupp : AnnularSupport g O R) : Integrable (kineticFieldEnergy O τ α g) := by
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
    simp [hz]
  exact centered_annular_mul_integrable O ρ R' _ _
    (continuousOn_const.sup (centered_weights_continuousOn O τ α hρ (hR'.trans hR)).2.1)
    (Lp.memLp g).norm.integrable_sq hs

set_option maxHeartbeats 60000 in
theorem kinetic_partition_bound {O : Configuration N} (family : BufferedFamily O)
    {R τ α : ℝ} (hR : 0 < R) (hsmall : 2 * R ≤ Real.exp (-2))
    (hτ : 0 ≤ τ) (hα : 0 < α) (hαR : R ≤ Real.exp (-(4 * α + 2)))
    (g : WaveSpace (Fin N × Fin 3)) (hsupp : AnnularSupport g O R) :
    ∃ J : ℕ, Integrable (kineticFieldEnergy O τ α g) ∧
      (∫ X, kineticFieldEnergy O τ α g X) ≤
        24 * ∑ j ∈ Finset.range J, τ * dyadicBeta α R j *
          ‖localizedField family R hR τ α j g‖ ^ 2 := by
  classical
  have hR1 : R < 1 := by
    have h := Real.exp_lt_one_iff.mpr (by norm_num : (-2 : ℝ) < 0)
    linarith only [h, hsmall, hR]
  have hkin := kinetic_integrable hR1 τ α g hsupp
  obtain ⟨ρ, R', hρ, hρR, hR', hg⟩ := hsupp
  obtain ⟨J, hJ⟩ := exists_inner_radius (R := R) hρ
  let η : ℕ → Configuration N → ℝ := fun j X => (cutoff family R j).scalar.weight X
  let q : ℕ → Configuration N → ℝ := fun j X => η j X ^ 2 * exponential O τ α X ^ 2 * ‖g X‖ ^ 2
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
    apply square_lower_of_sum_one (Finset.range J) (fun j => η j X)
      (sum_one_on_annulus family hR J hJ X hlo (hhi.trans hR'.le))
    exact_mod_cast overlap_card_le_three family hR (Finset.range J) X
  have hweight (j : ℕ) (X : Configuration N) (hη : η j X ≠ 0) :
      positiveKineticWeight O τ α X ≤ 8 * τ * dyadicBeta α R j * exponential O τ α X ^ 2 := by
    have hs := weight_supported family hR j X hη
    have hrj : radius R j ≤ Real.exp (-2) := (radius_le hR.le j).trans (by linarith only [hsmall, hR])
    have hb := (beta_annular_comparison hα ((radius_le hR.le j).trans hαR) (radius_pos hR j) hrj hs.1.le hs.2.le).2
    have hlog := (logarithmic_annular_comparison (radius_pos hR j) hrj hs.1.le hs.2.le).1
    have hb0 := (beta_pos hα hlog).le
    have he : exponential O τ α X ^ 2 = Real.exp (2 * τ * weight α (-Real.log (dist X O))) := by
      unfold exponential
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have hw : centeredKineticWeight O τ α X =
        exponential O τ α X ^ 2 * τ * beta α (-Real.log (dist X O)) := by
      rw [he]
      simp only [centeredKineticWeight, CarlemanSpatialDensity.kineticWeight, ← dist_eq_norm]
    rw [positiveKineticWeight, hw, max_eq_right (mul_nonneg (mul_nonneg (sq_nonneg _) hτ) hb0)]
    exact (mul_le_mul_of_nonneg_left hb (mul_nonneg (sq_nonneg _) hτ)).trans_eq (by dsimp [dyadicBeta]; ring)
  have hint (j : ℕ) : Integrable (q j) :=
    (Lp.memLp (localizedField family R hR τ α j g)).norm.integrable_sq.congr
      (localizedField_norm_sq_ae family hR hsmall τ α j g)
  have hh := DyadicWeightedPartition.integral_bound (μ := volume) (Finset.range J) η
    (positiveKineticWeight O τ α) (exponential O τ α) (fun X => ‖g X‖ ^ 2)
    (fun j => 8 * τ * dyadicBeta α R j) (m := 3) (by norm_num)
    (ae_of_all _ fun X => le_max_left _ _) (ae_of_all _ fun X => sq_nonneg _) hpart
    (ae_of_all _ fun X j _ hη => hweight j X hη) hkin (fun j _ => hint j)
  refine ⟨J, hkin, hh.trans_eq ?_⟩
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_congr_ae (localizedField_norm_sq_ae family hR hsmall τ α j g), ← l2_norm_sq]
  ring

attribute [local irreducible] ScalarFractionalMultiplier PhysicalFractionalCarleman.MixedEstimate

theorem scalar_kinetic_bound
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    {O : Configuration N} (family : BufferedFamily O) {R τ α K C₂ : ℝ}
    (hR : 0 < R) (hsmall : 2 * R ≤ Real.exp (-2)) (hτ : 0 < τ)
    (hα : 0 < α) (hαR : R ≤ Real.exp (-(4 * α + 2))) (hK : 0 ≤ K)
    (b : Configuration N → ℝ) (hendpoint : ScalarFractionalMultiplier spectral b (1 / 2) K)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (f : WaveSpace (Fin N × Fin 3))
    (hb : HasMultiplier b (inclusion (Fin N × Fin 3) (fun _ => 0) u))
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R)
    (hmixed : PhysicalFractionalCarleman.MixedEstimate spectral family R hR τ α u f C₂) :
    Integrable (kineticFieldEnergy O τ α
      (roughMultiply b (inclusion (Fin N × Fin 3) (fun _ => 0) u) hb)) ∧
      (∫ X, kineticFieldEnergy O τ α
        (roughMultiply b (inclusion (Fin N × Fin 3) (fun _ => 0) u) hb) X) ≤
      (24 * K * (R / τ) * ((1 / 4) * C₂ + 4608)) * ∫ X, sourceEnergy O τ α f X := by
  classical
  unfold ScalarFractionalMultiplier at hendpoint
  let g := roughMultiply b (inclusion (Fin N × Fin 3) (fun _ => 0) u) hb
  have hg := roughMultiply_annularSupport b _ hb hsupp
  have hpartition := kinetic_partition_bound family hR hsmall hτ.le hα hαR g hg
  let J := Classical.choose hpartition
  have hpart := Classical.choose_spec hpartition
  unfold PhysicalFractionalCarleman.MixedEstimate at hmixed
  let v := Classical.choose hmixed
  let hv := Classical.choose (Classical.choose_spec hmixed)
  have hseries := Classical.choose_spec (Classical.choose_spec hmixed)
  let Q := fun j => fractionalNormSq spectral (1 / 2)
    (PhysicalFractionalCarleman.localized family R hR τ α u j) ⟨v j, hv j⟩
  have hQ (j : ℕ) : 0 ≤ Q j := fractionalNormSq_nonneg spectral _ _ _
  have hlocal (j : ℕ) : ‖localizedField family R hR τ α j g‖ ^ 2 ≤ K * Q j := by
    have hend := hendpoint (PhysicalFractionalCarleman.localized family R hR τ α u j) (v j) (hv j)
    let hj := Classical.choose hend
    have hbound := Classical.choose_spec hend
    have heq : roughMultiply b (inclusion (Fin N × Fin 3) (fun _ => 0)
      (PhysicalFractionalCarleman.localized family R hR τ α u j)) hj =
        localizedField family R hR τ α j g := by
      simpa only [PhysicalFractionalCarleman.localized, localizedField, g] using
        roughMultiply_reference_localize (fun _ => 0)
          (weightedCutoff family R hR τ α j).scalar b u hb hj
    rw [← heq]
    exact hbound
  have hfinite : (∑ j ∈ Finset.range J, coefficient τ (dyadicBeta α R j) (radius R j) (1 / 2) * Q j) ≤
      ((1 / 4) * C₂ + 4608) * ∫ X, sourceEnergy O τ α f X := by
    have hh := ((hseries (1 / 2) (by norm_num) (by norm_num)).1.sum_le_tsum (Finset.range J)
      (fun j _ => mul_nonneg (coefficient_pos hτ (dyadicBeta_pos hα hR hsmall j)
        (radius_pos hR j) (1 / 2)).le (hQ j))).trans
      (hseries (1 / 2) (by norm_num) (by norm_num)).2
    norm_num at hh
    exact hh
  have hpoint (j : ℕ) : τ * dyadicBeta α R j * ‖localizedField family R hR τ α j g‖ ^ 2 ≤
      (K * (R / τ)) * (coefficient τ (dyadicBeta α R j) (radius R j) (1 / 2) * Q j) := by
    have hid : τ * dyadicBeta α R j =
        (radius R j / τ) * coefficient τ (dyadicBeta α R j) (radius R j) (1 / 2) := by
      norm_num [coefficient, Real.rpow_neg_one, Real.rpow_two]
      field_simp [hτ.ne', (radius_pos hR j).ne']
      <;> ring
    calc
      _ ≤ τ * dyadicBeta α R j * (K * Q j) :=
        mul_le_mul_of_nonneg_left (hlocal j) (mul_nonneg hτ.le (dyadicBeta_pos hα hR hsmall j).le)
      _ = K * ((radius R j / τ) * (coefficient τ (dyadicBeta α R j) (radius R j) (1 / 2) * Q j)) := by rw [hid]; ring
      _ ≤ K * ((R / τ) * (coefficient τ (dyadicBeta α R j) (radius R j) (1 / 2) * Q j)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (radius_le hR.le j) hτ.le)
          (mul_nonneg (coefficient_pos hτ (dyadicBeta_pos hα hR hsmall j) (radius_pos hR j) _).le (hQ j))) hK
      _ = _ := by ring
  refine ⟨hpart.1, hpart.2.trans ?_⟩
  calc
    _ ≤ 24 * ∑ j ∈ Finset.range J, (K * (R / τ)) *
        (coefficient τ (dyadicBeta α R j) (radius R j) (1 / 2) * Q j) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hpoint j) (by norm_num)
    _ = (24 * K * (R / τ)) * ∑ j ∈ Finset.range J,
        coefficient τ (dyadicBeta α R j) (radius R j) (1 / 2) * Q j := by rw [← Finset.mul_sum]; ring
    _ ≤ (24 * K * (R / τ)) * (((1 / 4) * C₂ + 4608) * ∫ X, sourceEnergy O τ α f X) :=
      mul_le_mul_of_nonneg_left hfinite (by positivity)
    _ = _ := by ring

end PfHk.PhysicalDyadicKineticPerturbation
