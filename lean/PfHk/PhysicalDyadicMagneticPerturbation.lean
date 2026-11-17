import PfHk.PhysicalDyadicProductRule
import PfHk.PhysicalDyadicScalarPerturbation
import PfHk.PhysicalEnlargedFractionalCarleman

/-! The endpoint magnetic source bound follows from the exact covariant
product rule and the proved enlarged fractional Carleman estimate. -/

noncomputable section
namespace PfHk.PhysicalDyadicMagneticPerturbation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference GptLean.SymmetricLift
  PfHk.PhysicalCarlemanInput PfHk.PhysicalLocalEnergy PfHk.PhysicalDyadicEnergy
  PfHk.SmoothCutoffBounds PfHk.SmoothDyadicCutoffs PfHk.PhysicalDyadicPartition
  PfHk.PhysicalOperatorDomain PfHk.PhysicalDyadicIntegralFractional PfHk.DyadicFractional
  PfHk.PhysicalDyadicScalarPerturbation PfHk.PhysicalDyadicProductRule

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

attribute [local irreducible] inclusion covariant PhysicalPFScalarMultiplier.multiply roughMultiply
  PfHk.PhysicalDyadicPartition.localizedField GptLean.ElectronicH1Multiplier.DifferentiableMultiplier.multiplier
  PfHk.SmoothDyadicCutoffs.weightedCutoff PfHk.SmoothDyadicCutoffs.Enlarged.weightedCutoff

variable {N : ℕ}
variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ i : Fin N × Fin 3, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i : Fin N × Fin 3, ∀ᵐ x : Configuration N ∂volume, ‖(κ i x).val‖ ≤ M) (e : ℝ)

def CovariantFractionalMultiplier
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (b : Configuration N → ℝ) (i : Fin N × Fin 3) (K : ℝ) : Prop :=
  ∀ (u : Reference (Fin N × Fin 3) (fun _ => 0)) (v : WaveSpace (Fin N × Fin 3))
    (hu : IsComparisonPair (fun _ => 0) u v),
    ∃ hb : HasMultiplier b (covariant _ (fun _ => 0) C κ hκ M hbound e i u),
      ‖roughMultiply b (covariant _ (fun _ => 0) C κ hκ M hbound e i u) hb‖ ^ 2 ≤
        K * fractionalNormSq spectral (3 / 2) u ⟨v, hu⟩

attribute [local irreducible] CovariantFractionalMultiplier ScalarFractionalMultiplier
  PhysicalEnlargedFractionalCarleman.MixedEstimate

theorem magnetic_source_bound
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    {O : Configuration N} (family : BufferedFamily O) {R τ α Kh Kl σ C₂ : ℝ}
    (hR : 0 < R) (hsmall : 4 * R ≤ Real.exp (-2))
    (hτ : 1 ≤ τ) (hα : 0 < α)
    (hKh : 0 ≤ Kh) (hKl : 0 ≤ Kl) (hσ : 0 ≤ σ)
    (b : Configuration N → ℝ) (i : Fin N × Fin 3)
    (hhigh : CovariantFractionalMultiplier C κ hκ M hbound e spectral b i Kh)
    (hlow : ScalarFractionalMultiplier spectral b (1 / 2) Kl)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (f : WaveSpace (Fin N × Fin 3))
    (hb : HasMultiplier b (covariant _ (fun _ => 0) C κ hκ M hbound e i u))
    (hsupp : AnnularSupport (covariant _ (fun _ => 0) C κ hκ M hbound e i u) O R)
    (hmixed : PhysicalEnlargedFractionalCarleman.MixedEstimate spectral family R hR τ α u f C₂)
    (hratio : ∀ j, radius R j / dyadicBeta α R j ≤ σ) :
    Integrable (sourceEnergy O τ α
      (roughMultiply b (covariant _ (fun _ => 0) C κ hκ M hbound e i u) hb)) ∧
      (∫ X, sourceEnergy O τ α
        (roughMultiply b (covariant _ (fun _ => 0) C κ hκ M hbound e i u) hb) X) ≤
      (24 * σ * (Kh * ((3 / 4) * C₂ + 10240) +
        Enlarged.firstWeightConstant family ^ 2 * Kl * ((1 / 4) * C₂ + 30720))) *
        ∫ X, sourceEnergy O τ α f X := by
  classical
  unfold CovariantFractionalMultiplier at hhigh
  unfold ScalarFractionalMultiplier at hlow
  have hsmall2 : 2 * R ≤ Real.exp (-2) := by linarith only [hsmall, hR]
  have hτ0 : 0 < τ := by linarith only [hτ]
  let g := roughMultiply b (covariant _ (fun _ => 0) C κ hκ M hbound e i u) hb
  have hg := roughMultiply_annularSupport b _ hb hsupp
  have hpartition := source_partition_bound family hR hsmall2 τ α g hg
  let J := Classical.choose hpartition
  have hpart := Classical.choose_spec hpartition
  unfold PhysicalEnlargedFractionalCarleman.MixedEstimate at hmixed
  let v := Classical.choose hmixed
  let hv := Classical.choose (Classical.choose_spec hmixed)
  have hseries := Classical.choose_spec (Classical.choose_spec hmixed)
  let z := PhysicalEnlargedFractionalCarleman.localized family R hR τ α u
  let Qh := fun j => fractionalNormSq spectral (3 / 2) (z j) ⟨v j, hv j⟩
  let Ql := fun j => fractionalNormSq spectral (1 / 2) (z j) ⟨v j, hv j⟩
  let G := Enlarged.firstWeightConstant family
  have hQh (j : ℕ) : 0 ≤ Qh j := fractionalNormSq_nonneg spectral _ _ _
  have hQl (j : ℕ) : 0 ≤ Ql j := fractionalNormSq_nonneg spectral _ _ _
  have hlocal (j : ℕ) : ‖localizedField family R hR τ α j g‖ ^ 2 ≤
      2 * (Kh * Qh j) + (2 * (G * τ / radius R j) ^ 2) * (Kl * Ql j) := by
    have hh := hhigh (z j) (v j) (hv j)
    have hl := hlow (z j) (v j) (hv j)
    let bh := Classical.choose hh
    let bl := Classical.choose hl
    have hloc := localized_covariant_multiplier_bound C κ hκ M hbound e family
      hR hsmall hτ hα u i b j hb bh bl
    exact hloc.trans (add_le_add
      (mul_le_mul_of_nonneg_left (Classical.choose_spec hh) (by norm_num))
      (mul_le_mul_of_nonneg_left (Classical.choose_spec hl) (by positivity)))
  have hfinite (s : ℝ) (hs : 0 ≤ s) (hs2 : s ≤ 2) :
      (∑ j ∈ Finset.range J, coefficient τ (dyadicBeta α R j) (radius R j) s *
        fractionalNormSq spectral s (z j) ⟨v j, hv j⟩) ≤
      ((s / 2) * C₂ + (1 - s / 2) * 40960) * ∫ X, sourceEnergy O τ α f X :=
    ((hseries s hs hs2).1.sum_le_tsum (Finset.range J)
      (fun j _ => mul_nonneg (coefficient_pos hτ0 (dyadicBeta_pos hα hR hsmall2 j)
        (radius_pos hR j) s).le (fractionalNormSq_nonneg spectral _ _ _))).trans
      (hseries s hs hs2).2
  have hhighsum : (∑ j ∈ Finset.range J, coefficient τ (dyadicBeta α R j) (radius R j) (3 / 2) *
      (Kh * Qh j)) ≤ (Kh * ((3 / 4) * C₂ + 10240)) * ∫ X, sourceEnergy O τ α f X := by
    have hh := hfinite (3 / 2) (by norm_num) (by norm_num)
    norm_num only at hh
    calc
      _ = Kh * ∑ j ∈ Finset.range J, coefficient τ (dyadicBeta α R j) (radius R j) (3 / 2) * Qh j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ Kh * (((3 / 4) * C₂ + 10240) * ∫ X, sourceEnergy O τ α f X) :=
        mul_le_mul_of_nonneg_left hh hKh
      _ = _ := by ring
  have hlowsum : (∑ j ∈ Finset.range J, coefficient τ (dyadicBeta α R j) (radius R j) (1 / 2) *
      (G ^ 2 * Kl * Ql j)) ≤ (G ^ 2 * Kl * ((1 / 4) * C₂ + 30720)) * ∫ X, sourceEnergy O τ α f X := by
    have hh := hfinite (1 / 2) (by norm_num) (by norm_num)
    norm_num only at hh
    calc
      _ = (G ^ 2 * Kl) * ∑ j ∈ Finset.range J, coefficient τ (dyadicBeta α R j) (radius R j) (1 / 2) * Ql j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ (G ^ 2 * Kl) * (((1 / 4) * C₂ + 30720) * ∫ X, sourceEnergy O τ α f X) :=
        mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg G) hKl)
      _ = _ := by ring
  have hsum := first_order_endpoint_sum (Finset.range J) (dyadicBeta α R) (radius R)
    (fun j => Kh * Qh j) (fun j => G ^ 2 * Kl * Ql j)
    hτ0 hσ (fun j _ => dyadicBeta_pos hα hR hsmall2 j) (fun j _ => radius_pos hR j)
    (fun j _ => mul_nonneg hKh (hQh j)) (fun j _ => mul_nonneg (mul_nonneg (sq_nonneg G) hKl) (hQl j))
    (fun j _ => hratio j) hhighsum hlowsum
  refine ⟨hpart.1, hpart.2.trans ?_⟩
  calc
    _ ≤ 12 * ∑ j ∈ Finset.range J, radius R j ^ 2 *
        (2 * (Kh * Qh j) + (2 * (G * τ / radius R j) ^ 2) * (Kl * Ql j)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hlocal j) (sq_nonneg _)
    _ = 24 * ∑ j ∈ Finset.range J, (radius R j ^ 2 * (Kh * Qh j) + τ ^ 2 * (G ^ 2 * Kl * Ql j)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      field_simp [(radius_pos hR j).ne']
      <;> ring
    _ ≤ 24 * (σ * (Kh * ((3 / 4) * C₂ + 10240) + G ^ 2 * Kl * ((1 / 4) * C₂ + 30720)) *
        ∫ X, sourceEnergy O τ α f X) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

end PfHk.PhysicalDyadicMagneticPerturbation
