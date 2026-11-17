import PfHk.PhysicalDyadicPartition
import PfHk.PhysicalFractionalCarleman

/-! Scalar weighted perturbations follow from the actual localized
Sobolev multiplier endpoint and the proved free fractional estimate. -/

noncomputable section
namespace PfHk.PhysicalDyadicScalarPerturbation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference GptLean.SymmetricLift
  PfHk.PhysicalCarlemanInput PfHk.PhysicalCutoffCommutator PfHk.PhysicalLocalEnergy
  PfHk.PhysicalDyadicEnergy PfHk.SmoothCutoffBounds PfHk.SmoothDyadicCutoffs
  PfHk.PhysicalDyadicPartition PfHk.PhysicalOperatorDomain
  PfHk.PhysicalDyadicIntegralFractional PfHk.DyadicFractional

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

attribute [local irreducible] inclusion PhysicalPFScalarMultiplier.multiply roughMultiply
  PfHk.PhysicalDyadicPartition.localizedField GptLean.ElectronicH1Multiplier.DifferentiableMultiplier.multiplier

variable {N : ℕ}

/-- An unweighted Sobolev multiplier endpoint for the actual comparison
graph. Coordinatewise multiplier theorems instantiate this property. -/
def ScalarFractionalMultiplier
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (b : Configuration N → ℝ) (s K : ℝ) : Prop :=
  ∀ (u : Reference (Fin N × Fin 3) (fun _ => 0)) (v : WaveSpace (Fin N × Fin 3))
    (hu : IsComparisonPair (fun _ => 0) u v),
    ∃ hb : HasMultiplier b (inclusion (Fin N × Fin 3) (fun _ => 0) u),
      ‖roughMultiply b (inclusion (Fin N × Fin 3) (fun _ => 0) u) hb‖ ^ 2 ≤
        K * fractionalNormSq spectral s u ⟨v, hu⟩

attribute [local irreducible] ScalarFractionalMultiplier PhysicalFractionalCarleman.MixedEstimate

/-- The singularly weighted error is integrable and has the precise
radius and parameter powers. Neither assertion is assumed for the error. -/
theorem scalar_source_bound
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    {O : Configuration N} (family : BufferedFamily O) {R τ α s K σ C₂ : ℝ}
    (hR : 0 < R) (hsmall : 2 * R ≤ Real.exp (-2)) (hτ : 0 < τ)
    (hα : 0 < α) (hs : 0 ≤ s) (hs2 : s ≤ 2) (hK : 0 ≤ K) (hσ : 0 ≤ σ)
    (b : Configuration N → ℝ) (hendpoint : ScalarFractionalMultiplier spectral b s K)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (f : WaveSpace (Fin N × Fin 3))
    (hb : HasMultiplier b (inclusion (Fin N × Fin 3) (fun _ => 0) u))
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R)
    (hmixed : PhysicalFractionalCarleman.MixedEstimate spectral family R hR τ α u f C₂)
    (hratio : ∀ j, radius R j ^ (4 - 2 * s) / dyadicBeta α R j ≤ σ) :
    Integrable (sourceEnergy O τ α
      (roughMultiply b (inclusion (Fin N × Fin 3) (fun _ => 0) u) hb)) ∧
      (∫ X, sourceEnergy O τ α
        (roughMultiply b (inclusion (Fin N × Fin 3) (fun _ => 0) u) hb) X) ≤
      (12 * K * σ * τ ^ (-(3 - 2 * s)) * ((s / 2) * C₂ + (1 - s / 2) * 6144)) *
        ∫ X, sourceEnergy O τ α f X := by
  classical
  unfold ScalarFractionalMultiplier at hendpoint
  let g := roughMultiply b (inclusion (Fin N × Fin 3) (fun _ => 0) u) hb
  have hg := roughMultiply_annularSupport b _ hb hsupp
  have hpartition := source_partition_bound family hR hsmall τ α g hg
  let J := Classical.choose hpartition
  have hpart := Classical.choose_spec hpartition
  unfold PhysicalFractionalCarleman.MixedEstimate at hmixed
  let v := Classical.choose hmixed
  let hv := Classical.choose (Classical.choose_spec hmixed)
  have hseries := Classical.choose_spec (Classical.choose_spec hmixed)
  let Q := fun j => fractionalNormSq spectral s
    (PhysicalFractionalCarleman.localized family R hR τ α u j) ⟨v j, hv j⟩
  have hQ (j : ℕ) : 0 ≤ Q j := fractionalNormSq_nonneg spectral s _ _
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
  have hfinite : (∑ j ∈ Finset.range J, coefficient τ (dyadicBeta α R j) (radius R j) s * Q j) ≤
      ((s / 2) * C₂ + (1 - s / 2) * 6144) * ∫ X, sourceEnergy O τ α f X :=
    ((hseries s hs hs2).1.sum_le_tsum (Finset.range J)
      (fun j _ => mul_nonneg (coefficient_pos hτ (dyadicBeta_pos hα hR hsmall j)
        (radius_pos hR j) s).le (hQ j))).trans (hseries s hs hs2).2
  have hsum := multiplier_sum_bound (Finset.range J) (dyadicBeta α R) (radius R) Q
    hτ hσ (fun j _ => dyadicBeta_pos hα hR hsmall j) (fun j _ => radius_pos hR j)
    (fun j _ => hQ j) (fun j _ => hratio j) hfinite
  refine ⟨hpart.1, hpart.2.trans ?_⟩
  calc
    _ ≤ 12 * ∑ j ∈ Finset.range J, radius R j ^ 2 * (K * Q j) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hlocal j) (sq_nonneg _)
    _ = (12 * K) * ∑ j ∈ Finset.range J, radius R j ^ (2 : ℝ) * Q j := by
      simp only [Real.rpow_two, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (12 * K) * (σ * τ ^ (-(3 - 2 * s)) *
        (((s / 2) * C₂ + (1 - s / 2) * 6144) * ∫ X, sourceEnergy O τ α f X)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end PfHk.PhysicalDyadicScalarPerturbation
