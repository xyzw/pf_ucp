import PfHk.PhysicalDyadicPartition
import PfHk.PhysicalMixedSeries
import PfHk.PhysicalDyadicCoordinatePerturbation

/-! Weighted scalar multiplication from the full mixed estimate with
arbitrary endpoint constants. This permits a second perturbation step for
the Pauli matrix coefficients after the orbital external fields. -/

noncomputable section
namespace PfHk.PauliCarlemanScalar

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

open PfHk.PhysicalDyadicScalarPerturbation

attribute [local irreducible] ScalarFractionalMultiplier PhysicalMixedSeries.Bound

/-- The singularly weighted error is integrable and has the precise
radius and parameter powers. Neither assertion is assumed for the error. -/
theorem scalar_source_bound
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    {O : Configuration N} (family : BufferedFamily O) {R τ α s K σ C₀ C₂ source : ℝ}
    (hR : 0 < R) (hsmall : 2 * R ≤ Real.exp (-2)) (hτ : 0 < τ)
    (hα : 0 < α) (hs : 0 ≤ s) (hs2 : s ≤ 2) (hK : 0 ≤ K) (hσ : 0 ≤ σ)
    (b : Configuration N → ℝ) (hendpoint : ScalarFractionalMultiplier spectral b s K)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hb : HasMultiplier b (inclusion (Fin N × Fin 3) (fun _ => 0) u))
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R)
    (hmixed : PhysicalMixedSeries.Bound spectral
      (PhysicalFractionalCarleman.localized family R hR τ α u)
      (dyadicBeta α R) (radius R) τ C₀ C₂ source)
    (hratio : ∀ j, radius R j ^ (4 - 2 * s) / dyadicBeta α R j ≤ σ) :
    Integrable (sourceEnergy O τ α
      (roughMultiply b (inclusion (Fin N × Fin 3) (fun _ => 0) u) hb)) ∧
      (∫ X, sourceEnergy O τ α
        (roughMultiply b (inclusion (Fin N × Fin 3) (fun _ => 0) u) hb) X) ≤
      (12 * K * σ * τ ^ (-(3 - 2 * s)) * ((s / 2) * C₂ + (1 - s / 2) * C₀)) *
        source := by
  classical
  unfold ScalarFractionalMultiplier at hendpoint
  let g := roughMultiply b (inclusion (Fin N × Fin 3) (fun _ => 0) u) hb
  have hg := roughMultiply_annularSupport b _ hb hsupp
  have hpartition := source_partition_bound family hR hsmall τ α g hg
  let J := Classical.choose hpartition
  have hpart := Classical.choose_spec hpartition
  unfold PhysicalMixedSeries.Bound at hmixed
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
      ((s / 2) * C₂ + (1 - s / 2) * C₀) * source :=
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
        (((s / 2) * C₂ + (1 - s / 2) * C₀) * source)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring


/-- Physical one-body Lp multiplication, with the multiplier domain and
weighted error estimate both derived from coordinate Sobolev calculus. -/
theorem coordinate_source_bound
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    {p : ℝ} (hp : 2 < p) (n : Fin N)
    (b : GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (hb : MemLp b (ENNReal.ofReal p) volume)
    {O : Configuration N} (family : BufferedFamily O)
    {R τ α σ C₀ C₂ source : ℝ}
    (hR : 0 < R) (hsmall : 2 * R ≤ Real.exp (-2)) (hτ : 0 < τ)
    (hα : 0 < α) (hσ : 0 ≤ σ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ∃ v, IsComparisonPair (fun _ => 0) u v)
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R)
    (hmixed : PhysicalMixedSeries.Bound spectral
      (PhysicalFractionalCarleman.localized family R hR τ α u)
      (dyadicBeta α R) (radius R) τ C₀ C₂ source)
    (hratio : ∀ j, radius R j ^ (4 - 2 * (3 / p)) / dyadicBeta α R j ≤ σ) :
    ∃ hm : HasMultiplier (CoordinateSobolev.coordinateCoefficient n b)
        (inclusion (Fin N × Fin 3) (fun _ => 0) u),
      Integrable (sourceEnergy O τ α
        (roughMultiply (CoordinateSobolev.coordinateCoefficient n b)
          (inclusion (Fin N × Fin 3) (fun _ => 0) u) hm)) ∧
      (∫ X, sourceEnergy O τ α
        (roughMultiply (CoordinateSobolev.coordinateCoefficient n b)
          (inclusion (Fin N × Fin 3) (fun _ => 0) u) hm) X) ≤
        (12 * PhysicalCoordinateMultipliers.coefficientNormSq S p b * σ *
          τ ^ (-(3 - 2 * (3 / p))) * (((3 / p) / 2) * C₂ +
            (1 - (3 / p) / 2) * C₀)) * source := by
  have hp0 : 0 < p := by linarith only [hp]
  have hs : 0 ≤ 3 / p := by positivity
  have hs2 : 3 / p ≤ 2 := (div_le_iff₀ hp0).mpr (by linarith only [hp])
  let hm := Classical.choose
    (PhysicalCoordinateMultipliers.scalar_multiplier S spectral joint hp n b hb u hu)
  refine ⟨hm, ?_⟩
  exact scalar_source_bound spectral family hR hsmall hτ hα hs hs2
    (PhysicalCoordinateMultipliers.coefficientNormSq_nonneg S p b) hσ
    (CoordinateSobolev.coordinateCoefficient n b)
    (PhysicalDyadicCoordinatePerturbation.coordinate_scalar_endpoint S spectral joint hp n b hb)
    u hm hsupp hmixed hratio

end PfHk.PauliCarlemanScalar
