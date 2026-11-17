import GptLean.RepresentabilityAmplitudePullback
import GptLean.PhysicalSourceCoordinates
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! The physical configuration measure grouped into its particle positions,
and exact factorization for scalar product amplitudes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.Representability

open MeasureTheory GptLean.SymmetricLift
open scoped ENNReal

abbrev AmplitudePosition := EuclideanSpace ℝ (Fin 3)

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Uncurrying scalar coordinates preserves the actual finite product volume. -/
theorem amplitude_uncurry_measurePreserving :
    MeasurePreserving (MeasurableEquiv.curry I J ℝ).symm volume volume := by
  refine ⟨(MeasurableEquiv.curry I J ℝ).symm.measurable, ?_⟩
  apply Eq.symm
  apply Measure.pi_eq
  intro s _
  have hp : (MeasurableEquiv.curry I J ℝ).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext x
    simp [Set.mem_pi, Prod.forall]
  rw [MeasurableEquiv.map_apply, hp]
  change (Measure.pi (fun _ : I => Measure.pi (fun _ : J => (volume : Measure ℝ))))
    (Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j)))) = _
  rw [Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun p : I × J => volume (s p))).symm

/-- Group all three Cartesian coordinates of each particle together. -/
def amplitudePositions (I : Type*) [Fintype I] :
    EuclideanSpace ℝ (I × Fin 3) ≃ᵐ (I → AmplitudePosition) :=
  (MeasurableEquiv.toLp 2 (I × Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.curry I (Fin 3) ℝ).trans
      (MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.toLp 2 (Fin 3 → ℝ)))

@[simp] theorem amplitudePositions_apply (x : EuclideanSpace ℝ (I × Fin 3))
    (i : I) (μ : Fin 3) : amplitudePositions I x i μ = x (i, μ) := rfl

theorem amplitudePositions_measurePreserving (I : Type*) [Fintype I] :
    MeasurePreserving (amplitudePositions I) volume volume := by
  have hc : MeasurePreserving (MeasurableEquiv.curry I (Fin 3) ℝ) volume volume :=
    (amplitude_uncurry_measurePreserving (I := I) (J := Fin 3)).symm
  have hp : MeasurePreserving
      (MeasurableEquiv.piCongrRight fun _ : I =>
        MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume :=
    volume_preserving_pi (fun _ => PiLp.volume_preserving_toLp (Fin 3))
  exact hp.comp (hc.comp (PiLp.volume_preserving_ofLp (I × Fin 3)))

/-- A product of arbitrary one-particle scalar factors on physical coordinates. -/
def productAmplitudeFamily (b : I → AmplitudePosition → ℝ)
    (x : EuclideanSpace ℝ (I × Fin 3)) : ℝ :=
  ∏ i, b i (amplitudePositions I x i)

/-- Fubini factorization, including the empty configuration. -/
theorem productAmplitudeFamily_integral (b : I → AmplitudePosition → ℝ) :
    (∫ x, productAmplitudeFamily b x) = ∏ i, ∫ y, b i y := by
  exact ((amplitudePositions_measurePreserving I).integral_comp'
    (fun x : I → AmplitudePosition => ∏ i, b i (x i))).trans
      (integral_fintype_prod_volume_eq_prod b)

theorem productAmplitudeFamily_square_integral (b : I → AmplitudePosition → ℝ) :
    (∫ x, (productAmplitudeFamily b x) ^ 2) = ∏ i, ∫ y, (b i y) ^ 2 := by
  have he : (fun x => (productAmplitudeFamily b x) ^ 2) =
      productAmplitudeFamily (fun i y => (b i y) ^ 2) := by
    funext x
    exact (Finset.prod_pow Finset.univ 2 _).symm
  rw [he, productAmplitudeFamily_integral]

theorem productAmplitudeFamily_memLp
    {b : I → AmplitudePosition → ℝ} (hb : ∀ i, MemLp (b i) 2 volume) :
    MemLp (productAmplitudeFamily b) 2 volume := by
  have hm : AEStronglyMeasurable (fun x : I → AmplitudePosition => ∏ i, b i (x i))
      volume :=
    Finset.univ.aestronglyMeasurable_fun_prod (fun i _ =>
      (hb i).1.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun _ => volume) i))
  have hi : Integrable (fun x : I → AmplitudePosition => ∏ i, (b i (x i)) ^ 2)
      volume :=
    Integrable.fintype_prod (fun i => (memLp_two_iff_integrable_sq (hb i).1).mp (hb i))
  have hprod : MemLp (fun x : I → AmplitudePosition => ∏ i, b i (x i)) 2 volume := by
    apply (memLp_two_iff_integrable_sq hm).mpr
    simpa only [Finset.prod_pow] using hi
  exact hprod.comp_measurePreserving (amplitudePositions_measurePreserving I)

/-- Independent factors that are locally L2 have a locally L2 product. -/
theorem productAmplitudeFamily_memLp_on_compact
    {b : I → AmplitudePosition → ℝ}
    (hb : ∀ i K, IsCompact K → MemLp (b i) 2 (volume.restrict K))
    {K : Set (EuclideanSpace ℝ (I × Fin 3))} (hK : IsCompact K) :
    MemLp (productAmplitudeFamily b) 2 (volume.restrict K) := by
  classical
  let C (i : I) := (fun x : EuclideanSpace ℝ (I × Fin 3) =>
    amplitudePositions I x i) '' K
  have hC (i : I) : IsCompact (C i) := by
    apply hK.image
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
      (continuous_pi fun μ => (EuclideanSpace.proj (i, μ)).continuous)
  let c (i : I) := (C i).indicator (b i)
  have hc (i : I) : MemLp (c i) 2 volume :=
    (memLp_indicator_iff_restrict (hC i).measurableSet).mpr (hb i (C i) (hC i))
  apply ((productAmplitudeFamily_memLp hc).restrict K).ae_eq
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  apply Finset.prod_congr rfl
  intro i _
  exact Set.indicator_of_mem (show amplitudePositions I x i ∈ C i from ⟨x, hx, rfl⟩) _

end GptLean.Representability
