import PfHk.PhysicalExternalSource
import PfHk.PhysicalSourceAbsorption
import PfHk.PhysicalExternalEnergy
import PfHk.PhysicalFreePerturbationData
import PfHk.PhysicalMixedSeries
import PfHk.PerturbationSmallness

/-! External potentials are absorbed on one radius, uniformly in the
center and on every smaller ball. The source is the actual finite sum
Hamiltonian on the free operator domain. The weak-operator domain bridge
is applied separately. -/

noncomputable section
namespace PfHk.PhysicalExternalCarlemanSum

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.CenteredPhysicalReference PfHk.PhysicalFieldRegularity
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain PfHk.PhysicalCarlemanInput
  PfHk.PhysicalDyadicEnergy PfHk.PhysicalDyadicPartition PfHk.PhysicalFreeCarleman
  PfHk.SmoothDyadicCutoffs PfHk.SmoothCutoffBounds PfHk.CarlemanWeights

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

local instance externalSumPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PfHk.PhysicalDyadicEnergy.dyadicEnergyPhotonRealInner

attribute [local irreducible] inclusion covariant radiation roughMultiply FreeGraph
  PhysicalExternalSource.total PhysicalExternalSource.term
  PhysicalPFReference.referenceSubspace

private theorem quarter_mul (x : ℝ) : (1 / 4 : ℝ) * x = x / 4 := by ring

private theorem full_constant (D E K F G : ℝ) (hD : D ≤ 64 * F)
    (hE : E ≤ 2 * D + 2 * K) (hK : K ≤ F) (hF : F ≤ 4 * G) : E ≤ 520 * G := by
  linarith only [hD, hE, hK, hF]

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (a : PhysicalExternalCoefficients.Data N)
  (S : CoordinateSobolev.Data PhotonFock N)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
  (joint : CoordinateComparisonSpectral.Data spectral)

def Estimate {O : Configuration N} (family : BufferedFamily O)
    (R : ℝ) (hR : 0 < R) (τ α C₂ C₂e : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u)
    (full : WaveSpace (Fin N × Fin 3)) : Prop :=
  Integrable (sourceEnergy O τ α full) ∧
    Integrable (PhysicalExternalEnergy.density F χ C e a.vector a.positive a.negative O τ α u hu) ∧
    (∫ X, PhysicalExternalEnergy.density F χ C e a.vector a.positive a.negative O τ α u hu X) ≤
      520 * ∫ X, sourceEnergy O τ α full X ∧
    PhysicalMixedSeries.Bound spectral (PhysicalFractionalCarleman.localized family R hR τ α u)
      (dyadicBeta α R) (radius R) τ (4 * 6144) (4 * C₂) (∫ X, sourceEnergy O τ α full X) ∧
    PhysicalMixedSeries.Bound spectral (PhysicalEnlargedFractionalCarleman.localized family R hR τ α u)
      (dyadicBeta α R) (radius R) τ (4 * 40960) (4 * C₂e) (∫ X, sourceEnergy O τ α full X) ∧
    ∀ᵐ X ∂volume, X ∉ Metric.ball O R → full X = 0

include S joint

theorem estimate_of_smallness
    {α : ℝ} (hα : 0 < α)
    (D : PhysicalFreePerturbationData.Data F χ C e spectral α)
    (hcore : AnnularCoreApproximation C (profile (N := N) F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e)
    {O : Configuration N} {R τ : ℝ} (hR : 0 < R) (hRD : R ≤ D.radius) (hτ : D.parameter ≤ τ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u)
    (free : WaveSpace (Fin N × Fin 3))
    (hfree : FreeGraph C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
      (profile_bound F χ 0) e u free)
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R)
    (P : PhysicalExternalSource.Products a C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e u)
    (σ : PhysicalExternalSource.Term N → ℝ) (hσ : ∀ t, 0 ≤ σ t)
    (hratio : ∀ t j, radius R j ^ PhysicalExternalSource.radiusExponent a t / dyadicBeta α R j ≤ σ t)
    (hsmall : (∑ t, PhysicalExternalSource.sourceConstant a S D.second D.enlargedSecond
      D.gradient e (profileBound F χ) t * σ t * τ ^ (-PhysicalExternalSource.parameterExponent a t)) ≤ 1 / 4)
    (hkin : PhysicalExternalSource.kineticConstant a S D.second * (R / τ) ≤ 1) :
    Estimate F χ C e a spectral (D.family O) R hR τ α D.second D.enlargedSecond u hu
      (free + PhysicalExternalSource.total a C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e u P) := by
  have hτ1 : 1 ≤ τ := D.parameter_ge_one.trans hτ
  have hτ0 : 0 < τ := lt_of_lt_of_le (by norm_num) hτ1
  have hsmall4 : 4 * R ≤ Real.exp (-2) :=
    (mul_le_mul_of_nonneg_left hRD (by norm_num)).trans
      (D.radius_four_small.trans (Real.exp_le_exp.mpr (by norm_num)))
  have hsmall2 : 2 * R ≤ Real.exp (-2) := by linarith only [hsmall4, hR]
  have hαR : R ≤ Real.exp (-(4 * α + 2)) := hRD.trans D.radius_alpha_small
  have hest := D.estimate τ hτ O R hR hRD u free hfree hsupp
  have hcoords := supported_coordinates F χ C e hcore hfree hsupp
  let ρ := Classical.choose hcoords
  let R' := Classical.choose (Classical.choose_spec hcoords)
  have hcoords' := Classical.choose_spec (Classical.choose_spec hcoords)
  have hsuppD : ∀ i, AnnularSupport (covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e i u) O R := fun i =>
    annularSupport_of_compact_annulus hR hcoords'.1 hcoords'.2.1 _ (hcoords'.2.2.2.1 i)
  let error := PhysicalExternalSource.total a C (profile F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e u P
  have herr := PhysicalExternalSource.source_bound a C (profile F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e u S spectral joint P (D.family O)
    hR hsmall4 hτ1 hα (D.gradient_eq O) free error hsupp hsuppD hest.2.2.1 hest.2.2.2
    σ hσ hratio (PhysicalExternalSource.total_ae a C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e u P)
  have hsource0 := PhysicalSourceAbsorption.sourceEnergy_nonneg O τ α free
  have herrsmall : (∫ X, sourceEnergy O τ α error X) ≤ (∫ X, sourceEnergy O τ α free X) / 4 :=
    herr.2.trans ((mul_le_mul_of_nonneg_right hsmall hsource0).trans_eq (quarter_mul _))
  have habs := PhysicalSourceAbsorption.absorb free (free + error) error rfl
    hest.1.source_integrable herr.1 herrsmall
  have hki := PhysicalExternalSource.kinetic_components_integrable a C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e u S spectral joint P
    (D.family O) hR hsmall2 hτ0 hα hαR free hsupp hest.2.2.1
  have hkb := PhysicalExternalSource.kinetic_bound a C (profile F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e u S spectral joint P (D.family O)
    hR hsmall2 hτ0 hα hαR free hsupp hest.2.2.1
  have henergy := PhysicalExternalEnergy.density_bound F χ C e a.vector a.positive a.negative
    u hu free hest.1.toEnergyData hki
  have hkinSum : (∑ i, ∫ X, positiveKineticWeight O τ α X *
      ‖roughMultiply (a.vector i) (inclusion (Fin N × Fin 3) (fun _ => 0) u) (hu.vector i) X‖ ^ 2) ≤
      ∫ X, sourceEnergy O τ α free X := by
    have heq : (∑ i, ∫ X, positiveKineticWeight O τ α X *
        ‖roughMultiply (a.vector i) (inclusion (Fin N × Fin 3) (fun _ => 0) u) (hu.vector i) X‖ ^ 2) =
        ∫ X, positiveKineticWeight O τ α X *
          ∑ i, ‖PhysicalExternalSource.vectorError a C (profile F χ 0) (profile_measurable F χ 0)
            (profileBound F χ) (profile_bound F χ 0) e u P i X‖ ^ 2 := by
      simp only [Finset.mul_sum]
      exact (integral_finsetSum _ (fun i _ => hki i)).symm
    exact heq.le.trans
      (hkb.2.trans ((mul_le_mul_of_nonneg_right hkin hsource0).trans_eq (one_mul _)))
  have hfullbound : (∫ X, PhysicalExternalEnergy.density F χ C e a.vector a.positive a.negative
      O τ α u hu X) ≤ 520 * ∫ X, sourceEnergy O τ α (free + error) X := by
    exact full_constant _ _ _ _ _ hest.2.1 henergy.2 hkinSum habs.2
  have hfreeSupport : ∀ᵐ X ∂volume, X ∉ Metric.ball O R → free X = 0 :=
    hcoords'.2.2.2.2.2.mono fun X hx hnot => hx (fun hmem =>
      hnot ((centeredAnnulus_dist hmem).2.trans_lt hcoords'.2.1))
  have herrorSupport := PhysicalExternalSource.total_supported_ball a C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e u P hsupp hsuppD
  have hfullSupport : ∀ᵐ X ∂volume, X ∉ Metric.ball O R → (free + error) X = 0 := by
    filter_upwards [Lp.coeFn_add free error, hfreeSupport, herrorSupport] with X hx hf he hnot
    exact hx.trans ((congrArg₂ (fun v w : PhotonFock => v + w) (hf hnot) (he hnot)).trans (zero_add _))
  exact ⟨habs.1, henergy.1, hfullbound,
    (PhysicalMixedSeries.of_standard hest.2.2.1).transfer_source (by norm_num) D.second_nonneg habs.2,
    (PhysicalMixedSeries.of_enlarged hest.2.2.2).transfer_source (by norm_num) D.enlargedSecond_nonneg habs.2,
    hfullSupport⟩

theorem exists_uniform_sum_estimate
    {α : ℝ} (hα : 0 < α)
    (D : PhysicalFreePerturbationData.Data F χ C e spectral α)
    (hD : HaslerHerbstDomain C (profile (N := N) F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e)
    (hcore : AnnularCoreApproximation C (profile (N := N) F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ D.radius ∧ r₀ < Real.exp (-2) ∧
      ∀ (O : Configuration N) (R : ℝ) (hR : 0 < R), R ≤ r₀ →
      ∀ τ : ℝ, D.parameter ≤ τ →
      ∀ (u : Reference (Fin N × Fin 3) (fun _ => 0))
        (hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u)
        (free : WaveSpace (Fin N × Fin 3))
        (hfree : FreeGraph C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
          (profile_bound F χ 0) e u free),
        AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R →
        ∃ P : PhysicalExternalSource.Products a C (profile F χ 0) (profile_measurable F χ 0)
          (profileBound F χ) (profile_bound F χ 0) e u,
          Estimate F χ C e a spectral (D.family O) R hR τ α D.second D.enlargedSecond u hu
            (free + PhysicalExternalSource.total a C (profile F χ 0) (profile_measurable F χ 0)
              (profileBound F χ) (profile_bound F χ 0) e u P) := by
  let K := PhysicalExternalSource.kineticConstant a S D.second
  have hK : 0 ≤ K := PhysicalExternalSource.kineticConstant_nonneg a S D.second_nonneg
  let Rmax := min D.radius (1 / (K + 1))
  have hRmax : 0 < Rmax := lt_min D.radius_pos (div_pos (by norm_num) (by linarith))
  have hex := PerturbationSmallness.exists_small_coefficient_with_ratios α hα
    (PhysicalExternalSource.radiusExponent a) (PhysicalExternalSource.parameterExponent a)
    (PhysicalExternalSource.sourceConstant a S D.second D.enlargedSecond D.gradient e (profileBound F χ))
    (PhysicalExternalSource.radiusExponent_pos a) (PhysicalExternalSource.parameterExponent_nonneg a)
    (PhysicalExternalSource.sourceConstant_nonneg a S D.second_nonneg D.enlargedSecond_nonneg)
    hRmax (by norm_num : (0 : ℝ) < 1 / 4)
  let r₀ := Classical.choose hex
  have hr := Classical.choose_spec hex
  have hr₀ := hr.1
  have hrmax := hr.2.1
  have hrsmall := hr.2.2.1
  have hcoeff := hr.2.2.2
  have hrD : r₀ ≤ D.radius := hrmax.trans (min_le_left _ _)
  refine ⟨r₀, hr₀, hrD, hrsmall, ?_⟩
  intro O R hR hRr₀ τ hτ u hu free hfree hsupp
  have hc : ComparisonDomain (fun _ => 0) u := (hD u).mp ⟨free, hfree⟩
  let P := PhysicalExternalSource.products_of_comparison a C (profile F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e u S spectral joint hc
  refine ⟨P, estimate_of_smallness F χ C e a S spectral joint hα D hcore
    hR (hRr₀.trans hrD) hτ u hu free hfree hsupp P
    (fun t => radiusSup α (PhysicalExternalSource.radiusExponent a t) R)
    (hcoeff R hR hRr₀).1 ?_ ((hcoeff R hR hRr₀).2.2 τ (D.parameter_ge_one.trans hτ)) ?_⟩
  · intro t j
    exact (hcoeff R hR hRr₀).2.1 t (radius R j) (radius_pos hR j) (radius_le hR.le j)
  · have hτ1 : 1 ≤ τ := D.parameter_ge_one.trans hτ
    have hRlim : R ≤ 1 / (K + 1) := hRr₀.trans (hrmax.trans (min_le_right _ _))
    have hden : 0 < K + 1 := by linarith only [hK]
    have hKR : K * R ≤ 1 := by
      have hh := (le_div_iff₀ hden).mp hRlim
      nlinarith only [hh, hR]
    exact (mul_le_mul_of_nonneg_left (div_le_self hR.le hτ1) hK).trans hKR

end PfHk.PhysicalExternalCarlemanSum
