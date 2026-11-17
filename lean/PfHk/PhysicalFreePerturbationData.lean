import PfHk.PhysicalFractionalCarleman
import PfHk.PhysicalEnlargedFractionalCarleman

/-! Joint free estimates on one constructed cutoff family. This package
is derived below from the proved free Carleman theorem. It is not an
additional background assumption in the perturbed theorem. -/

noncomputable section
namespace PfHk.PhysicalFreePerturbationData

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.CenteredPhysicalReference PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.PhysicalCarlemanInput
  PfHk.PhysicalDyadicEnergy PfHk.PhysicalFreeCarleman PfHk.CarlemanSpatialDensity
  PfHk.SmoothCutoffBounds PfHk.SmoothDyadicCutoffs

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

local instance freeDataPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PfHk.PhysicalDyadicEnergy.dyadicEnergyPhotonRealInner

attribute [local irreducible] inclusion covariant radiation FreeGraph

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (e : ℝ)

def Estimates (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    {O : Configuration N} (family : BufferedFamily O)
    (R : ℝ) (hR : 0 < R) (τ α C₂ C₂e : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (f : WaveSpace (Fin N × Fin 3)) : Prop :=
  EnergyEstimate F χ C e O R τ α u f ∧
    (∫ X, centeredOperatorDensity F χ C e O τ α u X) ≤
      64 * ∫ X, sourceEnergy O τ α f X ∧
    PhysicalFractionalCarleman.MixedEstimate spectral family R hR τ α u f C₂ ∧
    PhysicalEnlargedFractionalCarleman.MixedEstimate spectral family R hR τ α u f C₂e

structure Data (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3)) (α : ℝ) where
  family : ∀ O : Configuration N, BufferedFamily O
  radius : ℝ
  radius_pos : 0 < radius
  radius_small : radius < Real.exp (-2)
  radius_four_small : 4 * radius ≤ Real.exp (-4)
  radius_alpha_small : radius ≤ Real.exp (-(4 * α + 2))
  parameter : ℝ
  parameter_ge_one : 1 ≤ parameter
  second : ℝ
  second_nonneg : 0 ≤ second
  enlargedSecond : ℝ
  enlargedSecond_nonneg : 0 ≤ enlargedSecond
  gradient : ℝ
  gradient_nonneg : 0 ≤ gradient
  gradient_eq : ∀ O, Enlarged.firstWeightConstant (family O) = gradient
  estimate : ∀ τ : ℝ, parameter ≤ τ → ∀ (O : Configuration N) (R : ℝ)
    (hR : 0 < R), R ≤ radius →
    ∀ (u : Reference (Fin N × Fin 3) (fun _ => 0)) (f : WaveSpace (Fin N × Fin 3)),
    FreeGraph C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
      (profileBound F χ) (profile_bound (N := N) F χ 0) e u f →
    AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R →
    Estimates F χ C e spectral (family O) R hR τ α second enlargedSecond u f

theorem global_density_bound {O : Configuration N} {R τ α : ℝ}
    {u : Reference (Fin N × Fin 3) (fun _ => 0)} {f : WaveSpace (Fin N × Fin 3)}
    (hd : EnergyData F χ C e O R τ α u f)
    (hball : (∫ X in Metric.ball O R, centeredOperatorDensity F χ C e O τ α u X) ≤
      64 * ∫ X in Metric.ball O R, centeredSource O τ α (fun Y => ‖f Y‖ ^ 2) X) :
    (∫ X, centeredOperatorDensity F χ C e O τ α u X) ≤
      64 * ∫ X, sourceEnergy O τ α f X := by
  have hdS : ∀ᵐ X ∂volume, X ∉ Metric.ball O R →
      centeredOperatorDensity F χ C e O τ α u X = 0 := by
    filter_upwards [hd.mass_supported, hd.kinetic_supported, hd.radiation_supported]
      with X hm hk hr hX
    rw [density_eq_energies, hm hX, hk hX, hr hX]
    norm_num
  have hsball : (∫ X in Metric.ball O R,
      centeredSource O τ α (fun Y => ‖f Y‖ ^ 2) X) = ∫ X, sourceEnergy O τ α f X :=
    (integral_congr_ae (ae_of_all _ fun X => source_eq_energy O τ α f X)).trans
      (setIntegral_eq_integral_of_ae_compl_eq_zero hd.source_supported)
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hdS, ← hsball]
  exact hball

open PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.SphereCoreGeometry
  PfHk.OrdinaryPolarSobolevChart

theorem exists_data (hUV : CarlemanUV χ)
    (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
    (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
    (S : StandardPolarSobolevCharts N) (L : StandardLogPolarCalculus (Fin N × Fin 3))
    (hN : 0 < Fintype.card (Fin N × Fin 3))
    (D : WeylCoreReference.StandardWeylFormCoreDensity W B)
    (A : ∀ O : Configuration N, AnnularCoreApproximation C (profile F χ O)
      (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (hD : HaslerHerbstDomain C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
      (profileBound F χ) (profile_bound (N := N) F χ 0) e)
    (hG : HaslerHerbstGraphNorm C (profile (N := N) F χ 0)
      (profile_measurable (N := N) F χ 0) (profileBound F χ) (profile_bound (N := N) F χ 0) e)
    (α : ℝ) (hα : 0 < α) :
    Nonempty (Data F χ C e spectral α) := by
  classical
  have hexFamily := exists_uniform_buffered_family (I := Fin N × Fin 3)
  let B₁ := Classical.choose hexFamily
  let B₂ := Classical.choose (Classical.choose_spec hexFamily)
  have hfamily := (Classical.choose_spec (Classical.choose_spec hexFamily)).2.2
  let family : ∀ O : Configuration N, BufferedFamily O := fun O => Classical.choose (hfamily O)
  have hfirst (O : Configuration N) : (family O).firstBound = B₁ :=
    (Classical.choose_spec (hfamily O)).1
  have hsecond (O : Configuration N) : (family O).secondBound = B₂ :=
    (Classical.choose_spec (hfamily O)).2
  have hex := PhysicalFreeCarleman.exists_uniform_estimate F χ hUV e C W B P G S L hN D A
    α hα
  let rF := Classical.choose hex
  let τ₀ := Classical.choose (Classical.choose_spec hex)
  have hfree := Classical.choose_spec (Classical.choose_spec hex)
  -- The radius is also taken below the exponent threshold of the annular
  -- comparison of `β`.
  let r₀ := min rF (min (Real.exp (-4) / 4) (Real.exp (-(4 * α + 2))))
  have hr₀ : 0 < r₀ :=
    lt_min hfree.1 (lt_min (div_pos (Real.exp_pos _) (by norm_num)) (Real.exp_pos _))
  let C₂ := PhysicalFractionalCarleman.secondConstantOfBounds N hG.bound B₁ B₂
  let C₂e := PhysicalEnlargedFractionalCarleman.secondConstantOfBounds N hG.bound B₁ B₂
  let G₁ : ℝ := (9 / 2) * B₁ + 4
  have hC₂ : 0 ≤ C₂ := by
    dsimp [C₂, PhysicalFractionalCarleman.secondConstantOfBounds]
    positivity
  have hC₂e : 0 ≤ C₂e := by
    dsimp [C₂e, PhysicalEnlargedFractionalCarleman.secondConstantOfBounds]
    positivity
  have hG₁ (O : Configuration N) : Enlarged.firstWeightConstant (family O) = G₁ := by
    dsimp [Enlarged.firstWeightConstant, G₁]
    rw [hfirst O]
  refine ⟨{
    family := family
    radius := r₀
    radius_pos := hr₀
    radius_small := (min_le_left _ _).trans_lt hfree.2.1
    radius_four_small := by
      have h : r₀ ≤ Real.exp (-4) / 4 := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    radius_alpha_small := (min_le_right _ _).trans (min_le_right _ _)
    parameter := τ₀
    parameter_ge_one := hfree.2.2.1
    second := C₂
    second_nonneg := hC₂
    enlargedSecond := C₂e
    enlargedSecond_nonneg := hC₂e
    gradient := G₁
    gradient_nonneg := (hG₁ 0) ▸ Enlarged.firstWeightConstant_nonneg (family 0)
    gradient_eq := hG₁
    estimate := ?_
  }⟩
  intro τ hτ O R hR hRsmall u f hu hsupp
  have hRfree : R ≤ rF := hRsmall.trans (min_le_left _ _)
  have hRone : R < 1 := hRfree.trans_lt
    (hfree.2.1.trans (Real.exp_lt_one_iff.mpr (by norm_num)))
  have hτone : 1 ≤ τ := hfree.2.2.1.trans hτ
  have hsmall : 4 * R ≤ Real.exp (-4) := by
    have h := (hRsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
    linarith
  have hαR : R ≤ Real.exp (-(4 * α + 2)) :=
    (hRsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hsmall₂ : 2 * R ≤ Real.exp (-2) := by
    have h := Real.exp_le_exp.mpr (show (-4 : ℝ) ≤ -2 by norm_num)
    linarith
  have hball := hfree.2.2.2 τ hτ O R hR hRfree u f hu hsupp
  have he := energy_estimate_of_ball F χ C e (A 0) hRone
    (zero_le_one.trans hτone) hα hu hsupp hball
  refine ⟨he, global_density_bound F χ C e he.toEnergyData hball, ?_, ?_⟩
  · have hconst := PhysicalFractionalCarleman.secondConstant_eq_bounds hG.bound
      (family O) B₁ B₂ (hfirst O) (hsecond O)
    dsimp only [C₂]
    rw [← hconst]
    exact PhysicalFractionalCarleman.estimate_of_energy F χ C e spectral hD hG
      (family O) hR hsmall₂ hτone hα hαR hu he
  · have hconst := PhysicalEnlargedFractionalCarleman.secondConstant_eq_bounds hG.bound
      (family O) B₁ B₂ (hfirst O) (hsecond O)
    dsimp only [C₂e]
    rw [← hconst]
    exact PhysicalEnlargedFractionalCarleman.estimate_of_energy F χ C e spectral hD hG
      (family O) hR hsmall hτone hα hαR hu he

end PfHk.PhysicalFreePerturbationData
