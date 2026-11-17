import PfHk.PhysicalDyadicEnergy
import PfHk.PhysicalDyadicGraph
import PfHk.PhysicalDyadicSpectral
import Mathlib.Topology.Algebra.InfiniteSum.Real
import PfHk.EnlargedWeightedDyadicBounds

/-! The mixed electronic and radiation Carleman estimate for the actual
free Pauli–Fierz operator and the enlarged annular family. Both dyadic endpoints are derived from the
proved free estimate and the constructed scalar annular multipliers. -/

noncomputable section
namespace PfHk.PhysicalEnlargedFractionalCarleman

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain PfHk.CenteredPhysicalReference
  PfHk.PhysicalCutoffCommutator PfHk.PhysicalLocalEnergy PfHk.PhysicalDyadicEnergy
  PfHk.SmoothCutoffBounds PfHk.SmoothDyadicCutoffs PfHk.DyadicFractional
  PfHk.PhysicalDyadicIntegralFractional

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

local instance fractionalPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PfHk.PhysicalDyadicEnergy.dyadicEnergyPhotonRealInner

attribute [local irreducible] inclusion covariant radiation PhysicalPFScalarMultiplier.multiply
  externalCovariant FreeGraph

variable {N : ℕ}

private theorem small_two {R : ℝ} (hR : 0 < R) (hsmall : 4 * R ≤ Real.exp (-4)) :
    2 * R ≤ Real.exp (-2) := by
  have he : Real.exp (-4) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by norm_num)
  linarith

def secondConstant {O : Configuration N} (g : ℝ) (family : BufferedFamily O) : ℝ :=
  2*g^2 * (2*80 + 4*((40*(Fintype.card (Fin N × Fin 3) : ℝ)*Enlarged.firstWeightConstant family^2)*64) +
    (640*((Fintype.card (Fin N × Fin 3) : ℝ)*Enlarged.secondWeightConstant family)^2)*64 + 40960)

def secondConstantOfBounds (N : ℕ) (g b₁ b₂ : ℝ) : ℝ :=
  2*g^2 * (2*80 + 4*((40*(Fintype.card (Fin N × Fin 3) : ℝ)*((9/2:ℝ)*b₁+4)^2)*64) +
    (640*((Fintype.card (Fin N × Fin 3) : ℝ)*((65/4:ℝ)*b₂+36*b₁+80))^2)*64 + 40960)

theorem secondConstant_eq_bounds {O : Configuration N} (g : ℝ) (family : BufferedFamily O)
    (b₁ b₂ : ℝ) (h₁ : family.firstBound = b₁) (h₂ : family.secondBound = b₂) :
    secondConstant g family = secondConstantOfBounds N g b₁ b₂ := by
  unfold secondConstant secondConstantOfBounds Enlarged.firstWeightConstant Enlarged.secondWeightConstant
  rw [h₁, h₂]

/-- The localized reference vector is the actual product zeta_j exp(tau phi) u. -/
def localized {O : Configuration N} (family : BufferedFamily O) (R : ℝ) (hR : 0 < R)
    (τ α : ℝ) (u : Reference (Fin N × Fin 3) (fun _ => 0)) (j : ℕ) :
    Reference (Fin N × Fin 3) (fun _ => 0) :=
  PhysicalPFScalarMultiplier.multiply (fun _ => 0) (Enlarged.weightedCutoff family R hR τ α j).scalar u

/-- The full nonnegative series, with the same comparison graph at every
fractional order, including both endpoints. -/
def MixedEstimate (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    {O : Configuration N} (family : BufferedFamily O) (R : ℝ) (hR : 0 < R)
    (τ α : ℝ) (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (f : WaveSpace (Fin N × Fin 3)) (C₂ : ℝ) : Prop :=
  ∃ v : ℕ → WaveSpace (Fin N × Fin 3),
    ∃ hv : ∀ j, IsComparisonPair (fun _ => 0) (localized family R hR τ α u j) (v j),
    ∀ s : ℝ, 0 ≤ s → s ≤ 2 →
      Summable (fun j => coefficient τ (dyadicBeta α R j) (radius R j) s *
        fractionalNormSq spectral s (localized family R hR τ α u j) ⟨v j, hv j⟩) ∧
      (∑' j, coefficient τ (dyadicBeta α R j) (radius R j) s *
        fractionalNormSq spectral s (localized family R hR τ α u j) ⟨v j, hv j⟩) ≤
        ((s/2)*C₂ + (1-s/2)*40960) * ∫ X, sourceEnergy O τ α f X

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)

theorem estimate_of_energy
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (hD : HaslerHerbstDomain C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
      (profileBound F χ) (profile_bound (N := N) F χ 0) e)
    (hG : HaslerHerbstGraphNorm C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
      (profileBound F χ) (profile_bound (N := N) F χ 0) e)
    {O : Configuration N} (family : BufferedFamily O) {R τ α : ℝ} (hR : 0 < R)
    (hsmall : 4*R ≤ Real.exp (-4)) (hτ : 1 ≤ τ) (hα : 0 < α) (hαR : R ≤ Real.exp (-(4 * α + 2)))
    {u : Reference (Fin N × Fin 3) (fun _ => 0)} {f : WaveSpace (Fin N × Fin 3)}
    (hu : FreeGraph C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
      (profileBound F χ) (profile_bound (N := N) F χ 0) e u f)
    (he : EnergyEstimate F χ C e O R τ α u f) :
    MixedEstimate spectral family R hR τ α u f (secondConstant hG.bound family) := by
  classical
  unfold HaslerHerbstDomain FreeGraph at hD
  unfold HaslerHerbstGraphNorm FreeGraph at hG
  have hfree := hu
  unfold FreeGraph OperatorGraph at hfree
  let hu₀ := Classical.choose hfree
  have hf := Classical.choose_spec hfree
  let a := Enlarged.weightedCutoff family R hR τ α
  have hex := fun j => PhysicalDyadicGraph.localized_comparison_bound
    (fun _ => 0) C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
    (profileBound F χ) (profile_bound (N := N) F χ 0) e (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
    hD hG (a j) hf
  let v := fun j => Classical.choose (hex j)
  have hv := fun j => (Classical.choose_spec (hex j)).1
  refine ⟨v, hv, ?_⟩
  intro s hs hs2
  have hnonneg : ∀ j, 0 ≤ coefficient τ (dyadicBeta α R j) (radius R j) s *
      fractionalNormSq spectral s (localized family R hR τ α u j) ⟨v j, hv j⟩ := by
    intro j
    exact mul_nonneg
      (coefficient_pos (by linarith) (dyadicBeta_pos hα hR (small_two hR hsmall) j) (radius_pos hR j) s).le
      (fractionalNormSq_nonneg spectral s _ _)
  have hfinite : ∀ T : Finset ℕ,
      (∑ j ∈ T, coefficient τ (dyadicBeta α R j) (radius R j) s *
        fractionalNormSq spectral s (localized family R hR τ α u j) ⟨v j, hv j⟩) ≤
      ((s/2)*secondConstant hG.bound family + (1-s/2)*40960) *
        ∫ X, sourceEnergy O τ α f X := by
    intro T
    let Bg : ℝ := 40*(Fintype.card (Fin N × Fin 3) : ℝ)*Enlarged.firstWeightConstant family^2
    let Bl : ℝ := 640*((Fintype.card (Fin N × Fin 3) : ℝ)*Enlarged.secondWeightConstant family)^2
    have hBg : 0 ≤ Bg := by dsimp [Bg]; positivity
    have hBl : 0 ≤ Bl := by dsimp [Bl]; positivity
    have hkin : (fun X => positiveKineticWeight O τ α X * (∑ i,
        ‖externalCovariant (fun _ => 0) C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
          (profileBound F χ) (profile_bound (N := N) F χ 0) e (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
          u hu₀ i X‖ ^ 2)) = positiveKineticEnergy F χ C e O τ α u := by
      funext X
      simp only [positiveKineticEnergy, externalCovariant, roughMultiply_zero, add_zero]
    have hmI := he.mass_integrable.congr he.positive_mass_eq.symm
    have hkI := he.kinetic_integrable.congr he.positive_kinetic_eq.symm
    have hzeroI : Integrable (fun X => (640*positiveMassWeight O τ α X) *
        ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖^2) := by
      simpa only [positiveMassEnergy, mul_assoc] using hmI.const_mul 640
    have hsourceI : Integrable (fun X => (80*centeredSourceWeight O τ α X)*‖f X‖^2) := by
      simpa only [sourceEnergy, mul_assoc] using he.source_integrable.const_mul 80
    have hgradI : Integrable (fun X => (Bg*positiveKineticWeight O τ α X)*(∑ i,
        ‖externalCovariant (fun _ => 0) C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
          (profileBound F χ) (profile_bound (N := N) F χ 0) e (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
          u hu₀ i X‖ ^ 2)) := by
      simpa only [← hkin, mul_assoc] using hkI.const_mul Bg
    have hlapI : Integrable (fun X => (Bl*positiveMassWeight O τ α X)*
        ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖^2) := by
      simpa only [positiveMassEnergy, mul_assoc] using hmI.const_mul Bl
    have hzeroB : (∫ X, (640*positiveMassWeight O τ α X)*
        ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖^2) ≤
        40960*(∫ X, sourceEnergy O τ α f X) := by
      simp only [mul_assoc, integral_const_mul]
      exact (mul_le_mul_of_nonneg_left he.mass_bound (by norm_num : (0:ℝ)≤640)).trans_eq (by ring)
    have hgradB : (∫ X, (Bg*positiveKineticWeight O τ α X)*(∑ i,
        ‖externalCovariant (fun _ => 0) C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
          (profileBound F χ) (profile_bound (N := N) F χ 0) e (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
          u hu₀ i X‖ ^ 2)) ≤ (Bg*64)*(∫ X, sourceEnergy O τ α f X) := by
      simp only [mul_assoc, integral_const_mul]
      rw [hkin]
      exact (mul_le_mul_of_nonneg_left he.kinetic_bound hBg).trans_eq (by ring)
    have hlapB : (∫ X, (Bl*positiveMassWeight O τ α X)*
        ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖^2) ≤
        (Bl*64)*(∫ X, sourceEnergy O τ α f X) := by
      simp only [mul_assoc, integral_const_mul]
      exact (mul_le_mul_of_nonneg_left he.mass_bound hBl).trans_eq (by ring)
    have hzeroRaw := (PhysicalDyadicGraph.multiplier_norm_sum_bound T a
      (fun j => coefficient τ (dyadicBeta α R j) (radius R j) 0)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u)
      (fun X => 640 * positiveMassWeight O τ α X)
      (Enlarged.weighted_zero_sum family hR hsmall hτ hα hαR T) hzeroI).trans hzeroB
    have hzero : (∑ j ∈ T, coefficient τ (dyadicBeta α R j) (radius R j) 0 *
        ‖inclusion (Fin N × Fin 3) (fun _ => 0)
          (localized family R hR τ α u j)‖^2) ≤
        40960 * ∫ X, sourceEnergy O τ α f X := by
      simpa only [localized, a, PhysicalPFScalarMultiplier.value_multiply] using hzeroRaw
    have hgraphSum := PhysicalDyadicGraph.localized_comparison_integral_sum_fixed
      (fun _ => 0) C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
      (profileBound F χ) (profile_bound (N := N) F χ 0) e
      (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
      T (fun j => coefficient τ (dyadicBeta α R j) (radius R j) 2)
      (fun j _ => (coefficient_pos (by linarith)
        (dyadicBeta_pos hα hR (small_two hR hsmall) j) (radius_pos hR j) 2).le)
      hG a hf v hv
      (fun X => 80 * centeredSourceWeight O τ α X)
      (fun X => 640 * positiveMassWeight O τ α X)
      (fun X => Bg * positiveKineticWeight O τ α X)
      (fun X => Bl * positiveMassWeight O τ α X)
      (Enlarged.weighted_source_sum family hR hsmall hτ hα T)
      (Enlarged.weighted_mass_sum family hR hsmall hτ hα hαR T)
      (Enlarged.weighted_gradient_sum family hR hsmall hτ hα hαR T)
      (Enlarged.weighted_laplacian_sum family hR hsmall hτ hα hαR T)
      hsourceI hzeroI hgradI hlapI
    have hsourceB : (∫ X, (80 * centeredSourceWeight O τ α X) * ‖f X‖^2) ≤
        80 * ∫ X, sourceEnergy O τ α f X := by
      simp only [mul_assoc, integral_const_mul]
      exact le_rfl
    have hsecond : (∑ j ∈ T, coefficient τ (dyadicBeta α R j) (radius R j) 2 * ‖v j‖^2) ≤
        secondConstant hG.bound family * ∫ X, sourceEnergy O τ α f X := by
      apply hgraphSum.trans
      have hb := add_le_add (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hsourceB (by norm_num : (0 : ℝ) ≤ 2))
          (mul_le_mul_of_nonneg_left hgradB (by norm_num : (0 : ℝ) ≤ 4))) hlapB) hzeroB
      exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * hG.bound^2)).trans_eq
        (by dsimp [secondConstant, Bg, Bl]; ring)
    exact comparison_fractional_sum_normSq spectral T
      (localized family R hR τ α u) v hv (dyadicBeta α R) (radius R)
      (by linarith) hs hs2 (fun j _ => dyadicBeta_pos hα hR (small_two hR hsmall) j)
      (fun j _ => radius_pos hR j) hzero hsecond
  exact ⟨summable_of_sum_le hnonneg hfinite, Real.tsum_le_of_sum_le hnonneg hfinite⟩

attribute [local irreducible] MixedEstimate

open PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.SphereCoreGeometry
  PfHk.OrdinaryPolarSobolevChart PfHk.PhysicalCarlemanInput

/-- One enlarged smooth annular family at every center, with one radius threshold,
one parameter threshold and one second-order constant for all centers
and every smaller ball. No dyadic endpoint or weighted estimate is an input. -/
theorem exists_uniform_estimate (hUV : CarlemanUV χ)
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
    (hG : HaslerHerbstGraphNorm C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
      (profileBound F χ) (profile_bound (N := N) F χ 0) e)
    (α : ℝ) (hα : 0 < α) :
    ∃ family : ∀ O : Configuration N, BufferedFamily O,
    ∃ r₀ τ₀ C₂ : ℝ, 0 < r₀ ∧ r₀ < Real.exp (-2) ∧ 1 ≤ τ₀ ∧ 0 ≤ C₂ ∧
      ∀ τ : ℝ, τ₀ ≤ τ → ∀ (O : Configuration N) (R : ℝ) (hR : 0 < R), R ≤ r₀ →
      ∀ (u : Reference (Fin N × Fin 3) (fun _ => 0)) (f : WaveSpace (Fin N × Fin 3)),
      FreeGraph C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
        (profileBound F χ) (profile_bound (N := N) F χ 0) e u f →
      AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R →
      MixedEstimate spectral (family O) R hR τ α u f C₂ := by
  classical
  have hexFamily := exists_uniform_buffered_family (I := Fin N × Fin 3)
  let B₁ := Classical.choose hexFamily
  let B₂ := Classical.choose (Classical.choose_spec hexFamily)
  have hfamily := (Classical.choose_spec (Classical.choose_spec hexFamily)).2.2
  let family : ∀ O : Configuration N, BufferedFamily O :=
    fun O => Classical.choose (hfamily O)
  have hfirst (O : Configuration N) : (family O).firstBound = B₁ :=
    (Classical.choose_spec (hfamily O)).1
  have hsecond (O : Configuration N) : (family O).secondBound = B₂ :=
    (Classical.choose_spec (hfamily O)).2
  have hexEnergy := exists_uniform_energy_estimate F χ C e hUV W B P G S L hN D A α hα
  let rE := Classical.choose hexEnergy
  let τ₀ := Classical.choose (Classical.choose_spec hexEnergy)
  have henergyData := Classical.choose_spec (Classical.choose_spec hexEnergy)
  have hrE := henergyData.1
  have hsmallE := henergyData.2.1
  have hτ₀ := henergyData.2.2.1
  have henergy := henergyData.2.2.2
  -- The radius is also taken below the exponent threshold of the annular
  -- comparison of `β`.
  let r₀ := min rE (min (Real.exp (-4)/4) (Real.exp (-(4 * α + 2))))
  have hr₀ : 0 < r₀ := lt_min hrE (lt_min (by positivity) (Real.exp_pos _))
  have hsmall : r₀ < Real.exp (-2) :=
    (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by
      have he : Real.exp (-4) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by norm_num)
      linarith [Real.exp_pos (-4)]))
  let C₂ := secondConstantOfBounds N hG.bound B₁ B₂
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂, secondConstantOfBounds]; positivity
  have hconstant (O : Configuration N) : secondConstant hG.bound (family O) = C₂ :=
    secondConstant_eq_bounds hG.bound (family O) B₁ B₂ (hfirst O) (hsecond O)
  refine ⟨family, r₀, τ₀, C₂, hr₀, hsmall, hτ₀, hC₂, ?_⟩
  intro τ hτ O R hR hRsmall u f hu hsupp
  rw [← hconstant O]
  exact estimate_of_energy F χ C e spectral hD hG (family O) hR
    (by have h := (hRsmall.trans (min_le_right _ _)).trans (min_le_left _ _); linarith)
    (hτ₀.trans hτ) hα ((hRsmall.trans (min_le_right _ _)).trans (min_le_right _ _)) hu
    (henergy τ hτ O R hR (hRsmall.trans (min_le_left _ _)) u f hu hsupp)

end PfHk.PhysicalEnlargedFractionalCarleman
