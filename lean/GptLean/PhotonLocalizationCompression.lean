import GptLean.PhotonLocalizationTrace
import GptLean.PhotonLocalizationKernelModel
import GptLean.PhotonLocalizationDensity

/-!
Construct the trace compressions used by local photon compactness.

The input operators are the photon-number projection, electronic cutoff,
and compact-resolvent spectral projection. Their positive functional
expectations identify the three tails. The compression itself, its finite
dimensional space, its norm bound and its approximation estimate are all
derived. Physical Fock and localized form identifications remain separate.
-/

namespace GptLean.PhotonTrace

open Filter Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The actual compressed functionals belong to the finite-dimensional
dual of the operator corner, embedded by precomposition. -/
theorem exists_compression_space {S : A} (hS : IsFiniteRankProj S) :
    ∃ V : Submodule ℝ (A →L[ℂ] ℂ), FiniteDimensional ℝ V ∧
      ∀ φ : A →L[ℂ] ℂ, compr S φ ∈ V := by
  let W := LinearMap.range (comprMap S).toLinearMap
  let c : A →L[ℂ] W := (comprMap S).codRestrict W
    (fun x => LinearMap.mem_range_self _ x)
  let f : (W →L[ℂ] ℂ) →L[ℝ] (A →L[ℂ] ℂ) :=
    (ContinuousLinearMap.precomp ℂ c).restrictScalars ℝ
  have : FiniteDimensional ℂ W := hS.finiteDimensional
  have : FiniteDimensional ℝ (W →L[ℂ] ℂ) :=
    Module.Finite.trans ℂ (W →L[ℂ] ℂ)
  refine ⟨f.toLinearMap.range, inferInstance, ?_⟩
  intro φ
  exact ⟨φ.comp W.subtypeL, rfl⟩

/-- Compression preserves positivity and cannot increase the mass. -/
theorem compression_norm_le_one {φ : A →L[ℂ] ℂ}
    (hφ : IsPosFunctional φ) (hmass : (φ 1).re ≤ 1)
    {S : A} (hS : IsStarProjection S) : ‖compr S φ‖ ≤ 1 := by
  apply (hφ.compr hS.isSelfAdjoint).opNorm_le.trans
  simp only [compr_apply, mul_one, hS.isIdempotentElem.eq]
  have h := hφ.proj_re_nonneg hS.one_sub
  rw [map_sub, Complex.sub_re] at h
  linarith

/-- The combined cutoff and spectral residual yields the three-tail
trace-norm estimate with its explicit constants. -/
theorem compression_three_tail {φ : A →L[ℂ] ℂ}
    (hφ : IsPosFunctional φ) (hmass : (φ 1).re ≤ 1)
    {P ζ S : A} (hP : IsStarProjection P) (hζ : IsSelfAdjoint ζ)
    (hcomm : Commute ζ P) (hS : IsStarProjection S) :
    dist φ (compr S φ) ≤ 2 * Real.sqrt
      (2 * (φ (1 - P)).re + 2 * (φ ((1 - ζ) ^ 2)).re +
        2 * (φ (star (ζ * P) * (1 - S) * (ζ * P))).re) := by
  rw [dist_eq_norm]
  apply (hφ.norm_sub_compr_le_of_le_one hmass hS).trans
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
  have hsplit := hφ.one_sub_proj_re_le hS (ζ * P)
  have hcut := hφ.one_sub_cutoff_re_le hP hζ hcomm
  linarith

/-- Construct the existing compactness witness from actual operator
cutoffs. No compressed states, finite-dimensional trace spaces, gentle
estimate or norm bound are supplied as inputs. -/
noncomputable def compressionWitness
    (φ : ℕ → A →L[ℂ] ℂ)
    (hφ : ∀ n, IsPosFunctional (φ n)) (hmass : ∀ n, (φ n 1).re ≤ 1)
    (P ζ : ℕ → A) (S : ℕ → ℕ → ℕ → A)
    (hP : ∀ M, IsStarProjection (P M))
    (hζ : ∀ L, IsSelfAdjoint (ζ L))
    (hcomm : ∀ L M, Commute (ζ L) (P M))
    (hS : ∀ L M s, IsFiniteRankProj (S L M s))
    (Cnum : ℝ) (electronicError energy : ℕ → ℝ)
    (hnum : ∀ M n, (φ n (1 - P M)).re ≤ Cnum / (M + 1))
    (hel : ∀ L n, (φ n ((1 - ζ L) ^ 2)).re ≤ electronicError L)
    (hspec : ∀ L M s n,
      (φ n (star (ζ L * P M) * (1 - S L M s) * (ζ L * P M))).re ≤
        energy L / (s + 1))
    (htight : Tendsto electronicError atTop (𝓝 0)) :
    PhotonLocalization.CompressionWitness (A →L[ℂ] ℂ) φ := by
  choose spaces hfinite hmem using fun L M s => exists_compression_space (hS L M s)
  exact {
    spaces := spaces
    finite := hfinite
    compress := fun L M s n => compr (S L M s) (φ n)
    mem := fun L M s n => hmem L M s (φ n)
    norm_le := fun L M s n => compression_norm_le_one (hφ n) (hmass n)
      (hS L M s).isStarProjection
    numberTail := fun M n => (φ n (1 - P M)).re
    electronicTail := fun L n => (φ n ((1 - ζ L) ^ 2)).re
    spectralTail := fun L M s n =>
      (φ n (star (ζ L * P M) * (1 - S L M s) * (ζ L * P M))).re
    compression := fun L M s n => compression_three_tail (hφ n) (hmass n)
      (hP M) (hζ L) (hcomm L M) (hS L M s).isStarProjection
    Cnum := Cnum
    electronicError := electronicError
    energy := energy
    number_le := hnum
    electronic_le := hel
    spectral_le := hspec
    electronic_zero := htight }

/-- Local trace precompactness from number, spatial and spectral cutoffs.
The target compactness assertion is a conclusion of the constructor. -/
theorem totallyBounded_of_operator_cutoffs
    (φ : ℕ → A →L[ℂ] ℂ)
    (hφ : ∀ n, IsPosFunctional (φ n)) (hmass : ∀ n, (φ n 1).re ≤ 1)
    (P ζ : ℕ → A) (S : ℕ → ℕ → ℕ → A)
    (hP : ∀ M, IsStarProjection (P M))
    (hζ : ∀ L, IsSelfAdjoint (ζ L))
    (hcomm : ∀ L M, Commute (ζ L) (P M))
    (hS : ∀ L M s, IsFiniteRankProj (S L M s))
    (Cnum : ℝ) (electronicError energy : ℕ → ℝ)
    (hnum : ∀ M n, (φ n (1 - P M)).re ≤ Cnum / (M + 1))
    (hel : ∀ L n, (φ n ((1 - ζ L) ^ 2)).re ≤ electronicError L)
    (hspec : ∀ L M s n,
      (φ n (star (ζ L * P M) * (1 - S L M s) * (ζ L * P M))).re ≤
        energy L / (s + 1))
    (htight : Tendsto electronicError atTop (𝓝 0)) :
    TotallyBounded (Set.range φ) :=
  (compressionWitness φ hφ hmass P ζ S hP hζ hcomm hS Cnum electronicError
    energy hnum hel hspec htight).totallyBounded

/-- Actual L¹ density tails supply the electronic scalar error. The
electronic cutoff expectation is bounded by the one-particle spatial
tail, as follows from its multiplication-operator evaluation. -/
noncomputable def compressionWitness_of_density
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    (region : ℕ → Set Ω) (ρ : ℕ → MeasureTheory.Lp ℝ 1 μ)
    {mass : ℝ} (hρmass : ∀ n, ‖ρ n‖ ≤ mass)
    (htight : PhotonLocalization.DensityTight region ρ)
    (φ : ℕ → A →L[ℂ] ℂ)
    (hφ : ∀ n, IsPosFunctional (φ n)) (hmass : ∀ n, (φ n 1).re ≤ 1)
    (P ζ : ℕ → A) (S : ℕ → ℕ → ℕ → A)
    (hP : ∀ M, IsStarProjection (P M))
    (hζ : ∀ L, IsSelfAdjoint (ζ L))
    (hcomm : ∀ L M, Commute (ζ L) (P M))
    (hS : ∀ L M s, IsFiniteRankProj (S L M s))
    (Cnum : ℝ) (energy : ℕ → ℝ)
    (hnum : ∀ M n, (φ n (1 - P M)).re ≤ Cnum / (M + 1))
    (hel : ∀ L n, (φ n ((1 - ζ L) ^ 2)).re ≤
      PhotonLocalization.densityTail region L (ρ n))
    (hspec : ∀ L M s n,
      (φ n (star (ζ L * P M) * (1 - S L M s) * (ζ L * P M))).re ≤
        energy L / (s + 1)) :
    PhotonLocalization.CompressionWitness (A →L[ℂ] ℂ) φ :=
  compressionWitness φ hφ hmass P ζ S hP hζ hcomm hS Cnum
    (PhotonLocalization.densityTailError region ρ) energy hnum
    (fun L n => (hel L n).trans
      (PhotonLocalization.densityTail_le_error_of_norm_bound region hρmass L n))
    hspec (PhotonLocalization.densityTailError_tendsto_zero_of_tight region hρmass htight)

end GptLean.PhotonTrace
