import GptLean.PhysicalFockFormPullback
import GptLean.PhysicalFockKernelField

/-!
Actual retained field outputs on the physical localization channel.
The annihilation form identity proves summability of the output sector
coordinates. The sector CCR then proves creation summability and its
exact mass correction. No radiation-domain preservation of an arbitrary
one-photon split is assumed.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationFockChannel
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false

private def squareSummableVector {K : ℕ → Type*} [∀ n, NormedAddCommGroup (K n)]
    (v : ∀ n, K n) (h : (∑' n, ENNReal.ofReal (‖v n‖ ^ 2)) < ⊤) : Space K := by
  have hs : Summable (fun n => ‖v n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal h.ne
  exact ⟨v, memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs)⟩

private theorem squareSummableVector_mass {K : ℕ → Type*} [∀ n, NormedAddCommGroup (K n)]
    (v : ∀ n, K n) (h : (∑' n, ENNReal.ofReal (‖v n‖ ^ 2)) < ⊤) :
    ENNReal.ofReal (‖squareSummableVector v h‖ ^ 2) =
      ∑' n, ENNReal.ofReal (‖v n‖ ^ 2) := by
  have he (n : ℕ) : squareSummableVector v h n = v n := rfl
  simpa only [weightedForm, one_mul, he] using (massForm_eq K (squareSummableVector v h)).symm

section Generic
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

def annihilationOnDomain (f : Lp ℂ 2 μ) (u : Fock μ)
    (hu : annihilationForm μ f u < ⊤) : Fock μ :=
  squareSummableVector (fun n => annihilationSector μ n f (u (n + 1))) hu

theorem annihilationOnDomain_mass (f : Lp ℂ 2 μ) (u : Fock μ)
    (hu : annihilationForm μ f u < ⊤) :
    ENNReal.ofReal (‖annihilationOnDomain μ f u hu‖ ^ 2) = annihilationForm μ f u :=
  squareSummableVector_mass _ hu

def creationOnDomain (C : CanonicalSectorCCR μ) (f : Lp ℂ 2 μ) (u : Fock μ)
    (hu : annihilationForm μ f u < ⊤) : Fock μ :=
  squareSummableVector (creationCoordinates μ f u) (by
    rw [creationCoordinates_tsum μ C]
    exact ENNReal.add_lt_top.mpr ⟨hu, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩)

theorem creationOnDomain_mass (C : CanonicalSectorCCR μ) (f : Lp ℂ 2 μ) (u : Fock μ)
    (hu : annihilationForm μ f u < ⊤) :
    ENNReal.ofReal (‖creationOnDomain μ C f u hu‖ ^ 2) =
      annihilationForm μ f u + ENNReal.ofReal (‖f‖ ^ 2) * ENNReal.ofReal (‖u‖ ^ 2) :=
  (squareSummableVector_mass _ _).trans (creationCoordinates_tsum μ C f u)

def profileAnnihilationOutput (f : Lp ℂ 2 μ) (v : Space (fun _ : ℕ => Fock μ))
    (hv : (∑' a, annihilationForm μ f (v a)) < ⊤) : Space (fun _ : ℕ => Fock μ) :=
  squareSummableVector (fun a => annihilationOnDomain μ f (v a) ((ENNReal.le_tsum a).trans_lt hv)) (by
    simpa only [annihilationOnDomain_mass] using hv)

theorem profileAnnihilationOutput_mass (f : Lp ℂ 2 μ) (v : Space (fun _ : ℕ => Fock μ))
    (hv : (∑' a, annihilationForm μ f (v a)) < ⊤) :
    ENNReal.ofReal (‖profileAnnihilationOutput μ f v hv‖ ^ 2) =
      ∑' a, annihilationForm μ f (v a) :=
  (squareSummableVector_mass _ _).trans (tsum_congr fun _ => annihilationOnDomain_mass μ _ _ _)

theorem profileCreation_mass_sum (C : CanonicalSectorCCR μ) (f : Lp ℂ 2 μ)
    (v : Space (fun _ : ℕ => Fock μ)) (hv : (∑' a, annihilationForm μ f (v a)) < ⊤) :
    (∑' a, ENNReal.ofReal (‖creationOnDomain μ C f (v a) ((ENNReal.le_tsum a).trans_lt hv)‖ ^ 2)) =
      (∑' a, annihilationForm μ f (v a)) + ENNReal.ofReal (‖f‖ ^ 2) * ENNReal.ofReal (‖v‖ ^ 2) := by
  simp_rw [creationOnDomain_mass]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
  have hm := massForm_eq (fun _ : ℕ => Fock μ) v
  simpa only [weightedForm, one_mul] using congrArg
    (fun s => (∑' a, annihilationForm μ f (v a)) + ENNReal.ofReal (‖f‖ ^ 2) * s) hm

def profileCreationOutput (C : CanonicalSectorCCR μ) (f : Lp ℂ 2 μ)
    (v : Space (fun _ : ℕ => Fock μ)) (hv : (∑' a, annihilationForm μ f (v a)) < ⊤) :
    Space (fun _ : ℕ => Fock μ) :=
  squareSummableVector (fun a => creationOnDomain μ C f (v a) ((ENNReal.le_tsum a).trans_lt hv)) (by
    rw [profileCreation_mass_sum μ C f v hv]
    exact ENNReal.add_lt_top.mpr ⟨hv, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩)

theorem profileCreationOutput_mass (C : CanonicalSectorCCR μ) (f : Lp ℂ 2 μ)
    (v : Space (fun _ : ℕ => Fock μ)) (hv : (∑' a, annihilationForm μ f (v a)) < ⊤) :
    ENNReal.ofReal (‖profileCreationOutput μ C f v hv‖ ^ 2) =
      (∑' a, annihilationForm μ f (v a)) + ENNReal.ofReal (‖f‖ ^ 2) * ENNReal.ofReal (‖v‖ ^ 2) :=
  (squareSummableVector_mass _ _).trans (profileCreation_mass_sum μ C f v hv)

end Generic

variable (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
  (f : Lp ℂ 2 photonMeasure) (k : WeightedPhotonKernel)
  (hk : (retainedMap j).adjoint f = k.val.1)

include C hk in
theorem channelAnnihilation_finite (u : RadiationGraphSpace) :
    (∑' a, annihilationForm photonMeasure f
      ((photonFactorization BF).factor j (radiationGraphInclusion u) a)) < ⊤ := by
  rw [photonFactorization_annihilationForm BF C, hk]
  exact (annihilation_sector_tsum_bound k.val.1 k.val.2 k.property
    (radiationGraphInclusion u) (radiationGraph_finite u)).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (radiationGraph_finite u))

def channelAnnihilationOutput (u : RadiationGraphSpace) : Space (fun _ : ℕ => PhotonFock) :=
  profileAnnihilationOutput photonMeasure f ((photonFactorization BF).factor j (radiationGraphInclusion u))
    (channelAnnihilation_finite BF C j f k hk u)

def channelCreationOutput (u : RadiationGraphSpace) : Space (fun _ : ℕ => PhotonFock) :=
  profileCreationOutput photonMeasure C f ((photonFactorization BF).factor j (radiationGraphInclusion u))
    (channelAnnihilation_finite BF C j f k hk u)

theorem channelAnnihilationOutput_mass (u : RadiationGraphSpace) :
    ENNReal.ofReal (‖channelAnnihilationOutput BF C j f k hk u‖ ^ 2) =
      annihilationForm photonMeasure k.val.1 (radiationGraphInclusion u) := by
  rw [channelAnnihilationOutput, profileAnnihilationOutput_mass,
    photonFactorization_annihilationForm BF C, hk]

set_option backward.isDefEq.respectTransparency.types true in
theorem channelCreationOutput_mass (u : RadiationGraphSpace) :
    ENNReal.ofReal (‖channelCreationOutput BF C j f k hk u‖ ^ 2) =
      annihilationForm photonMeasure k.val.1 (radiationGraphInclusion u) +
        ENNReal.ofReal (‖f‖ ^ 2) * ENNReal.ofReal (‖radiationGraphInclusion u‖ ^ 2) := by
  have h := profileCreationOutput_mass photonMeasure C f
    ((photonFactorization BF).factor j (radiationGraphInclusion u))
    (channelAnnihilation_finite BF C j f k hk u)
  have hn : ‖(photonFactorization BF).factor j (radiationGraphInclusion u)‖ =
      ‖radiationGraphInclusion u‖ := ((photonFactorization BF).factor j).norm_map _
  have ha : (∑' a, annihilationForm photonMeasure f
      ((photonFactorization BF).factor j (radiationGraphInclusion u) a)) =
      annihilationForm photonMeasure k.val.1 (radiationGraphInclusion u) :=
    (photonFactorization_annihilationForm BF C j f (radiationGraphInclusion u)).trans
      (congrArg (fun g => annihilationForm photonMeasure g (radiationGraphInclusion u)) hk)
  exact h.trans (congrArg₂ (fun a b : ENNReal => a + ENNReal.ofReal (‖f‖ ^ 2) * b)
    ha (congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) hn))

theorem channelAnnihilationOutput_norm_le (u : RadiationGraphSpace) :
    ‖channelAnnihilationOutput BF C j f k hk u‖ ≤ ‖k.val.2‖ * ‖radiationGraphDerivative u‖ := by
  have h := annihilation_sector_tsum_bound k.val.1 k.val.2 k.property
    (radiationGraphInclusion u) (radiationGraph_finite u)
  change annihilationForm photonMeasure k.val.1 (radiationGraphInclusion u) ≤
    ENNReal.ofReal (‖k.val.2‖ ^ 2) * radiationForm (radiationGraphInclusion u) at h
  rw [← channelAnnihilationOutput_mass BF C j f k hk, radiationGraph_energy,
    ← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow] at h
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    ((ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp h)

theorem channelCreationOutput_norm_le (u : RadiationGraphSpace) :
    ‖channelCreationOutput BF C j f k hk u‖ ≤
      ‖k.val.2‖ * ‖radiationGraphDerivative u‖ + ‖f‖ * ‖radiationGraphInclusion u‖ := by
  have he := channelCreationOutput_mass BF C j f k hk u
  rw [← channelAnnihilationOutput_mass BF C j f k hk,
    ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))] at he
  have hs := (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (by positivity)).mp he
  have ha := pow_le_pow_left₀ (norm_nonneg _)
    (channelAnnihilationOutput_norm_le BF C j f k hk u) 2
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hp : 0 ≤ (‖k.val.2‖ * ‖radiationGraphDerivative u‖) *
      (‖f‖ * ‖radiationGraphInclusion u‖) := by positivity
  nlinarith only [hs, ha, hp]

private def doubleCoordinateMap {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    {K : ℕ → Type*} [∀ n, NormedAddCommGroup (K n)] [∀ n, NormedSpace ℂ (K n)]
    (v : Q → Space (fun _ : ℕ => Space K)) (A : ∀ _a n : ℕ, Q →L[ℂ] K n)
    (hA : ∀ q a n, v q a n = A a n q) (M : ℝ) (hM : ∀ q, ‖v q‖ ≤ M * ‖q‖) :
    Q →L[ℂ] Space (fun _ : ℕ => Space K) :=
  LinearMap.mkContinuous
    { toFun := v
      map_add' q r := by
        apply lp.ext
        funext a
        apply lp.ext
        funext n
        change v (q + r) a n = v q a n + v r a n
        rw [hA, hA, hA, map_add]
      map_smul' c q := by
        apply lp.ext
        funext a
        apply lp.ext
        funext n
        change v (c • q) a n = c • v q a n
        rw [hA, hA, map_smul] }
    M hM

private def channelInputCoordinate (a n : ℕ) : RadiationGraphSpace →L[ℂ] Sector photonMeasure n :=
  (lp.evalCLM ℂ (Sector photonMeasure) 2 n).comp
    ((lp.evalCLM ℂ (fun _ : ℕ => PhotonFock) 2 a).comp
      (((photonFactorization BF).factor j).toContinuousLinearMap.comp radiationGraphInclusion))

/-- Retained annihilation is an actual continuous map on the source radiation graph. -/
def channelAnnihilation : RadiationGraphSpace →L[ℂ] Space (fun _ : ℕ => PhotonFock) :=
  doubleCoordinateMap (channelAnnihilationOutput BF C j f k hk)
    (fun a n => (annihilationSector photonMeasure n f).comp (channelInputCoordinate BF j a (n + 1)))
    (fun _ _ _ => rfl) (‖k.val.2‖ * ‖radiationGraphDerivative‖)
    (fun q => (channelAnnihilationOutput_norm_le BF C j f k hk q).trans (by
      nlinarith only [radiationGraphDerivative.le_opNorm q, norm_nonneg k.val.2]))

private def channelCreationCoordinate (a : ℕ) : (n : ℕ) → RadiationGraphSpace →L[ℂ] Sector photonMeasure n
  | 0 => 0
  | n + 1 => (creationSector photonMeasure n f).comp (channelInputCoordinate BF j a n)

/-- Retained creation is obtained from its sector coordinates and the proved CCR norm identity. -/
def channelCreation : RadiationGraphSpace →L[ℂ] Space (fun _ : ℕ => PhotonFock) :=
  doubleCoordinateMap (channelCreationOutput BF C j f k hk) (channelCreationCoordinate BF j f)
    (fun _ _ n => by cases n <;> rfl)
    (‖k.val.2‖ * ‖radiationGraphDerivative‖ + ‖f‖ * ‖radiationGraphInclusion‖)
    (fun q => (channelCreationOutput_norm_le BF C j f k hk q).trans (by
      nlinarith only [radiationGraphDerivative.le_opNorm q, radiationGraphInclusion.le_opNorm q,
        norm_nonneg k.val.2, norm_nonneg f]))

def channelField : RadiationGraphSpace →L[ℂ] Space (fun _ : ℕ => PhotonFock) :=
  channelAnnihilation BF C j f k hk + channelCreation BF C j f k hk

theorem channelField_norm_le (u : RadiationGraphSpace) :
    ‖channelField BF C j f k hk u‖ ≤
      2 * ‖k.val.2‖ * ‖radiationGraphDerivative u‖ + ‖f‖ * ‖radiationGraphInclusion u‖ := by
  have ha := channelAnnihilationOutput_norm_le BF C j f k hk u
  have hc := channelCreationOutput_norm_le BF C j f k hk u
  have ht := norm_add_le (channelAnnihilation BF C j f k hk u) (channelCreation BF C j f k hk u)
  change ‖channelField BF C j f k hk u‖ ≤ _ at ht
  change ‖channelAnnihilation BF C j f k hk u‖ ≤ _ at ha
  change ‖channelCreation BF C j f k hk u‖ ≤ _ at hc
  linarith

/-- On an actual radiation graph output, the constructed coordinate is
the ordinary physical annihilation operator on that output. -/
theorem channelAnnihilation_output (g : WeightedPhotonKernel) (hg : g.val.1 = f)
    (u v : RadiationGraphSpace) (a : ℕ)
    (hv : radiationGraphInclusion v = (photonFactorization BF).factor j (radiationGraphInclusion u) a) :
    kernelAnnihilation g v = channelAnnihilation BF C j f k hk u a := by
  apply lp.ext
  funext n
  change annihilationSector photonMeasure n g.val.1 (radiationGraphInclusion v (n + 1)) =
    annihilationSector photonMeasure n f
      ((photonFactorization BF).factor j (radiationGraphInclusion u) a (n + 1))
  rw [hg, hv]

theorem channelCreation_output (g : WeightedPhotonKernel) (hg : g.val.1 = f)
    (u v : RadiationGraphSpace) (a : ℕ)
    (hv : radiationGraphInclusion v = (photonFactorization BF).factor j (radiationGraphInclusion u) a) :
    kernelCreation C g v = channelCreation BF C j f k hk u a := by
  apply lp.ext
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    change creationSector photonMeasure n g.val.1 (radiationGraphInclusion v n) =
      creationSector photonMeasure n f
        ((photonFactorization BF).factor j (radiationGraphInclusion u) a n)
    rw [hg, hv]

theorem channelField_output (g : WeightedPhotonKernel) (hg : g.val.1 = f)
    (u v : RadiationGraphSpace) (a : ℕ)
    (hv : radiationGraphInclusion v = (photonFactorization BF).factor j (radiationGraphInclusion u) a) :
    kernelField C g v = channelField BF C j f k hk u a := by
  change kernelAnnihilation g v + kernelCreation C g v =
    channelAnnihilation BF C j f k hk u a + channelCreation BF C j f k hk u a
  exact congrArg₂ (fun s t : PhotonFock => s + t)
    (channelAnnihilation_output BF C j f k hk g hg u v a hv)
    (channelCreation_output BF C j f k hk g hg u v a hv)

end GptLean.PhysicalFock
