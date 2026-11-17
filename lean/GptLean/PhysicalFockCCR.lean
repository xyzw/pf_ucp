import GptLean.PhysicalFockRadiationField

/-!
The universal CCR boundary for the constructed symmetric tensor model.

The only background below is the diagonal sector CCR identity for the
actual insertion operators and their actual Hilbert adjoints. It is
stated for an arbitrary sigma-finite one-particle measure and all kernels
and vectors. No cutoff, localization error or chosen field bound occurs.
Given this universal identity, full creation on the radiation graph and
its norm identity are constructed by summing the actual sectors.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

/-- Standard bosonic CCR for the fixed normalized symmetric insertion. -/
structure CanonicalSectorCCR {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] : Prop where
  vacuum : ∀ (f : Lp ℂ 2 μ) (u : Sector μ 0),
    ‖creationSector μ 0 f u‖ ^ 2 = ‖f‖ ^ 2 * ‖u‖ ^ 2
  successor : ∀ (f : Lp ℂ 2 μ) (n : ℕ) (u : Sector μ (n + 1)),
    ‖creationSector μ (n + 1) f u‖ ^ 2 =
      ‖annihilationSector μ n f u‖ ^ 2 + ‖f‖ ^ 2 * ‖u‖ ^ 2

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

def creationCoordinates (f : Lp ℂ 2 μ) (u : Fock μ) : (n : ℕ) → Sector μ n
  | 0 => 0
  | n + 1 => creationSector μ n f (u n)

theorem creationCoordinates_tsum (C : CanonicalSectorCCR μ) (f : Lp ℂ 2 μ) (u : Fock μ) :
    (∑' n, ENNReal.ofReal (‖creationCoordinates μ f u n‖ ^ 2)) =
      (∑' n, ENNReal.ofReal (‖annihilationSector μ n f (u (n + 1))‖ ^ 2)) +
        ENNReal.ofReal (‖f‖ ^ 2) * ENNReal.ofReal (‖u‖ ^ 2) := by
  have hm : (∑' n, ENNReal.ofReal (‖u n‖ ^ 2)) = ENNReal.ofReal (‖u‖ ^ 2) := by
    simpa only [weightedForm, one_mul] using massForm_eq (Sector μ) u
  rw [← hm]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [creationCoordinates, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, ENNReal.ofReal_zero, zero_add]
  rw [tsum_eq_zero_add' ENNReal.summable (f := fun n =>
    ENNReal.ofReal (‖creationSector μ n f (u n)‖ ^ 2))]
  simp_rw [C.vacuum, C.successor,
    ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    ENNReal.ofReal_mul (sq_nonneg _)]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left,
    tsum_eq_zero_add' ENNReal.summable (f := fun n => ENNReal.ofReal (‖u n‖ ^ 2)), mul_add]
  exact add_left_comm _ _ _

end Generic

variable (C : CanonicalSectorCCR photonMeasure)

def creationGraphOutput (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (q : RadiationGraphSpace) : PhotonFock := by
  let c := creationCoordinates photonMeasure f (radiationGraphInclusion q)
  have ht : (∑' n, ENNReal.ofReal (‖c n‖ ^ 2)) ≠ ⊤ := by
    rw [creationCoordinates_tsum photonMeasure C]
    apply ENNReal.add_ne_top.mpr
    refine ⟨?_, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
    exact ((annihilation_sector_tsum_bound f g hfg (radiationGraphInclusion q)
      (radiationGraph_finite q)).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (radiationGraph_finite q))).ne
  have hs : Summable (fun n => ‖c n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal ht
  exact ⟨c, memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs)⟩

@[simp] theorem creationGraphOutput_coordinate (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (q : RadiationGraphSpace) (n : ℕ) :
    creationGraphOutput C f g hfg q n =
      creationCoordinates photonMeasure f (radiationGraphInclusion q) n := rfl

theorem creationGraphOutput_norm_sq (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (q : RadiationGraphSpace) :
    ‖creationGraphOutput C f g hfg q‖ ^ 2 =
      ‖annihilationRadiation f g hfg q‖ ^ 2 + ‖f‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 := by
  have hm (u : PhotonFock) : (∑' n, ENNReal.ofReal (‖u n‖ ^ 2)) =
      ENNReal.ofReal (‖u‖ ^ 2) := by
    simpa only [weightedForm, one_mul] using massForm_eq (Sector photonMeasure) u
  have h := creationCoordinates_tsum photonMeasure C f (radiationGraphInclusion q)
  change (∑' n, ENNReal.ofReal (‖creationGraphOutput C f g hfg q n‖ ^ 2)) =
    (∑' n, ENNReal.ofReal (‖annihilationRadiation f g hfg q n‖ ^ 2)) + _ at h
  rw [hm, hm, ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (by positivity)).mp h

theorem creationGraphOutput_norm_le (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (q : RadiationGraphSpace) :
    ‖creationGraphOutput C f g hfg q‖ ≤
      ‖g‖ * ‖radiationGraphDerivative q‖ + ‖f‖ * ‖radiationGraphInclusion q‖ := by
  have ha := annihilationRadiation_norm_le f g hfg q
  have hs := creationGraphOutput_norm_sq C f g hfg q
  have ha2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hp : 0 ≤ (‖g‖ * ‖radiationGraphDerivative q‖) *
      (‖f‖ * ‖radiationGraphInclusion q‖) := by positivity
  nlinarith only [hs, ha2, hp]

/-- Full creation uses exactly the preceding normalized sector operators. -/
def creationRadiation (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p) :
    RadiationGraphSpace →L[ℂ] PhotonFock :=
  LinearMap.mkContinuous
    { toFun := creationGraphOutput C f g hfg
      map_add' q r := by
        apply lp.ext
        funext n
        cases n with
        | zero => exact (zero_add _).symm
        | succ n => exact map_add (creationSector photonMeasure n f) _ _
      map_smul' c q := by
        apply lp.ext
        funext n
        cases n with
        | zero => exact (smul_zero c).symm
        | succ n => exact map_smul (creationSector photonMeasure n f) c _ }
    (‖g‖ * ‖radiationGraphDerivative‖ + ‖f‖ * ‖radiationGraphInclusion‖)
    (fun q => (creationGraphOutput_norm_le C f g hfg q).trans (by
      nlinarith only [radiationGraphDerivative.le_opNorm q, radiationGraphInclusion.le_opNorm q,
        norm_nonneg g, norm_nonneg f]))

theorem creationRadiation_norm_sq (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (q : RadiationGraphSpace) :
    ‖creationRadiation C f g hfg q‖ ^ 2 =
      ‖annihilationRadiation f g hfg q‖ ^ 2 + ‖f‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 :=
  creationGraphOutput_norm_sq C f g hfg q

end GptLean.PhysicalFock
