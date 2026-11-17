import GptLean.PhotonLocalizationCompactness
import GptLean.Repair.CovariantProduct
import GptLean.PhotonLocalization

/-!
The supported local free form in the photon compactness argument.

Electronic derivatives are distributional derivatives of actual L²
functions. Multiplication by a smooth electronic cutoff and a photon
number contraction preserves this domain by the weak product rule.
The resulting form estimate and its ensemble sum are proved here.
-/

noncomputable section

namespace GptLean.PhotonLocalization

open MeasureTheory Filter GptLean.SymmetricLift GptLean.Repair
open scoped ENNReal Topology ContDiff

section Multipliers

variable {Ω K : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

private theorem bounded_multiplier_memLp (a : Ω → ℝ)
    (ha : AEStronglyMeasurable a μ) (B : ℝ)
    (hb : ∀ᵐ x ∂μ, |a x| ≤ B) (u : Lp K 2 μ) :
    MemLp (fun x => a x • u x) 2 μ := by
  apply (Lp.memLp u).of_le_mul (c := B) (ha.smul (Lp.aestronglyMeasurable u))
  filter_upwards [hb] with x hx
  simpa only [Pi.smul_apply', norm_smul, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right hx (norm_nonneg (u x))

/-- Multiplication by an arbitrary bounded real function on complex L². -/
def realL2Multiplier (a : Ω → ℝ) (ha : AEStronglyMeasurable a μ)
    (B : ℝ) (hb : ∀ᵐ x ∂μ, |a x| ≤ B) : Lp K 2 μ →L[ℂ] Lp K 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun u => (bounded_multiplier_memLp a ha B hb u).toLp _
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [(bounded_multiplier_memLp a ha B hb (u + v)).coeFn_toLp,
          (bounded_multiplier_memLp a ha B hb u).coeFn_toLp,
          (bounded_multiplier_memLp a ha B hb v).coeFn_toLp,
          Lp.coeFn_add u v,
          Lp.coeFn_add ((bounded_multiplier_memLp a ha B hb u).toLp _)
            ((bounded_multiplier_memLp a ha B hb v).toLp _)]
          with x h₁ h₂ h₃ h₄ h₅
        simp only [h₁, h₅, h₄, Pi.add_apply, h₂, h₃, smul_add]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [(bounded_multiplier_memLp a ha B hb (c • u)).coeFn_toLp,
          (bounded_multiplier_memLp a ha B hb u).coeFn_toLp,
          Lp.coeFn_smul c u,
          Lp.coeFn_smul c ((bounded_multiplier_memLp a ha B hb u).toLp _)]
          with x h₁ h₂ h₃ h₄
        simp only [h₁, h₄, h₃, Pi.smul_apply, h₂, RingHom.id_apply]
        exact smul_comm _ _ _ }
    B (by
      intro u
      change ‖(bounded_multiplier_memLp a ha B hb u).toLp _‖ ≤ B * ‖u‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(bounded_multiplier_memLp a ha B hb u).coeFn_toLp, hb]
        with x hx hb'
      rw [hx, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hb' (norm_nonneg _))

theorem realL2Multiplier_apply (a : Ω → ℝ) (ha : AEStronglyMeasurable a μ)
    (B : ℝ) (hb : ∀ᵐ x ∂μ, |a x| ≤ B) (u : Lp K 2 μ) :
    realL2Multiplier a ha B hb u =ᵐ[μ] fun x => a x • u x :=
  (bounded_multiplier_memLp a ha B hb u).coeFn_toLp

theorem realL2Multiplier_norm_le (a : Ω → ℝ) (ha : AEStronglyMeasurable a μ)
    (B : ℝ) (hb : ∀ᵐ x ∂μ, |a x| ≤ B) (u : Lp K 2 μ) :
    ‖realL2Multiplier a ha B hb u‖ ≤ B * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [realL2Multiplier_apply a ha B hb u, hb] with x hx hb'
  rw [hx, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hb' (norm_nonneg _)

theorem compLpL_norm_le (P : K →L[ℂ] K) (hP : ∀ v, ‖P v‖ ≤ ‖v‖)
    (u : Lp K 2 μ) : ‖P.compLpL 2 μ u‖ ≤ ‖u‖ := by
  simpa only [one_mul] using
    (Lp.norm_le_mul_norm_of_ae_le_mul (c := 1)
      (f := P.compLpL 2 μ u) (g := u) (by
        filter_upwards [P.coeFn_compLpL u] with x hx
        simpa only [hx, one_mul] using hP (u x)))

end Multipliers

variable {I K : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

abbrev SpatialPhotonL2 (I K : Type*) [Fintype I]
    [NormedAddCommGroup K] := Lp K 2 (volume : Measure (EuclideanSpace ℝ I))

/-- A vector in the actual free form domain. Radiation is represented by
the graph of its square root, and electronic derivatives are weak ones. -/
structure SpatialFreeVector (R : K →ₗ.[ℂ] K) where
  value : SpatialPhotonL2 I K
  derivative : I → SpatialPhotonL2 I K
  radiation : SpatialPhotonL2 I K
  weak : HasWeakH1Local (fun x => value x) (fun i x => derivative i x)
  radiation_graph : ∀ᵐ x ∂volume, (value x, radiation x) ∈ R.graph

namespace SpatialFreeVector

variable {R : K →ₗ.[ℂ] K}

def form (u : SpatialFreeVector (I := I) R) : ℝ :=
  ‖u.value‖ ^ 2 + (∑ i, ‖u.derivative i‖ ^ 2) + ‖u.radiation‖ ^ 2

theorem form_nonneg (u : SpatialFreeVector (I := I) R) : 0 ≤ u.form := by
  unfold form
  positivity

theorem mass_le_form (u : SpatialFreeVector (I := I) R) : ‖u.value‖ ^ 2 ≤ u.form := by
  unfold form
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg ‖u.derivative i‖)
  nlinarith [sq_nonneg ‖u.radiation‖]

end SpatialFreeVector

/-- The scalar cutoff and its actual coordinate derivatives. The bound
is on the fixed multiplier, independent of all source vectors and sectors. -/
structure SmoothElectronicCutoff (I : Type*) [Fintype I] [DecidableEq I] where
  multiplier : EuclideanSpace ℝ I → ℝ
  smooth : ContDiff ℝ ∞ multiplier
  nonneg : ∀ x, 0 ≤ multiplier x
  le_one : ∀ x, multiplier x ≤ 1
  derivativeBound : ℝ
  bound_nonneg : 0 ≤ derivativeBound
  derivative_bound : ∀ i x,
    |fderiv ℝ multiplier x (EuclideanSpace.single i 1)| ≤ derivativeBound

namespace SmoothElectronicCutoff

def operator (Z : SmoothElectronicCutoff I) :
    SpatialPhotonL2 I K →L[ℂ] SpatialPhotonL2 I K :=
  realL2Multiplier Z.multiplier Z.smooth.continuous.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by rw [abs_of_nonneg (Z.nonneg x)]; exact Z.le_one x)

def commutator (Z : SmoothElectronicCutoff I) (i : I) :
    SpatialPhotonL2 I K →L[ℂ] SpatialPhotonL2 I K :=
  realL2Multiplier (fun x => fderiv ℝ Z.multiplier x (EuclideanSpace.single i 1))
    (((Z.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable)
    Z.derivativeBound (Eventually.of_forall (Z.derivative_bound i))

theorem operator_apply (Z : SmoothElectronicCutoff I) (u : SpatialPhotonL2 I K) :
    Z.operator u =ᵐ[volume] fun x => Z.multiplier x • u x :=
  realL2Multiplier_apply _ _ _ _ _

theorem commutator_apply (Z : SmoothElectronicCutoff I) (i : I)
    (u : SpatialPhotonL2 I K) :
    Z.commutator i u =ᵐ[volume] fun x =>
      fderiv ℝ Z.multiplier x (EuclideanSpace.single i 1) • u x :=
  realL2Multiplier_apply _ _ _ _ _

theorem operator_norm_le (Z : SmoothElectronicCutoff I) (u : SpatialPhotonL2 I K) :
    ‖Z.operator u‖ ≤ ‖u‖ := by
  have h := realL2Multiplier_norm_le Z.multiplier
    Z.smooth.continuous.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by rw [abs_of_nonneg (Z.nonneg x)]; exact Z.le_one x) u
  simpa only [operator, one_mul] using h

theorem commutator_norm_le (Z : SmoothElectronicCutoff I) (i : I)
    (u : SpatialPhotonL2 I K) :
    ‖Z.commutator i u‖ ≤ Z.derivativeBound * ‖u‖ :=
  realL2Multiplier_norm_le _ _ _ _ u

variable [CompleteSpace K]

/-- The cut vector and its derivatives are constructed on the full space.
The product rule is proved distributionally before any restricted form
or local spectrum is used. -/
def cutVector (Z : SmoothElectronicCutoff I) (P : K →L[ℂ] K)
    {R : K →ₗ.[ℂ] K}
    (hR : ∀ v w, (v, w) ∈ R.graph → (P v, P w) ∈ R.graph)
    (u : SpatialFreeVector (I := I) R) : SpatialFreeVector (I := I) R where
  value := Z.operator (P.compLpL 2 volume u.value)
  derivative i := Z.operator (P.compLpL 2 volume (u.derivative i)) +
    Z.commutator i (P.compLpL 2 volume u.value)
  radiation := Z.operator (P.compLpL 2 volume u.radiation)
  weak := by
    have hw := weakH1Local_smooth_real_smul
      (weakH1Local_map (P.restrictScalars ℝ) u.weak) Z.smooth
    apply hw.congr
    · filter_upwards [Z.operator_apply (P.compLpL 2 volume u.value),
        P.coeFn_compLpL u.value] with x hx hp
      rw [hx, hp]
      rfl
    · intro i
      filter_upwards [Z.operator_apply (P.compLpL 2 volume (u.derivative i)),
        Z.commutator_apply i (P.compLpL 2 volume u.value),
        P.coeFn_compLpL (u.derivative i), P.coeFn_compLpL u.value,
        Lp.coeFn_add (Z.operator (P.compLpL 2 volume (u.derivative i)))
          (Z.commutator i (P.compLpL 2 volume u.value))]
        with x hz hc hp hpu ha
      simp only [ha, Pi.add_apply, hz, hc, hp, hpu]
      rfl
  radiation_graph := by
    filter_upwards [Z.operator_apply (P.compLpL 2 volume u.value),
      Z.operator_apply (P.compLpL 2 volume u.radiation),
      P.coeFn_compLpL u.value, P.coeFn_compLpL u.radiation, u.radiation_graph]
      with x hz hr hp hpr hg
    rw [hz, hr, hp, hpr]
    simpa only [Prod.smul_mk, Complex.coe_smul] using
      R.graph.smul_mem (Z.multiplier x : ℂ) (hR _ _ hg)

theorem cutVector_value_norm_le (Z : SmoothElectronicCutoff I) (P : K →L[ℂ] K)
    (hP : ∀ v, ‖P v‖ ≤ ‖v‖) {R : K →ₗ.[ℂ] K}
    (hR : ∀ v w, (v, w) ∈ R.graph → (P v, P w) ∈ R.graph)
    (u : SpatialFreeVector (I := I) R) :
    ‖(Z.cutVector P hR u).value‖ ≤ ‖u.value‖ :=
  (Z.operator_norm_le _).trans (compLpL_norm_le P hP _)

theorem cutVector_radiation_norm_le (Z : SmoothElectronicCutoff I) (P : K →L[ℂ] K)
    (hP : ∀ v, ‖P v‖ ≤ ‖v‖) {R : K →ₗ.[ℂ] K}
    (hR : ∀ v w, (v, w) ∈ R.graph → (P v, P w) ∈ R.graph)
    (u : SpatialFreeVector (I := I) R) :
    ‖(Z.cutVector P hR u).radiation‖ ≤ ‖u.radiation‖ :=
  (Z.operator_norm_le _).trans (compLpL_norm_le P hP _)

theorem cutVector_derivative_sq_le (Z : SmoothElectronicCutoff I) (P : K →L[ℂ] K)
    (hP : ∀ v, ‖P v‖ ≤ ‖v‖) {R : K →ₗ.[ℂ] K}
    (hR : ∀ v w, (v, w) ∈ R.graph → (P v, P w) ∈ R.graph)
    (u : SpatialFreeVector (I := I) R) (i : I) :
    ‖(Z.cutVector P hR u).derivative i‖ ^ 2 ≤
      2 * ‖u.derivative i‖ ^ 2 + 2 * Z.derivativeBound ^ 2 * ‖u.value‖ ^ 2 := by
  have h₁ := (Z.operator_norm_le (P.compLpL 2 volume (u.derivative i))).trans
    (compLpL_norm_le P hP (u.derivative i))
  have h₂ := (Z.commutator_norm_le i (P.compLpL 2 volume u.value)).trans
    (mul_le_mul_of_nonneg_left (compLpL_norm_le P hP u.value) Z.bound_nonneg)
  have hs₁ := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr h₁
  have hs₂ := sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg Z.bound_nonneg (norm_nonneg _)) |>.mpr h₂
  have hsum := GptLean.PhotonLocalization.norm_add_sq_le
    (Z.operator (P.compLpL 2 volume (u.derivative i)))
    (Z.commutator i (P.compLpL 2 volume u.value))
  change ‖Z.operator (P.compLpL 2 volume (u.derivative i)) +
    Z.commutator i (P.compLpL 2 volume u.value)‖ ^ 2 ≤ _
  nlinarith [sq_nonneg (‖Z.operator (P.compLpL 2 volume (u.derivative i))‖ -
    ‖Z.commutator i (P.compLpL 2 volume u.value)‖)]

/-- Uniform in the photon number cutoff. The only new cost comes from
the actual derivative of the electronic multiplier. -/
theorem cutVector_form_le (Z : SmoothElectronicCutoff I) (P : K →L[ℂ] K)
    (hP : ∀ v, ‖P v‖ ≤ ‖v‖) {R : K →ₗ.[ℂ] K}
    (hR : ∀ v w, (v, w) ∈ R.graph → (P v, P w) ∈ R.graph)
    (u : SpatialFreeVector (I := I) R) :
    (Z.cutVector P hR u).form ≤ 2 * u.form +
      (2 * Fintype.card I * Z.derivativeBound ^ 2) * ‖u.value‖ ^ 2 := by
  have hm := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (Z.cutVector_value_norm_le P hP hR u)
  have hr := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (Z.cutVector_radiation_norm_le P hP hR u)
  have hd := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Z.cutVector_derivative_sq_le P hP hR u i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hd
  unfold SpatialFreeVector.form
  nlinarith [sq_nonneg ‖u.value‖, sq_nonneg ‖u.radiation‖]

end SmoothElectronicCutoff

end GptLean.PhotonLocalization
