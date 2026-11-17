import GptLean.PhotonLocalizationLocalForms
import GptLean.PhotonLocalizationPhysicalTails
import GptLean.ElectronicLocalizationMetric
import GptLean.SymmetricLift.TensorApproximation

/-!
The electronic product cutoff used by the local form construction.
Its coordinate derivative bound is derived from one fixed smooth bump
and rescaling, giving the explicit inverse-square localization cost.
-/

noncomputable section

namespace GptLean.PhotonLocalization

open GptLean.SymmetricLift GptLean.PhotonLocalizationKernelCutoffs
open scoped ContDiff

abbrev ElectronicPosition := EuclideanSpace ℝ (Fin 3)

theorem retained_one_hasCompactSupport :
    HasCompactSupport (retained (P := ElectronicPosition) 1) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ElectronicPosition) 2)
  intro x hx
  by_contra hout
  have hn : 2 ≤ ‖x‖ := by
    have hgt : 2 < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hout
    exact hgt.le
  exact hx (retained_eq_zero (by norm_num) (by simpa using hn))

theorem retained_one_exists_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ElectronicPosition, ‖fderiv ℝ (retained 1) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (retained_one_hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    ((retained_smooth (P := ElectronicPosition) 1).continuous_fderiv (by simp))
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

/-- A constant determined solely by the fixed one-particle bump. -/
def electronicDerivativeConstant : ℝ := retained_one_exists_derivative_bound.choose

theorem electronicDerivativeConstant_nonneg : 0 ≤ electronicDerivativeConstant :=
  retained_one_exists_derivative_bound.choose_spec.1

theorem retained_one_derivative_bound (x : ElectronicPosition) :
    ‖fderiv ℝ (retained 1) x‖ ≤ electronicDerivativeConstant :=
  retained_one_exists_derivative_bound.choose_spec.2 x

theorem retained_fderiv_scale (L : ℝ) (x v : ElectronicPosition) :
    fderiv ℝ (retained L) x v =
      L⁻¹ * fderiv ℝ (retained 1) (L⁻¹ • x) v := by
  have he : retained (P := ElectronicPosition) L =
      fun y => retained 1 (L⁻¹ • y) := by
    funext y
    simp [retained]
  have hd := ((retained_smooth (P := ElectronicPosition) 1).differentiable (by simp)
    (L⁻¹ • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul L⁻¹)
  rw [he]
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_smul,
    smul_eq_mul] using congrArg (fun A : ElectronicPosition →L[ℝ] ℝ => A v) hd.fderiv

theorem retained_coordinate_derivative_bound {L : ℝ} (hL : 0 < L)
    (x : ElectronicPosition) (j : Fin 3) :
    |fderiv ℝ (retained L) x (EuclideanSpace.single j 1)| ≤
      electronicDerivativeConstant / L := by
  rw [retained_fderiv_scale, abs_mul, abs_inv, abs_of_pos hL]
  have h := ContinuousLinearMap.le_opNorm (fderiv ℝ (retained 1) (L⁻¹ • x))
    (EuclideanSpace.single j 1)
  have hn : ‖(EuclideanSpace.single j (1 : ℝ) : ElectronicPosition)‖ = 1 := by simp
  simp only [Real.norm_eq_abs, hn, mul_one] at h
  calc
    L⁻¹ * |fderiv ℝ (retained 1) (L⁻¹ • x) (EuclideanSpace.single j 1)|
      ≤ L⁻¹ * electronicDerivativeConstant :=
      mul_le_mul_of_nonneg_left (h.trans (retained_one_derivative_bound _)) (inv_nonneg.mpr hL.le)
    _ = _ := by ring

variable {N : ℕ}

/-- The Euclidean configuration has the same individual positions as the
product configuration used by the density marginal. -/
def electronicPositions : Configuration N →L[ℝ] (Fin N → ElectronicPosition) :=
  ContinuousLinearMap.pi (fun i => (particleLinear i).toContinuousLinearMap)

theorem electronicPositions_single (j : Fin N × Fin 3) :
    electronicPositions (EuclideanSpace.single j 1) =
      Pi.single j.1 (EuclideanSpace.single j.2 1) := by
  classical
  funext i
  change particle (EuclideanSpace.single j 1) i = _
  by_cases hi : i = j.1
  · subst i
    simpa only [Pi.single_eq_same] using particle_single_same j.1 j.2
  · simp [Pi.single_eq_of_ne hi, particle_single_ne j.1 j.2 hi]

def configurationElectronicProduct (L : ℝ) (x : Configuration N) : ℝ :=
  electronicProduct L (electronicPositions x)

theorem electronicProduct_smooth (L : ℝ) :
    ContDiff ℝ ∞ (electronicProduct (P := ElectronicPosition) (N := N) L) := by
  apply contDiff_prod
  intro i _
  exact (retained_smooth L).comp (contDiff_apply ℝ ElectronicPosition i)

theorem configurationElectronicProduct_smooth (L : ℝ) :
    ContDiff ℝ ∞ (configurationElectronicProduct (N := N) L) :=
  (electronicProduct_smooth L).comp electronicPositions.contDiff

theorem configurationElectronicProduct_derivative (L : ℝ) (x : Configuration N)
    (j : Fin N × Fin 3) :
    fderiv ℝ (configurationElectronicProduct L) x (EuclideanSpace.single j 1) =
      fderiv ℝ (retained L) (particle x j.1) (EuclideanSpace.single j.2 1) *
        ∏ i ∈ Finset.univ.erase j.1, retained L (particle x i) := by
  let η : Unit → ElectronicPosition → ℝ := fun _ => retained L
  have hd : ∀ a, Differentiable ℝ (η a) := fun _ => (retained_smooth L).differentiable (by simp)
  have ht := ElectronicLocalization.tensorMultiplier_fderiv_single η hd
    (fun _ : Fin N => ()) (electronicPositions x) j.1 (EuclideanSpace.single j.2 1)
  have hc := ((electronicProduct_smooth (N := N) L).differentiable (by simp)
    (electronicPositions x)).hasFDerivAt.comp x electronicPositions.hasFDerivAt
  change fderiv ℝ (electronicProduct L ∘ electronicPositions) x _ = _
  rw [hc.fderiv, ContinuousLinearMap.comp_apply, electronicPositions_single]
  exact ht

theorem configurationElectronicProduct_derivative_bound {L : ℝ} (hL : 0 < L)
    (x : Configuration N) (j : Fin N × Fin 3) :
    |fderiv ℝ (configurationElectronicProduct L) x (EuclideanSpace.single j 1)| ≤
      electronicDerivativeConstant / L := by
  rw [configurationElectronicProduct_derivative, abs_mul]
  have hp0 : 0 ≤ ∏ i ∈ Finset.univ.erase j.1, retained L (particle x i) :=
    Finset.prod_nonneg fun i _ => retained_nonneg _ _
  have hp1 : (∏ i ∈ Finset.univ.erase j.1, retained L (particle x i)) ≤ 1 :=
    Finset.prod_le_one (fun i _ => retained_nonneg _ _) (fun i _ => retained_le_one _ _)
  rw [abs_of_nonneg hp0]
  exact (mul_le_of_le_one_right (abs_nonneg _) hp1).trans
    (retained_coordinate_derivative_bound hL _ _)

/-- The form cutoff is the actual product, with no derivative estimate
left as an input. Its kinetic cost is proportional to N / L². -/
def physicalElectronicCutoff (L : ℝ) (hL : 0 < L) :
    SmoothElectronicCutoff (Fin N × Fin 3) where
  multiplier := configurationElectronicProduct L
  smooth := configurationElectronicProduct_smooth L
  nonneg x := electronicProduct_nonneg L (electronicPositions x)
  le_one x := electronicProduct_le_one L (electronicPositions x)
  derivativeBound := electronicDerivativeConstant / L
  bound_nonneg := div_nonneg electronicDerivativeConstant_nonneg hL.le
  derivative_bound j x := configurationElectronicProduct_derivative_bound hL x j

/-- The bounded configuration region contains every electronic coordinate. -/
def electronicConfigurationRegion (L : ℝ) : Set (Configuration N) :=
  {x | ∀ i, ‖particle x i‖ ≤ 2 * L}

theorem physicalElectronicCutoff_support {L : ℝ} (hL : 0 < L)
    (x : Configuration N) (hx : x ∉ electronicConfigurationRegion L) :
    (physicalElectronicCutoff (N := N) L hL).multiplier x = 0 := by
  have hn : ∃ i, 2 * L < ‖particle x i‖ := by
    simpa only [electronicConfigurationRegion, Set.mem_ofPred_eq, not_forall, not_le] using hx
  obtain ⟨i, hi⟩ := hn
  exact electronicProduct_eq_zero hL ⟨i, hi.le⟩

theorem physicalElectronicCutoff_cost (L : ℝ) (hL : 0 < L) :
    2 * Fintype.card (Fin N × Fin 3) *
      (physicalElectronicCutoff (N := N) L hL).derivativeBound ^ 2 =
        (6 * N * electronicDerivativeConstant ^ 2) / L ^ 2 := by
  simp only [physicalElectronicCutoff, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_ofNat, div_pow]
  ring

end GptLean.PhotonLocalization
