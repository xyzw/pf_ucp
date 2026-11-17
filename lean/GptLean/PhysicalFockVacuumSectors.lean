import GptLean.PhysicalFockVacuumGeometry
import GptLean.PhysicalFockTensorSectors

/-!
The actual zero-photon sector is the span of the actual vacuum. Thus
the tensor vacuum projection is precisely the sum of the joint sectors
whose discarded number is zero. No environmental basis index enters.
-/

noncomputable section
namespace GptLean.PhysicalFock.VacuumSectors

open MeasureTheory UniformSpace TensorCoordinates TensorSectors TensorGentle
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true

section Tensor
variable {H E Z : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

private def tensorDiscard (A : E →L[ℂ] E) : TensorSpace H E →L[ℂ] TensorSpace H E :=
  (A.lTensor H).completion

private theorem tensorDiscard_tensor (A : E →L[ℂ] E) (u : H) (v : E) :
    tensorDiscard A (tensor u v) = tensor u (A v) := by
  rw [tensor_apply, tensorDiscard, ContinuousLinearMap.completion_apply_coe]
  rfl

private theorem tensor_map_ext (T S : TensorSpace H E →L[ℂ] Z)
    (h : ∀ u v, T (tensor u v) = S (tensor u v)) : T = S := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq T.continuous S.continuous
  | ih z =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [Completion.coe_zero, map_zero]
    | tmul u v => exact h u v
    | add z z' hz hz' => simpa only [Completion.coe_add, map_add] using congrArg₂ (· + ·) hz hz'

private theorem tensor_smul_shift (u : H) (v : E) (a : ℂ) :
    tensor u (a • v) = tensor (a • u) v := by
  simp only [map_smul, smul_apply]
end Tensor

private theorem tensor_zero_coordinate (K : ℕ → Type*)
    [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
    (z : TensorSpace (Space K) (Space K)) (p : ℕ × ℕ) :
    pairCoordinate K p (tensorDiscard (sector K 0) z) =
      if p.2 = 0 then pairCoordinate K p z else 0 := by
  classical
  induction z using Completion.induction_on with
  | hp =>
    apply isClosed_eq
    · exact (pairCoordinate K p).continuous.comp (tensorDiscard (sector K 0)).continuous
    · split_ifs <;> fun_prop
  | ih z =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [Completion.coe_zero, map_zero, ite_self]
    | tmul u v =>
      change pairCoefficients K (tensorDiscard (sector K 0) (tensor u v)) p =
        if p.2 = 0 then pairCoefficients K (tensor u v) p else 0
      rw [tensorDiscard_tensor, pairCoefficients_tensor, pairCoefficients_tensor]
      change tensor (u p.1) (lp.single 2 0 (v 0) p.2) =
        if p.2 = 0 then tensor (u p.1) (v p.2) else 0
      by_cases hp : p.2 = 0
      · obtain ⟨r, s⟩ := p
        dsimp only at hp ⊢
        subst s
        simp only [lp.single_apply_self, ite_true]
      · rw [lp.single_apply_ne _ _ _ hp, map_zero, ite_eq_right hp]
    | add z z' hz hz' =>
      simp only [Completion.coe_add, map_add, hz, hz']
      split_ifs <;> simp

private theorem subtract_zero_indicator {G : Type*} [AddGroup G] (n : ℕ) (x : G) :
    x - (if n = 0 then x else 0) = if 1 ≤ n then x else 0 := by
  by_cases h : n = 0
  · simp [h]
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
    simp only [ite_eq_right h, sub_zero, ite_eq_left hn]

private theorem pair_norm_hasSum (K : ℕ → Type*)
    [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
    (z : TensorSpace (Space K) (Space K)) :
    HasSum (fun p : ℕ × ℕ => ‖pairCoordinate K p z‖ ^ 2) (‖z‖ ^ 2) := by
  have h : HasSum (fun p : ℕ × ℕ => ‖pairCoefficients K z p‖ ^ 2)
      (‖pairCoefficients K z‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (pairCoefficients K z)
  exact (congrArg (fun s : ℝ => HasSum (fun p : ℕ × ℕ =>
    ‖pairCoordinate K p z‖ ^ 2) s)
      (congrArg (fun s : ℝ => s ^ 2) ((pairCoefficients K).norm_map z))).mp h

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
  (B : ConcreteExponentialLaw μ)

def vacuumProjection : Fock μ →L[ℂ] Fock μ :=
  (ContinuousLinearMap.smulRight (innerSL ℂ (creationWord μ [])) (creationWord μ []))

include B in
theorem vacuumProjection_eq_sector : vacuumProjection μ = photonSector μ 0 := by
  apply B.ext_words μ
  intro w
  change ⟪creationWord μ [], creationWord μ w⟫_ℂ • creationWord μ [] = _
  rw [WordGram.vacuum_word_inner, photonSector_word]
  cases w with
  | nil => simp
  | cons f w => simp

def discardedOperator (A : Fock μ →L[ℂ] Fock μ) :
    TensorSpace (Fock μ) (Fock μ) →L[ℂ] TensorSpace (Fock μ) (Fock μ) :=
  tensorDiscard A

theorem discardedOperator_tensor (A : Fock μ →L[ℂ] Fock μ) (u v : Fock μ) :
    discardedOperator μ A (tensor u v) = tensor u (A v) :=
  tensorDiscard_tensor A u v

include B in
theorem discarded_vacuum_projection :
    discardedOperator μ (photonSector μ 0) =
      (VacuumOperator.insertion μ).toContinuousLinearMap.comp (VacuumOperator.contraction μ) := by
  apply tensor_map_ext
  intro u v
  have hp := congrArg (fun A : Fock μ →L[ℂ] Fock μ => A v) (vacuumProjection_eq_sector μ B)
  have hc := VacuumOperator.contraction_tensor μ u v
  calc
    discardedOperator μ (photonSector μ 0) (tensor u v) = tensor u (photonSector μ 0 v) :=
      discardedOperator_tensor μ (photonSector μ 0) u v
    _ = tensor u (⟪creationWord μ [], v⟫_ℂ • creationWord μ []) := congrArg (tensor u) hp.symm
    _ = tensor (⟪creationWord μ [], v⟫_ℂ • u) (creationWord μ []) := tensor_smul_shift _ _ _
    _ = _ := (congrArg (fun w : Fock μ => tensor w (creationWord μ [])) hc).symm

theorem discarded_sector_coordinate (z : TensorSpace (Fock μ) (Fock μ)) (p : ℕ × ℕ) :
    pairCoordinate (Sector μ) p (discardedOperator μ (photonSector μ 0) z) =
      if p.2 = 0 then pairCoordinate (Sector μ) p z else 0 :=
  tensor_zero_coordinate (Sector μ) z p

theorem residual_coordinate (BF : StandardSymmetricFockExponential)
    (z : TensorSpace PhotonFock PhotonFock) (p : ℕ × ℕ) :
    pairCoordinate (Sector photonMeasure) p (residual z) =
      if 1 ≤ p.2 then pairCoordinate (Sector photonMeasure) p z else 0 := by
  let P := pairCoordinate (Sector photonMeasure) p
  have hsub := P.map_sub z
    (VacuumOperator.insertion photonMeasure (VacuumOperator.contraction photonMeasure z))
  have h := congrArg (fun A : TensorSpace PhotonFock PhotonFock →L[ℂ]
      TensorSpace PhotonFock PhotonFock => A z)
    (discarded_vacuum_projection photonMeasure (photonExponential BF))
  have hp := congrArg P h
  have hc := discarded_sector_coordinate photonMeasure z p
  exact hsub.trans ((congrArg (fun w => P z - w) (hp.symm.trans hc)).trans
    (subtract_zero_indicator p.2 (P z)))

theorem nonvac_mass_hasSum (BF : StandardSymmetricFockExponential)
    (z : TensorSpace PhotonFock PhotonFock) :
    HasSum (fun p : ℕ × ℕ => if 1 ≤ p.2 then
      ‖pairCoordinate (Sector photonMeasure) p z‖ ^ 2 else 0)
      (‖z‖ ^ 2 - ‖VacuumOperator.contraction photonMeasure z‖ ^ 2) := by
  have h := pair_norm_hasSum (Sector photonMeasure) (residual z)
  have hsum := (congrArg (fun s : ℝ => HasSum
    (fun p : ℕ × ℕ => ‖pairCoordinate (Sector photonMeasure) p (residual z)‖ ^ 2) s)
    (residual_norm_sq z)).mp h
  apply hsum.congr_fun
  intro p
  have hc := congrArg (fun v : TensorSpace (Sector photonMeasure p.1)
      (Sector photonMeasure p.2) => ‖v‖ ^ 2) (residual_coordinate BF z p)
  exact (hc.trans (by split_ifs <;> simp)).symm

end GptLean.PhysicalFock.VacuumSectors
