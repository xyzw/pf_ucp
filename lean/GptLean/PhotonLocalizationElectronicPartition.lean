import GptLean.PhotonLocalizationPhysicalCompactness
import GptLean.ElectronicLocalizationIMS

/-!
The actual retained electronic product is one member of a smooth finite
tensor square partition. Its IMS estimate therefore keeps coefficient one
on the original kinetic energy. The error is bounded by a fixed constant
times N / L². No square root of a many-electron complement is introduced.
-/

noncomputable section

namespace GptLean.PhotonLocalization

open ElectronicLocalization PhotonLocalizationKernelCutoffs SymmetricLift
open scoped InnerProductSpace Topology

theorem discarded_one_sub_one_compact :
    HasCompactSupport (fun x : ElectronicPosition => discarded 1 x - 1) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ElectronicPosition) 2)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  have heq := discarded_eq_one (P := ElectronicPosition) (R := 1) zero_lt_one
    (y := x) (by linarith)
  exact hx (by change discarded 1 x - 1 = 0; rw [heq, sub_self])

theorem discarded_one_exists_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ElectronicPosition, ‖fderiv ℝ (discarded 1) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (discarded_one_sub_one_compact.fderiv ℝ).exists_bound_of_continuous
    (((discarded_smooth (P := ElectronicPosition) 1).sub contDiff_const).continuous_fderiv
      (by simp))
  simp only [fderiv_sub_const] at hC
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

def electronicDiscardDerivativeConstant : ℝ := discarded_one_exists_derivative_bound.choose

theorem electronicDiscardDerivativeConstant_nonneg : 0 ≤ electronicDiscardDerivativeConstant :=
  discarded_one_exists_derivative_bound.choose_spec.1

theorem discarded_one_derivative_bound (x : ElectronicPosition) :
    ‖fderiv ℝ (discarded 1) x‖ ≤ electronicDiscardDerivativeConstant :=
  discarded_one_exists_derivative_bound.choose_spec.2 x

theorem discarded_fderiv_scale (L : ℝ) (x v : ElectronicPosition) :
    fderiv ℝ (discarded L) x v =
      L⁻¹ * fderiv ℝ (discarded 1) (L⁻¹ • x) v := by
  have he : discarded (P := ElectronicPosition) L =
      fun y => discarded 1 (L⁻¹ • y) := by
    funext y
    simp [discarded]
  have hd := ((discarded_smooth (P := ElectronicPosition) 1).differentiable (by simp)
    (L⁻¹ • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul L⁻¹)
  rw [he]
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_smul,
    smul_eq_mul] using congrArg (fun A : ElectronicPosition →L[ℝ] ℝ => A v) hd.fderiv

theorem discarded_coordinate_derivative_bound {L : ℝ} (hL : 0 < L)
    (x : ElectronicPosition) (j : Fin 3) :
    |fderiv ℝ (discarded L) x (EuclideanSpace.single j 1)| ≤
      electronicDiscardDerivativeConstant / L := by
  rw [discarded_fderiv_scale, abs_mul, abs_inv, abs_of_pos hL]
  have h := ContinuousLinearMap.le_opNorm (fderiv ℝ (discarded 1) (L⁻¹ • x))
    (EuclideanSpace.single j 1)
  have hn : ‖(EuclideanSpace.single j (1 : ℝ) : ElectronicPosition)‖ = 1 := by simp
  simp only [Real.norm_eq_abs, hn, mul_one] at h
  calc
    _ ≤ L⁻¹ * electronicDiscardDerivativeConstant :=
      mul_le_mul_of_nonneg_left (h.trans (discarded_one_derivative_bound _)) (inv_nonneg.mpr hL.le)
    _ = _ := by ring

/-- The two smooth one-electron partition functions. -/
def electronicPair (L : ℝ) : Bool → ElectronicPosition → ℝ
  | false => retained L
  | true => discarded L

theorem electronicPair_differentiable (L : ℝ) (a : Bool) :
    Differentiable ℝ (electronicPair L a) := by
  cases a
  · exact (retained_smooth L).differentiable (by simp)
  · exact (discarded_smooth L).differentiable (by simp)

theorem electronicPair_nonneg (L : ℝ) (a : Bool) (x : ElectronicPosition) :
    0 ≤ electronicPair L a x := by
  cases a
  · exact retained_nonneg L x
  · exact discarded_nonneg L x

theorem electronicPair_partition (L : ℝ) (x : ElectronicPosition) :
    HasSum (fun a : Bool => electronicPair L a x ^ 2) 1 := by
  have h : (∑ a : Bool, electronicPair L a x ^ 2) = 1 := by
    simpa [electronicPair, add_comm] using square_partition L x
  exact h ▸ hasSum_fintype (fun a : Bool => electronicPair L a x ^ 2)

def electronicPartitionConstant : ℝ :=
  electronicDerivativeConstant ^ 2 + electronicDiscardDerivativeConstant ^ 2

theorem electronicPartitionConstant_nonneg : 0 ≤ electronicPartitionConstant := by
  unfold electronicPartitionConstant
  positivity

theorem electronicPair_coordinate_metric {L : ℝ} (hL : 0 < L)
    (x : ElectronicPosition) (j : Fin 3) :
    (∑' a : Bool, fderiv ℝ (electronicPair L a) x (EuclideanSpace.single j 1) ^ 2) ≤
      electronicPartitionConstant / L ^ 2 := by
  have hr := (sq_le_sq₀ (abs_nonneg _) (div_nonneg electronicDerivativeConstant_nonneg hL.le)).2
    (retained_coordinate_derivative_bound hL x j)
  have hd := (sq_le_sq₀ (abs_nonneg _)
    (div_nonneg electronicDiscardDerivativeConstant_nonneg hL.le)).2
    (discarded_coordinate_derivative_bound hL x j)
  simp only [sq_abs, div_pow] at hr hd
  simpa [tsum_fintype, electronicPair, electronicPartitionConstant, add_div, add_comm] using
    add_le_add hr hd

variable {N : ℕ}

theorem electronicTensor_coordinate_metric {L : ℝ} (hL : 0 < L)
    (X : Fin N → ElectronicPosition) (i : Fin N) (j : Fin 3) :
    (∑' a : Fin N → Bool, fderiv ℝ (tensorMultiplier (electronicPair L) a) X
      (Pi.single i (EuclideanSpace.single j 1)) ^ 2) ≤
      electronicPartitionConstant / L ^ 2 := by
  rw [(tensorMultiplier_single_hasSum_sq (electronicPair L) (locallyFinite_of_finite _)
    (electronicPair_differentiable L) (electronicPair_nonneg L)
    (electronicPair_partition L) X i (EuclideanSpace.single j 1)).tsum_eq]
  exact electronicPair_coordinate_metric hL (X i) j

theorem electronicTensor_total_metric {L : ℝ} (hL : 0 < L)
    (X : Fin N → ElectronicPosition) :
    (∑ i : Fin N, ∑ j : Fin 3, ∑' a : Fin N → Bool,
      fderiv ℝ (tensorMultiplier (electronicPair L) a) X
        (Pi.single i (EuclideanSpace.single j 1)) ^ 2) ≤
      (3 * N * electronicPartitionConstant) / L ^ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin N) _ =>
    Finset.sum_le_sum (s := Finset.univ) fun (j : Fin 3) _ =>
      electronicTensor_coordinate_metric hL X i j
  calc
    _ ≤ ∑ _i : Fin N, ∑ _j : Fin 3, electronicPartitionConstant / L ^ 2 := h
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The selected partition member is exactly the retained product used
in the existing electronic cutoff, at the same radius. -/
theorem electronicTensor_retained (L : ℝ) :
    tensorMultiplier (electronicPair L) (fun _ : Fin N => false) = electronicProduct L := rfl

theorem retained_product_coordinate_ims {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {L : ℝ} (hL : 0 < L)
    (X : Fin N → ElectronicPosition) (i : Fin N) (j : Fin 3) (d ψ : H) :
    ‖(electronicProduct L X : ℂ) • d - Complex.I •
        (fderiv ℝ (electronicProduct L) X (Pi.single i (EuclideanSpace.single j 1)) : ℂ) • ψ‖ ^ 2 ≤
      ‖d‖ ^ 2 + (electronicPartitionConstant / L ^ 2) * ‖ψ‖ ^ 2 := by
  let f := tensorMultiplier (electronicPair L) (N := N)
  have hd : ∀ a, Differentiable ℝ (f a) := by
    intro a
    simpa only [f, Function.comp_def, Equiv.refl_apply] using
      permutedTensor_differentiable (electronicPair L) (electronicPair_differentiable L)
        a (Equiv.refl (Fin N))
  have hs := localization_ims_hasSum f (locallyFinite_of_finite _) hd
    (tensorMultiplier_nonneg _ (electronicPair_nonneg L))
    (tensorMultiplier_hasSum_sq _ (locallyFinite_of_finite _) (electronicPair_partition L))
    (fun _ => d) (fun _ => ψ) X (Pi.single i (EuclideanSpace.single j 1))
  have hterm : ‖localizedDerivative f (fun _ => d) (fun _ => ψ)
      (Pi.single i (EuclideanSpace.single j 1)) (fun _ => false) X‖ ^ 2 ≤
      ∑ a : Fin N → Bool, ‖localizedDerivative f (fun _ => d) (fun _ => ψ)
        (Pi.single i (EuclideanSpace.single j 1)) a X‖ ^ 2 :=
    Finset.single_le_sum (f := fun a : Fin N → Bool =>
      ‖localizedDerivative f (fun _ => d) (fun _ => ψ)
        (Pi.single i (EuclideanSpace.single j 1)) a X‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
  have hsum := hs.tsum_eq
  rw [tsum_fintype] at hsum
  rw [hsum] at hterm
  have hmetric := electronicTensor_coordinate_metric hL X i j
  have hbound := add_le_add_left (mul_le_mul_of_nonneg_right hmetric (sq_nonneg ‖ψ‖)) (‖d‖ ^ 2)
  exact hterm.trans (by simpa only [f, add_comm] using hbound)

theorem configuration_product_coordinate_ims {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {L : ℝ} (hL : 0 < L)
    (x : Configuration N) (j : Fin N × Fin 3) (d ψ : H) :
    ‖(configurationElectronicProduct L x : ℂ) • d - Complex.I •
        (fderiv ℝ (configurationElectronicProduct L) x (EuclideanSpace.single j 1) : ℂ) • ψ‖ ^ 2 ≤
      ‖d‖ ^ 2 + (electronicPartitionConstant / L ^ 2) * ‖ψ‖ ^ 2 := by
  have hc := ((electronicProduct_smooth (N := N) L).differentiable (by simp)
    (electronicPositions x)).hasFDerivAt.comp x electronicPositions.hasFDerivAt
  have hd : fderiv ℝ (configurationElectronicProduct L) x (EuclideanSpace.single j 1) =
      fderiv ℝ (electronicProduct L) (electronicPositions x)
        (Pi.single j.1 (EuclideanSpace.single j.2 1)) := by
    change fderiv ℝ (electronicProduct L ∘ electronicPositions) x _ = _
    rw [hc.fderiv, ContinuousLinearMap.comp_apply, electronicPositions_single]
  rw [hd]
  exact retained_product_coordinate_ims hL (electronicPositions x) j.1 j.2 d ψ

/-- This is the same `physicalElectronicFamily` used by local compactness. -/
theorem physicalElectronicFamily_coordinate_ims {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (L : ℕ)
    (x : Configuration N) (j : Fin N × Fin 3) (d ψ : H) :
    ‖((physicalElectronicFamily L).multiplier x : ℂ) • d - Complex.I •
        (fderiv ℝ (physicalElectronicFamily L).multiplier x
          (EuclideanSpace.single j 1) : ℂ) • ψ‖ ^ 2 ≤
      ‖d‖ ^ 2 + (electronicPartitionConstant / ((L : ℝ) + 1) ^ 2) * ‖ψ‖ ^ 2 :=
  configuration_product_coordinate_ims (by positivity) x j d ψ

theorem physicalElectronicFamily_kinetic_ims {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (L : ℕ) (x : Configuration N)
    (d : Fin N × Fin 3 → H) (ψ : H) :
    (1 / 2 : ℝ) * ∑ j : Fin N × Fin 3,
      ‖((physicalElectronicFamily L).multiplier x : ℂ) • d j - Complex.I •
        (fderiv ℝ (physicalElectronicFamily L).multiplier x
          (EuclideanSpace.single j 1) : ℂ) • ψ‖ ^ 2 ≤
      (1 / 2 : ℝ) * ∑ j : Fin N × Fin 3, ‖d j‖ ^ 2 +
        (3 * N * electronicPartitionConstant / (2 * ((L : ℝ) + 1) ^ 2)) * ‖ψ‖ ^ 2 := by
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ j : Fin N × Fin 3,
        (‖d j‖ ^ 2 + (electronicPartitionConstant / ((L : ℝ) + 1) ^ 2) * ‖ψ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun j _ => physicalElectronicFamily_coordinate_ims L x j (d j) ψ)
        (by norm_num)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem physicalElectronicFamily_ims_cost_zero :
    Filter.Tendsto (fun L : ℕ =>
      3 * N * electronicPartitionConstant / (2 * ((L : ℝ) + 1) ^ 2))
      Filter.atTop (𝓝 0) := by
  have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul
    (3 * N * electronicPartitionConstant / 2)
  simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, div_pow, one_pow,
    div_mul_div_comm, div_one, mul_one] using h

/-- Every RMS-symmetrized branch is invariant under electron permutations. -/
theorem symmetricElectronicPartition_perm (L : ℝ) (a : Fin N → Bool)
    (X : Fin N → ElectronicPosition) (π : Equiv.Perm (Fin N)) :
    symmetricMultiplier (electronicPair L) a (X ∘ π) =
      symmetricMultiplier (electronicPair L) a X :=
  symmetricMultiplier_perm _ _ _ _

/-- Symmetrization leaves the all-retained branch exactly unchanged. -/
theorem symmetricElectronicPartition_retained (L : ℝ) :
    symmetricMultiplier (electronicPair L) (fun _ : Fin N => false) =
      electronicProduct L := by
  funext X
  have hp (π : Equiv.Perm (Fin N)) :
      tensorMultiplier (electronicPair L) (fun _ : Fin N => false) (X ∘ π) =
        electronicProduct L X := by
    change (∏ i, retained L (X (π i))) = ∏ i, retained L (X i)
    exact Equiv.prod_comp π (fun i => retained L (X i))
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (sq_eq_sq₀ (symmetricMultiplier_nonneg _ _ _) (electronicProduct_nonneg L X)).mp
  rw [symmetricMultiplier_sq]
  simp only [hp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hc

theorem symmetricElectronicPartition_hasSum_sq (L : ℝ) (X : Fin N → ElectronicPosition) :
    HasSum (fun a : Fin N → Bool => symmetricMultiplier (electronicPair L) a X ^ 2) 1 :=
  symmetricMultiplier_hasSum_sq _ (locallyFinite_of_finite _) (electronicPair_partition L) X

theorem symmetricElectronicPartition_differentiable (L : ℝ) (a : Fin N → Bool) :
    Differentiable ℝ (symmetricMultiplier (electronicPair L) a) :=
  symmetricMultiplier_differentiable _ (electronicPair_differentiable L)
    (electronicPair_nonneg L) a

theorem symmetricElectronicPartition_nonneg (L : ℝ) (a : Fin N → Bool)
    (X : Fin N → ElectronicPosition) :
    0 ≤ symmetricMultiplier (electronicPair L) a X :=
  symmetricMultiplier_nonneg _ _ _

theorem symmetricElectronicPartition_total_metric {L : ℝ} (hL : 0 < L)
    (X : Fin N → ElectronicPosition) :
    (∑ i : Fin N, ∑ j : Fin 3, ∑' a : Fin N → Bool,
      fderiv ℝ (symmetricMultiplier (electronicPair L) a) X
        (Pi.single i (EuclideanSpace.single j 1)) ^ 2) ≤
      (3 * N * electronicPartitionConstant) / L ^ 2 := by
  have hmetric (x : ElectronicPosition) :
      (∑ j : Fin 3, ∑' a : Bool,
        fderiv ℝ (electronicPair L a) x (EuclideanSpace.single j 1) ^ 2) ≤
          3 * electronicPartitionConstant / L ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin 3, electronicPartitionConstant / L ^ 2 :=
        Finset.sum_le_sum fun j _ => electronicPair_coordinate_metric hL x j
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have h := symmetricMultiplier_total_metric_le (electronicPair L)
    (fun j : Fin 3 => EuclideanSpace.single j 1) (locallyFinite_of_finite _)
    (electronicPair_differentiable L) (electronicPair_nonneg L)
    (electronicPair_partition L) (3 * electronicPartitionConstant / L ^ 2) hmetric X
  exact h.trans_eq (by ring)

/-- The complete symmetric partition has the scalar IMS metric used by
the signed full-form assembly, with the same electronic cutoff radius. -/
theorem symmetricElectronicPartition_ims_metric (L : ℕ)
    (X : Fin N → ElectronicPosition) :
    (1 / 2 : ℝ) * ∑ i : Fin N × Fin 3, ∑ a : Fin N → Bool,
      fderiv ℝ (symmetricMultiplier (electronicPair ((L : ℝ) + 1)) a) X
        (Pi.single i.1 (EuclideanSpace.single i.2 1)) ^ 2 ≤
      3 * N * electronicPartitionConstant / (2 * ((L : ℝ) + 1) ^ 2) := by
  have h := symmetricElectronicPartition_total_metric
    (L := (L : ℝ) + 1) (by positivity) X
  rw [Fintype.sum_prod_type]
  simp only [tsum_fintype] at h
  exact (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq
    (by simp only [div_eq_mul_inv, mul_inv_rev]; ring)

/-- The selected symmetric branch is precisely the multiplier already
used in the local compactness and photon-loss state construction. -/
theorem symmetricElectronicPartition_physical (L : ℕ) (x : Configuration N) :
    symmetricMultiplier (electronicPair ((L : ℝ) + 1)) (fun _ : Fin N => false)
      (electronicPositions x) = (physicalElectronicFamily L).multiplier x := by
  rw [symmetricElectronicPartition_retained]
  rfl

end GptLean.PhotonLocalization
