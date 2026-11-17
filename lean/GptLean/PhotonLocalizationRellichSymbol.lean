import GptLean.PhotonLocalizationLocalFormsCutoff
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The actual joint H½ Fourier symbol is controlled by the free
electronic kinetic and photon radiation symbol in every finite sector. -/

namespace GptLean.PhotonLocalization

open GptLean.SymmetricLift

/-- Scalar form of the joint fractional coercivity inequality. -/
theorem joint_fractional_symbol_le {A B : Type*} [Fintype A] [Fintype B]
    (e : A → ℝ) (p : B → ℝ) (hp : ∀ j, 0 ≤ p j) :
    Real.sqrt (1 + (∑ i, e i ^ 2) + ∑ j, p j ^ 2) ≤
      1 + (∑ i, e i ^ 2) + ∑ j, p j := by
  have he : 0 ≤ ∑ i, e i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hp0 : 0 ≤ ∑ j, p j := Finset.sum_nonneg fun j _ => hp j
  have hp2 : (∑ j, p j ^ 2) ≤ (∑ j, p j) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => hp j
  have hroot := Real.sq_sqrt (by positivity : 0 ≤ 1 + (∑ i, e i ^ 2) + ∑ j, p j ^ 2)
  have hnonneg := Real.sqrt_nonneg (1 + (∑ i, e i ^ 2) + ∑ j, p j ^ 2)
  nlinarith [sq_nonneg (∑ i, e i ^ 2), mul_nonneg he hp0]

abbrev PhotonSectorPosition (N m : ℕ) := Configuration (N + m)

noncomputable def sectorFreeSymbol (N m : ℕ) (x : PhotonSectorPosition N m) : ℝ :=
  1 + (∑ i : Fin N, ‖particle x (Fin.castAdd m i)‖ ^ 2) +
    ∑ j : Fin m, ‖particle x (Fin.natAdd N j)‖

noncomputable def sectorHalfSymbol (N m : ℕ) (x : PhotonSectorPosition N m) : ℝ :=
  Real.sqrt (1 + ‖x‖ ^ 2)

theorem sector_norm_sq (N m : ℕ) (x : PhotonSectorPosition N m) :
    ‖x‖ ^ 2 = (∑ i : Fin N, ‖particle x (Fin.castAdd m i)‖ ^ 2) +
      ∑ j : Fin m, ‖particle x (Fin.natAdd N j)‖ ^ 2 := by
  have he : ‖x‖ ^ 2 = ∑ i : Fin (N + m), ‖particle x i‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [he, Fin.sum_univ_add]

theorem sector_symbol_coercivity (N m : ℕ) (x : PhotonSectorPosition N m) :
    sectorHalfSymbol N m x ≤ sectorFreeSymbol N m x := by
  unfold sectorHalfSymbol sectorFreeSymbol
  rw [sector_norm_sq]
  simpa only [add_assoc] using joint_fractional_symbol_le
    (fun i : Fin N => ‖particle x (Fin.castAdd m i)‖)
    (fun j : Fin m => ‖particle x (Fin.natAdd N j)‖) (fun _ => norm_nonneg _)

theorem sectorFreeSymbol_nonneg (N m : ℕ) (x : PhotonSectorPosition N m) :
    0 ≤ sectorFreeSymbol N m x := by unfold sectorFreeSymbol; positivity

/-- The actual bounded region in a fixed finite photon sector. -/
def sectorConfigurationRegion (N m : ℕ) (L r : ℝ) : Set (PhotonSectorPosition N m) :=
  {x | (∀ i : Fin N, ‖particle x (Fin.castAdd m i)‖ ≤ 2 * L) ∧
    ∀ j : Fin m, ‖particle x (Fin.natAdd N j)‖ ≤ 2 * r}

theorem sectorConfigurationRegion_bounded (N m : ℕ) {L r : ℝ}
    (hL : 0 ≤ L) (hr : 0 ≤ r) :
    Bornology.IsBounded (sectorConfigurationRegion N m L r) := by
  apply (Metric.isBounded_closedBall (x := (0 : PhotonSectorPosition N m))
    (r := Real.sqrt ((N : ℝ) * (2 * L) ^ 2 + (m : ℝ) * (2 * r) ^ 2))).subset
  intro x hx
  change dist x 0 ≤ _
  rw [dist_zero_right]
  have he := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hx.1 i)
  have hp := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hx.2 j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at he hp
  have hsq : ‖x‖ ^ 2 ≤ (N : ℝ) * (2 * L) ^ 2 + (m : ℝ) * (2 * r) ^ 2 := by
    rw [sector_norm_sq]
    exact add_le_add he hp
  have hroot := Real.sq_sqrt (by positivity :
    0 ≤ (N : ℝ) * (2 * L) ^ 2 + (m : ℝ) * (2 * r) ^ 2)
  nlinarith [Real.sqrt_nonneg ((N : ℝ) * (2 * L) ^ 2 + (m : ℝ) * (2 * r) ^ 2),
    norm_nonneg x]

end GptLean.PhotonLocalization
