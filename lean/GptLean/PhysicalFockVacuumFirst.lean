import GptLean.PhysicalFockVacuumGeometry
import GptLean.PhysicalChannelDual
import GptLean.PhysicalFockChannelComposition

/-!
A vacuum-first environmental coordinate map constructed from the actual
vacuum projection and the original environmental coordinates. Its normal
channel equals the original channel on all observables. This does not
identify coordinate zero of the original arbitrary Hilbert basis with
the vacuum.
-/

noncomputable section
namespace GptLean.PhysicalFock.VacuumFirst

open TensorCoordinates TensorGentle PhysicalL2HilbertSum
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true

local notation "K" => VacuumOperator.contraction photonMeasure
local notation "TensorFock" => TensorSpace PhotonFock PhotonFock

private def succEmbedding : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩

section Generic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem first_zero (u : H) (v : lp (fun _ : ℕ => H) 2) :
    (lp.single (E := fun _ : ℕ => H) 2 0 u + padding succEmbedding v) 0 = u := by
  rw [lp.coeFn_add, Pi.add_apply, lp.single_apply_self,
    padding_off succEmbedding _ 0 (by rintro ⟨n, hn⟩; exact Nat.succ_ne_zero n hn), add_zero]

private theorem first_succ (u : H) (v : lp (fun _ : ℕ => H) 2) (n : ℕ) :
    (lp.single (E := fun _ : ℕ => H) 2 0 u + padding succEmbedding v) (n + 1) = v n := by
  rw [lp.coeFn_add, Pi.add_apply,
    lp.single_apply_ne _ _ _ (Nat.succ_ne_zero n)]
  exact (zero_add _).trans (padding_at succEmbedding v n)

private theorem first_norm_sq (u : H) (v : lp (fun _ : ℕ => H) 2) :
    ‖lp.single (E := fun _ : ℕ => H) 2 0 u + padding succEmbedding v‖ ^ 2 =
      ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  have hzero : padding succEmbedding v 0 = 0 :=
    padding_off succEmbedding v 0 (by rintro ⟨n, hn⟩; exact Nat.succ_ne_zero n hn)
  rw [norm_add_sq (𝕜 := ℂ), lp.inner_single_left, hzero, inner_zero_right]
  simp only [lp.norm_single (by norm_num : 0 < (2 : ENNReal)), LinearIsometry.norm_map,
    map_zero, mul_zero, add_zero]

omit [CompleteSpace H] in
private theorem clm_eq_of_diagonal (S T : H →L[ℂ] H)
    (h : ∀ u, ⟪u, S u⟫_ℂ = ⟪u, T u⟫_ℂ) : S = T := by
  have he := (ext_inner_map S.toLinearMap T.toLinearMap).mp (fun u => by
    change ⟪S u, u⟫_ℂ = ⟪T u, u⟫_ℂ
    simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) (h u))
  exact ContinuousLinearMap.ext (fun u => LinearMap.congr_fun he u)
end Generic

private theorem norm_from_split (a b c d : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (h : a ^ 2 = b ^ 2 + c ^ 2) (hc : c ^ 2 = d ^ 2 - b ^ 2) : a = d :=
  (sq_eq_sq₀ ha hd).mp (by linarith only [h, hc])

private theorem sum_first {f : ℕ → ℂ} {a b : ℂ}
    (hzero : f 0 = a) (h : HasSum (fun n => f (n + 1)) b) : HasSum f (a + b) := by
  have hs := (hasSum_nat_add_iff 1).mp h
  simpa only [Finset.sum_range_one, hzero, add_comm] using hs

def map : TensorFock →L[ℂ] lp (fun _ : ℕ => PhotonFock) 2 :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => PhotonFock) 2 0).comp K +
    (padding succEmbedding).toContinuousLinearMap.comp
      ((environmentalCoordinates PhotonFock).toContinuousLinearMap.comp residual)

@[simp] theorem map_zero_coordinate (z : TensorFock) : map z 0 = K z := by
  exact first_zero (K z) (environmentalCoordinates PhotonFock (residual z))

@[simp] theorem map_succ_coordinate (z : TensorFock) (n : ℕ) :
    map z (n + 1) = environmentalCoordinates PhotonFock (residual z) n := by
  exact first_succ (K z) (environmentalCoordinates PhotonFock (residual z)) n

theorem map_norm (z : TensorFock) : ‖map z‖ = ‖z‖ := by
  let v := environmentalCoordinates PhotonFock (residual z)
  have h := first_norm_sq (K z) v
  have hv : ‖v‖ ^ 2 = ‖z‖ ^ 2 - ‖K z‖ ^ 2 := by
    exact (congrArg (fun r : ℝ => r ^ 2)
      ((environmentalCoordinates PhotonFock).norm_map (residual z))).trans (residual_norm_sq z)
  exact norm_from_split ‖map z‖ ‖K z‖ ‖v‖ ‖z‖ (norm_nonneg _) (norm_nonneg _) h hv

def coordinates : TensorFock →ₗᵢ[ℂ] lp (fun _ : ℕ => PhotonFock) 2 where
  toLinearMap := map.toLinearMap
  norm_map' := map_norm

@[simp] theorem coordinates_zero (z : TensorFock) : coordinates z 0 = K z :=
  map_zero_coordinate z

@[simp] theorem coordinates_succ (z : TensorFock) (n : ℕ) :
    coordinates z (n + 1) = environmentalCoordinates PhotonFock (residual z) n :=
  map_succ_coordinate z n

theorem observable_hasSum (A : PhotonFock →L[ℂ] PhotonFock) (z : TensorFock) :
    HasSum (fun n => ⟪coordinates z n, A (coordinates z n)⟫_ℂ)
      ⟪z, retainedOperator A z⟫_ℂ := by
  have h := environmentalCoordinates_observable_hasSum A (residual z)
  have ht : HasSum (fun n => ⟪coordinates z (n + 1), A (coordinates z (n + 1))⟫_ℂ)
      ⟪residual z, retainedOperator A (residual z)⟫_ℂ := by
    apply h.congr_fun
    intro n
    exact congrArg (fun v : PhotonFock => ⟪v, A v⟫_ℂ) (coordinates_succ z n)
  have hs := sum_first
    (f := fun n => ⟪coordinates z n, A (coordinates z n)⟫_ℂ)
    (a := ⟪K z, A (K z)⟫_ℂ)
    (b := ⟪residual z, retainedOperator A (residual z)⟫_ℂ)
    (congrArg (fun v : PhotonFock => ⟪v, A v⟫_ℂ) (coordinates_zero z)) ht
  exact (congrArg (fun s : ℂ => HasSum
    (fun n => ⟪coordinates z n, A (coordinates z n)⟫_ℂ) s)
    (observable_decomposition A z).symm).mp hs

open MeasureTheory PhotonLocalizationFockChannel PhotonLocalizationChannel

variable (BF : StandardSymmetricFockExponential)

def factor (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
    WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure)) : KrausIsometry PhotonFock :=
  coordinates.comp ((photonExponential BF).split photonMeasure j)

@[simp] theorem factor_zero (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
    WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure)) (u : PhotonFock) :
    factor BF j u 0 = VacuumOperator.operator photonMeasure (photonExponential BF) j u :=
  coordinates_zero _

theorem pullback_eq (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
    WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (A : PhotonFock →L[ℂ] PhotonFock) :
    PhysicalChannelDual.pullback (factor BF j) A =
      PhysicalChannelDual.pullback ((photonFactorization BF).factor j) A := by
  have hdiag (u : PhotonFock) :
      ⟪u, PhysicalChannelDual.pullback (factor BF j) A u⟫_ℂ =
        ⟪u, PhysicalChannelDual.pullback ((photonFactorization BF).factor j) A u⟫_ℂ := by
    exact ((PhysicalChannelDual.pullback_hasSum (factor BF j) A u u).unique
      (observable_hasSum A ((photonExponential BF).split photonMeasure j u))).trans
      (ChannelComposition.pullback_inner BF j A u u).symm
  exact clm_eq_of_diagonal _ _ hdiag

end GptLean.PhysicalFock.VacuumFirst
