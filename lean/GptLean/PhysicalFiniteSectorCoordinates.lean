import GptLean.PhysicalFockElectronic
import GptLean.Repair.TraceChannel

/-!
Actual finite photon-number coordinates on spatial L2. The coordinate
map is evaluation in the Fock Hilbert sum. Parseval proves that the
number-supported subspace embeds isometrically in the finite Hilbert
product of its spatial sector spaces.
-/

noncomputable section

namespace GptLean.PhysicalFiniteSectorCoordinates

open MeasureTheory PhysicalFock Filter Topology
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

variable (K : ℕ → Type*) [∀ n, NormedAddCommGroup (K n)]
  [∀ n, InnerProductSpace ℂ (K n)]
  {X : Type*} [MeasurableSpace X] (μ : Measure X)

def coordinate (n : ℕ) : ElectronicSpace K μ →L[ℂ] Lp (K n) 2 μ :=
  (lp.evalCLM ℂ K 2 n).compLpL 2 μ

theorem coordinate_ae (n : ℕ) (u : ElectronicSpace K μ) :
    coordinate K μ n u =ᵐ[μ] fun x => u x n :=
  (lp.evalCLM ℂ K 2 n).coeFn_compLpL u

theorem coordinate_norm_sq (n : ℕ) (u : ElectronicSpace K μ) :
    ‖coordinate K μ n u‖ ^ 2 = ‖electronicSector K μ n u‖ ^ 2 := by
  have h := Repair.toL2_norm_sq (Lp.memLp (coordinate K μ n u))
  simp only [Lp.toLp_coeFn] at h
  rw [h, electronicSector_mass_integral]
  apply integral_congr_ae
  filter_upwards [coordinate_ae K μ n u] with x hx
  rw [hx]

theorem coordinates_mass_hasSum (u : ElectronicSpace K μ) :
    HasSum (fun n => ‖coordinate K μ n u‖ ^ 2) (‖u‖ ^ 2) := by
  simpa only [coordinate_norm_sq] using electronicSector_mass_hasSum K μ u

def numberSubspace (M : ℕ) : Submodule ℂ (ElectronicSpace K μ) where
  carrier := {u | ∀ n, M < n → coordinate K μ n u = 0}
  zero_mem' := by intro n _; exact map_zero _
  add_mem' := by intro u v hu hv n hn; rw [map_add, hu n hn, hv n hn, add_zero]
  smul_mem' := by intro c u hu n hn; rw [map_smul, hu n hn, smul_zero]

theorem numberSubspace_closed (M : ℕ) :
    IsClosed (numberSubspace K μ M : Set (ElectronicSpace K μ)) := by
  change IsClosed {u | ∀ n, M < n → coordinate K μ n u = 0}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun n => isClosed_iInter fun _ =>
    isClosed_eq (coordinate K μ n).continuous continuous_const

instance numberSubspaceComplete [∀ n, CompleteSpace (K n)] (M : ℕ) :
    CompleteSpace (numberSubspace K μ M) :=
  (numberSubspace_closed K μ M).completeSpace_coe

theorem finite_coordinates_mass (M : ℕ) (u : numberSubspace K μ M) :
    (∑ m : Fin (M + 1), ‖coordinate K μ m.val u.val‖ ^ 2) = ‖u‖ ^ 2 := by
  calc
    _ = ∑ n ∈ Finset.range (M + 1), ‖coordinate K μ n u.val‖ ^ 2 :=
      Fin.sum_univ_eq_sum_range _ _
    _ = ∑' n, ‖coordinate K μ n u.val‖ ^ 2 := by
      symm
      apply tsum_eq_sum
      intro n hn
      have hMn : M < n := by
        have hnot : ¬ n < M + 1 := by simpa only [Finset.mem_range] using hn
        omega
      rw [u.property n hMn, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    _ = _ := (coordinates_mass_hasSum K μ u.val).tsum_eq

/-- The actual finite-sector coordinate embedding, with the Hilbert product norm. -/
def coordinates (M : ℕ) : numberSubspace K μ M →ₗᵢ[ℂ]
    PiLp 2 (fun m : Fin (M + 1) => Lp (K m.val) 2 μ) where
  toFun u := WithLp.toLp 2 (fun m => coordinate K μ m.val u.val)
  map_add' u v := by
    apply (WithLp.ext_iff 2).mpr
    funext m
    exact (coordinate K μ m.val).map_add u.val v.val
  map_smul' c u := by
    apply (WithLp.ext_iff 2).mpr
    funext m
    exact (coordinate K μ m.val).map_smul c u.val
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2]
    exact finite_coordinates_mass K μ M u

@[simp] theorem coordinates_apply (M : ℕ) (u : numberSubspace K μ M)
    (m : Fin (M + 1)) : coordinates K μ M u m = coordinate K μ m.val u.val := rfl

private theorem cutoff_coordinate_zero (M n : ℕ) (hMn : M < n) (u : Space K) :
    cutoff K M u n = 0 := by
  simp only [cutoff, sum_apply, lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  apply sector_coordinate_ne
  have hjM : j < M + 1 := Finset.mem_range.mp hj
  omega

/-- Every actual number-cutoff vector belongs to the constructed finite-coordinate space. -/
theorem cutoff_mem (M : ℕ) (u : ElectronicSpace K μ) :
    (cutoff K M).compLpL 2 μ u ∈ numberSubspace K μ M := by
  intro n hn
  apply Lp.ext
  filter_upwards [coordinate_ae K μ n ((cutoff K M).compLpL 2 μ u),
    (cutoff K M).coeFn_compLpL u, Lp.coeFn_zero (K n) 2 μ] with x hx hy hz
  rw [hx, hy, cutoff_coordinate_zero K M n hn, hz]
  rfl

end GptLean.PhysicalFiniteSectorCoordinates
