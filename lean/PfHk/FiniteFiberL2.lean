import GptLean.PhotonKernelLocalization
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Finite Hilbert sums of actual L2 functions. The construction retains
the coordinate representatives and proves their exact squared-norm sum. -/

noncomputable section
namespace PfHk.FiniteFiberL2

open MeasureTheory
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types true

variable {S X H : Type*} [Fintype S] [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}

abbrev Fiber := PiLp 2 (fun _ : S => H)

def bundle (u : S → Lp H 2 μ) : Lp (Fiber (S := S) (H := H)) 2 μ :=
  (MemLp.of_eval_piLp (fun s => Lp.memLp (u s))).toLp
    (fun x => WithLp.toLp 2 (fun s => u s x))

omit [InnerProductSpace ℂ H] in
theorem bundle_ae (u : S → Lp H 2 μ) :
    (bundle u : X → Fiber (S := S) (H := H)) =ᵐ[μ]
      fun x => WithLp.toLp 2 (fun s => u s x) :=
  (MemLp.of_eval_piLp (fun s => Lp.memLp (u s))).coeFn_toLp

omit [InnerProductSpace ℂ H] in
theorem bundle_apply_ae (u : S → Lp H 2 μ) (s : S) :
    (fun x => bundle u x s) =ᵐ[μ] u s :=
  (bundle_ae u).mono fun _ hx => congrArg (fun z : Fiber (S := S) (H := H) => z s) hx

omit [InnerProductSpace ℂ H] in
theorem norm_sq_ae (u : S → Lp H 2 μ) :
    (fun x => ‖bundle u x‖ ^ 2) =ᵐ[μ] fun x => ∑ s, ‖u s x‖ ^ 2 := by
  filter_upwards [bundle_ae u] with x hx
  rw [hx, PiLp.norm_sq_eq_of_L2]

theorem norm_sq (u : S → Lp H 2 μ) : ‖bundle u‖ ^ 2 = ∑ s, ‖u s‖ ^ 2 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [GptLean.PhotonKernelLocalization.l2_norm_sq_eq_integral]
  rw [integral_congr_ae (norm_sq_ae u)]
  rw [integral_finsetSum _ (fun s _ =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (u s))).mp (Lp.memLp (u s)))]
  exact Finset.sum_congr rfl fun s _ =>
    (GptLean.PhotonKernelLocalization.l2_norm_sq_eq_integral (u s)).symm

omit [InnerProductSpace ℂ H] in
theorem bundle_add (u v : S → Lp H 2 μ) : bundle (u + v) = bundle u + bundle v := by
  apply Lp.ext
  filter_upwards [bundle_ae (u + v), bundle_ae u, bundle_ae v,
    Lp.coeFn_add (bundle u) (bundle v),
    ae_all_iff.mpr (fun s => Lp.coeFn_add (u s) (v s))] with x huv hu hv ha hc
  rw [huv, ha, Pi.add_apply, hu, hv]
  apply PiLp.ext
  intro s
  exact hc s

theorem bundle_smul (c : ℂ) (u : S → Lp H 2 μ) : bundle (c • u) = c • bundle u := by
  apply Lp.ext
  filter_upwards [bundle_ae (c • u), bundle_ae u, Lp.coeFn_smul c (bundle u),
    ae_all_iff.mpr (fun s => Lp.coeFn_smul c (u s))] with x hcu hu hc hs
  rw [hcu, hc, Pi.smul_apply, hu]
  apply PiLp.ext
  intro s
  exact hs s

omit [InnerProductSpace ℂ H] in
theorem bundle_zero : bundle (0 : S → Lp H 2 μ) = 0 := by
  apply Lp.ext
  filter_upwards [bundle_ae (0 : S → Lp H 2 μ),
    Lp.coeFn_zero (Fiber (S := S) (H := H)) 2 μ,
    ae_all_iff.mpr (fun _ : S => Lp.coeFn_zero H 2 μ)] with x hb hz hs
  rw [hb, hz]
  apply PiLp.ext
  intro s
  exact hs s

omit [InnerProductSpace ℂ H] in
theorem bundle_injective : Function.Injective (bundle (S := S) (H := H) (μ := μ)) := by
  intro u v huv
  funext s
  apply Lp.ext
  filter_upwards [bundle_apply_ae u s, bundle_apply_ae v s] with x hu hv
  exact hu.symm.trans ((congrArg (fun z : Lp (Fiber (S := S) (H := H)) 2 μ => z x s) huv).trans hv)

def isometry : PiLp 2 (fun _ : S => Lp H 2 μ) →ₗᵢ[ℂ]
    Lp (Fiber (S := S) (H := H)) 2 μ where
  toFun u := bundle (fun s => u s)
  map_add' u v := by
    change bundle (WithLp.ofLp u + WithLp.ofLp v) = _
    exact bundle_add _ _
  map_smul' c u := by
    change bundle (c • WithLp.ofLp u) = _
    exact bundle_smul c _
  norm_map' u := by
    change ‖bundle (WithLp.ofLp u)‖ = ‖u‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq, PiLp.norm_sq_eq_of_L2]

def coordinate (s : S) : Lp (Fiber (S := S) (H := H)) 2 μ →L[ℂ] Lp H 2 μ :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : S => H) s).compLpL 2 μ

theorem coordinate_bundle (u : S → Lp H 2 μ) (s : S) : coordinate s (bundle u) = u s := by
  apply Lp.ext
  exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : S => H) s).coeFn_compLpL (bundle u)).trans
    (bundle_apply_ae u s)

theorem bundle_coordinate (u : Lp (Fiber (S := S) (H := H)) 2 μ) :
    bundle (fun s => coordinate s u) = u := by
  apply Lp.ext
  filter_upwards [bundle_ae (fun s => coordinate s u),
    ae_all_iff.mpr (fun s => (PiLp.proj (𝕜 := ℂ) 2 (fun _ : S => H) s).coeFn_compLpL u)]
    with x hb hc
  rw [hb]
  apply PiLp.ext
  intro s
  exact hc s

end PfHk.FiniteFiberL2
