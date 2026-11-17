import GptLean.PhysicalFockCCR
import GptLean.PhysicalFockKernelLinearity
import GptLean.PhysicalFockCreationWords
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Module

/-!
Mixed canonical commutators for the actual symmetric creation operators
and their Hilbert adjoints. The supplied universal diagonal sector CCR
is polarized in the state vector and then in the one-photon kernels.
No mixed commutator or finite-word covariance is assumed.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000

private theorem sesquilinear_zero_of_diagonal
    {E W : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup W] [Module ℂ W]
    (D : E → E → W)
    (hadd₁ : ∀ f g h, D (f + g) h = D f h + D g h)
    (hadd₂ : ∀ f g h, D f (g + h) = D f g + D f h)
    (hsmul₁ : ∀ (c : ℂ) (f g : E), D (c • f) g = starRingEnd ℂ c • D f g)
    (hsmul₂ : ∀ (c : ℂ) (f g : E), D f (c • g) = c • D f g)
    (hdiag : ∀ f, D f f = 0) (f g : E) : D f g = 0 := by
  have hs : D f g + D g f = 0 := by
    have h := hdiag (f + g)
    rw [hadd₁, hadd₂, hadd₂, hdiag, hdiag] at h
    simpa only [zero_add, add_zero] using h
  have hi : Complex.I • D f g + (-Complex.I) • D g f = 0 := by
    have h := hdiag (f + Complex.I • g)
    rw [hadd₁, hadd₂, hadd₂, hdiag, hdiag] at h
    simpa only [zero_add, add_zero, hsmul₁, hsmul₂, Complex.conj_I] using h
  have hz : (2 * Complex.I) • D f g = 0 := by
    calc
      (2 * Complex.I) • D f g = Complex.I • (D f g + D g f) +
          (Complex.I • D f g + (-Complex.I) • D g f) := by module
      _ = 0 := by rw [hs, hi, smul_zero, zero_add]
  exact (smul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)

private theorem adjoint_comp_eq_of_norm
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : H →L[ℂ] K) (a : ℝ) (h : ∀ u, ‖T u‖ ^ 2 = a * ‖u‖ ^ 2) :
    T.adjoint.comp T = (a : ℂ) • ContinuousLinearMap.id ℂ H := by
  have he := (ext_inner_map (T.adjoint.comp T).toLinearMap
    ((a : ℂ) • ContinuousLinearMap.id ℂ H).toLinearMap).mp (fun u => by
      change ⟪T.adjoint (T u), u⟫_ℂ = ⟪(a : ℂ) • u, u⟫_ℂ
      rw [T.adjoint_inner_left, inner_smul_left, inner_self_eq_norm_sq_to_K,
        inner_self_eq_norm_sq_to_K]
      simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.conj_ofReal,
        Complex.ofReal_mul, Complex.ofReal_pow] using
        congrArg Complex.ofReal (h u))
  apply ContinuousLinearMap.ext
  intro u
  exact congrArg (fun L : H →ₗ[ℂ] H => L u) he

private theorem adjoint_comp_sub_eq_of_norm
    {G H K : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : G →L[ℂ] H) (T : H →L[ℂ] K) (a : ℝ)
    (h : ∀ u, ‖T u‖ ^ 2 = ‖A.adjoint u‖ ^ 2 + a * ‖u‖ ^ 2) :
    T.adjoint.comp T - A.comp A.adjoint = (a : ℂ) • ContinuousLinearMap.id ℂ H := by
  have he := (ext_inner_map (T.adjoint.comp T - A.comp A.adjoint).toLinearMap
    ((a : ℂ) • ContinuousLinearMap.id ℂ H).toLinearMap).mp (fun u => by
      change ⟪T.adjoint (T u) - A (A.adjoint u), u⟫_ℂ = ⟪(a : ℂ) • u, u⟫_ℂ
      rw [inner_sub_left, T.adjoint_inner_left, ← A.adjoint_inner_right,
        inner_smul_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
        inner_self_eq_norm_sq_to_K]
      have hh := congrArg Complex.ofReal (h u)
      simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow] at hh
      simp only [RCLike.ofReal_eq_complex_ofReal, Complex.conj_ofReal]
      exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hh))
  apply ContinuousLinearMap.ext
  intro u
  exact congrArg (fun L : H →ₗ[ℂ] H => L u) he

private theorem mixed_successor_of_diagonal
    {E G H K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (L₀ : E →ₗ[ℂ] (G →L[ℂ] H)) (L₁ : E →ₗ[ℂ] (H →L[ℂ] K))
    (hdiag : ∀ f, (L₁ f).adjoint.comp (L₁ f) - (L₀ f).comp (L₀ f).adjoint =
      ⟪f, f⟫_ℂ • ContinuousLinearMap.id ℂ H) (f g : E) :
    (L₁ f).adjoint.comp (L₁ g) - (L₀ g).comp (L₀ f).adjoint =
      ⟪f, g⟫_ℂ • ContinuousLinearMap.id ℂ H := by
  let D (f g : E) := (L₁ f).adjoint.comp (L₁ g) - (L₀ g).comp (L₀ f).adjoint -
    ⟪f, g⟫_ℂ • ContinuousLinearMap.id ℂ H
  apply sub_eq_zero.mp
  change D f g = 0
  apply sesquilinear_zero_of_diagonal D
  · intro a b c
    simp only [D, map_add, inner_add_left, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add]
    module
  · intro a b c
    simp only [D, map_add, inner_add_right, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add]
    module
  · intro c a b
    simp only [D, map_smul, map_smulₛₗ, inner_smul_left,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    module
  · intro c a b
    simp only [D, map_smul, inner_smul_right,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    module
  · intro a
    exact sub_eq_zero.mpr (hdiag a)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
  (C : CanonicalSectorCCR μ)

private def creationKernelMap (n : ℕ) :
    Lp ℂ 2 μ →ₗ[ℂ] (Sector μ n →L[ℂ] Sector μ (n + 1)) where
  toFun := creationSector μ n
  map_add' := creationSector_add μ n
  map_smul' c f := creationSector_smul μ n f c

include C

theorem sectorCCR_vacuum_diagonal (f : Lp ℂ 2 μ) :
    (annihilationSector μ 0 f).comp (creationSector μ 0 f) =
      ⟪f, f⟫_ℂ • ContinuousLinearMap.id ℂ (Sector μ 0) := by
  simpa only [annihilationSector, inner_self_eq_norm_sq_to_K,
    RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using
    adjoint_comp_eq_of_norm (creationSector μ 0 f) (‖f‖ ^ 2) (C.vacuum f)

theorem sectorCCR_successor_diagonal (n : ℕ) (f : Lp ℂ 2 μ) :
    (annihilationSector μ (n + 1) f).comp (creationSector μ (n + 1) f) -
      (creationSector μ n f).comp (annihilationSector μ n f) =
        ⟪f, f⟫_ℂ • ContinuousLinearMap.id ℂ (Sector μ (n + 1)) := by
  simpa only [annihilationSector, inner_self_eq_norm_sq_to_K,
    RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using
    adjoint_comp_sub_eq_of_norm (creationSector μ n f) (creationSector μ (n + 1) f)
      (‖f‖ ^ 2) (C.successor f n)

/-- The mixed vacuum CCR for the actual adjacent-sector operators. -/
theorem sectorCCR_vacuum (f g : Lp ℂ 2 μ) :
    (annihilationSector μ 0 f).comp (creationSector μ 0 g) =
      ⟪f, g⟫_ℂ • ContinuousLinearMap.id ℂ (Sector μ 0) := by
  let D (f g : Lp ℂ 2 μ) := (annihilationSector μ 0 f).comp (creationSector μ 0 g) -
    ⟪f, g⟫_ℂ • ContinuousLinearMap.id ℂ (Sector μ 0)
  apply sub_eq_zero.mp
  change D f g = 0
  apply sesquilinear_zero_of_diagonal D
  · intro a b c
    dsimp [D]
    rw [annihilationSector_add, inner_add_left, ContinuousLinearMap.add_comp]
    module
  · intro a b c
    dsimp [D]
    rw [creationSector_add, inner_add_right, ContinuousLinearMap.comp_add]
    module
  · intro c a b
    dsimp [D]
    rw [annihilationSector_smul, inner_smul_left, ContinuousLinearMap.smul_comp]
    module
  · intro c a b
    dsimp [D]
    rw [creationSector_smul, inner_smul_right, ContinuousLinearMap.comp_smul]
    module
  · intro a
    exact sub_eq_zero.mpr (sectorCCR_vacuum_diagonal μ C a)

/-- The mixed CCR on every positive number sector. -/
theorem sectorCCR_successor (n : ℕ) (f g : Lp ℂ 2 μ) :
    (annihilationSector μ (n + 1) f).comp (creationSector μ (n + 1) g) -
      (creationSector μ n g).comp (annihilationSector μ n f) =
        ⟪f, g⟫_ℂ • ContinuousLinearMap.id ℂ (Sector μ (n + 1)) := by
  exact mixed_successor_of_diagonal (creationKernelMap μ n) (creationKernelMap μ (n + 1))
    (fun a => sectorCCR_successor_diagonal μ C n a) f g

theorem sectorCCR_vacuum_apply (f g : Lp ℂ 2 μ) (u : Sector μ 0) :
    annihilationSector μ 0 f (creationSector μ 0 g u) = ⟪f, g⟫_ℂ • u :=
  congrArg (fun L : Sector μ 0 →L[ℂ] Sector μ 0 => L u) (sectorCCR_vacuum μ C f g)

theorem sectorCCR_successor_apply (n : ℕ) (f g : Lp ℂ 2 μ) (u : Sector μ (n + 1)) :
    annihilationSector μ (n + 1) f (creationSector μ (n + 1) g u) =
      creationSector μ n g (annihilationSector μ n f u) + ⟪f, g⟫_ℂ • u := by
  have h := congrArg (fun L : Sector μ (n + 1) →L[ℂ] Sector μ (n + 1) => L u)
    (sectorCCR_successor μ C n f g)
  change annihilationSector μ (n + 1) f (creationSector μ (n + 1) g u) -
    creationSector μ n g (annihilationSector μ n f u) = ⟪f, g⟫_ℂ • u at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- Annihilation of one actual creation applied to the actual vacuum. -/
theorem annihilation_creationWord_singleton (f g : Lp ℂ 2 μ) :
    annihilationSector μ 0 f (creationWordSector μ [g]) =
      ⟪f, g⟫_ℂ • creationWordSector μ [] :=
  sectorCCR_vacuum_apply μ C f g (vacuumSector μ)

/-- Recursive annihilation of a finite word in the actual creation operators. -/
theorem annihilation_creationWord_cons_cons (f g h : Lp ℂ 2 μ) (w : List (Lp ℂ 2 μ)) :
    annihilationSector μ (w.length + 1) f (creationWordSector μ (g :: h :: w)) =
      creationSector μ w.length g (annihilationSector μ w.length f
        (creationWordSector μ (h :: w))) + ⟪f, g⟫_ℂ • creationWordSector μ (h :: w) :=
  sectorCCR_successor_apply μ C w.length f g (creationWordSector μ (h :: w))

end GptLean.PhysicalFock
