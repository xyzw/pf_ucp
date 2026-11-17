import GptLean.PhysicalFockElectronic
import GptLean.PhotonLocalizationFockChannel

/-!
Pointwise lifting of an actual countable Kraus isometry through electronic L².

Each coordinate is the ordinary bounded-operator action on L². Integrating
the pointwise Parseval identity proves that their Hilbert sum is an
isometry. Thus the electronic factor is constructed, rather than supplied
as another Fock-factorization premise.
-/

noncomputable section
namespace GptLean.PhysicalFock.KrausL2

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

variable {X H K : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => K) 2)

def coordinate (n : ℕ) : Lp H 2 μ →L[ℂ] Lp K 2 μ :=
  ((lp.evalCLM ℂ (fun _ : ℕ => K) 2 n).comp U.toContinuousLinearMap).compLpL 2 μ

theorem coordinate_ae (n : ℕ) (u : Lp H 2 μ) :
    coordinate μ U n u =ᵐ[μ] fun x => U (u x) n :=
  ((lp.evalCLM ℂ (fun _ : ℕ => K) 2 n).comp U.toContinuousLinearMap).coeFn_compLpL u

theorem coordinate_norm_sq (n : ℕ) (u : Lp H 2 μ) :
    ‖coordinate μ U n u‖ ^ 2 = ∫ x, ‖U (u x) n‖ ^ 2 ∂μ := by
  let : InnerProductSpace ℝ K := InnerProductSpace.rclikeToReal ℂ K
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [coordinate_ae μ U n u] with x hx
  exact congrArg (fun v : K => ‖v‖ ^ 2) hx

theorem coordinate_mass_hasSum (u : Lp H 2 μ) :
    HasSum (fun n => ‖coordinate μ U n u‖ ^ 2) (‖u‖ ^ 2) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  have hi : Integrable (fun x => ‖u x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => ‖U (u x) n‖ ^ 2) μ :=
    (((lp.evalCLM ℂ (fun _ : ℕ => K) 2 n).continuous.comp
      U.continuous).comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).norm.pow 2
  have hs (x : X) : HasSum (fun n => ‖U (u x) n‖ ^ 2) (‖u x‖ ^ 2) := by
    simpa only [U.norm_map] using PhysicalFock.coordinate_mass_hasSum (fun _ : ℕ => K) (U (u x))
  have h : HasSum (fun n => ∫ x, ‖U (u x) n‖ ^ 2 ∂μ) (∫ x, ‖u x‖ ^ 2 ∂μ) :=
    hasSum_integral_of_dominated_convergence
      (fun n x => ‖U (u x) n‖ ^ 2) hm
      (fun n => ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]))
      (ae_of_all _ (fun x => (hs x).summable))
      (show Integrable (fun x => ∑' n, ‖U (u x) n‖ ^ 2) μ from by
        simpa only [(hs _).tsum_eq] using hi)
      (ae_of_all _ hs)
  simpa only [← coordinate_norm_sq, ← PhotonKernelLocalization.l2_norm_sq_eq_integral] using h

def output (u : Lp H 2 μ) : lp (fun _ : ℕ => Lp K 2 μ) 2 :=
  ⟨fun n => coordinate μ U n u,
    memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (coordinate_mass_hasSum μ U u).summable)⟩

@[simp] theorem output_coordinate (u : Lp H 2 μ) (n : ℕ) :
    output μ U u n = coordinate μ U n u := rfl

theorem output_norm (u : Lp H 2 μ) : ‖output μ U u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact (PhysicalFock.coordinate_mass_hasSum (fun _ : ℕ => Lp K 2 μ) (output μ U u)).unique
    (coordinate_mass_hasSum μ U u)

/-- The tensor lift of the same countable Kraus isometry. -/
def lift : Lp H 2 μ →ₗᵢ[ℂ] lp (fun _ : ℕ => Lp K 2 μ) 2 where
  toLinearMap :=
    { toFun := output μ U
      map_add' u v := by
        apply lp.ext
        funext n
        exact map_add (coordinate μ U n) u v
      map_smul' c u := by
        apply lp.ext
        funext n
        exact map_smul (coordinate μ U n) c u }
  norm_map' := output_norm μ U

@[simp] theorem lift_coordinate (u : Lp H 2 μ) (n : ℕ) :
    lift μ U u n = coordinate μ U n u := rfl

theorem lift_coordinate_ae (u : Lp H 2 μ) (n : ℕ) :
    lift μ U u n =ᵐ[μ] fun x => U (u x) n := coordinate_ae μ U n u

/-- Electronic scalar multiplication commutes with every actual Kraus coordinate. -/
theorem lift_scalar_ae (φ : X → ℂ) (u v : Lp H 2 μ)
    (hv : v =ᵐ[μ] fun x => φ x • u x) (n : ℕ) :
    lift μ U v n =ᵐ[μ] fun x => φ x • lift μ U u n x := by
  filter_upwards [lift_coordinate_ae μ U v n, lift_coordinate_ae μ U u n, hv]
    with x hx hy hz
  calc
    lift μ U v n x = U (v x) n := hx
    _ = U (φ x • u x) n := congrArg (fun w : H => U w n) hz
    _ = φ x • U (u x) n := by rw [map_smul]; rfl
    _ = φ x • lift μ U u n x := congrArg (φ x • ·) hy.symm

/-- A bounded intertwining identity of the actual fiber maps remains true after electronic lifting. -/
theorem lift_intertwines (A : H →L[ℂ] H) (B : K →L[ℂ] K)
    (h : ∀ v n, U (A v) n = B (U v n)) (u : Lp H 2 μ) (n : ℕ) :
    lift μ U (A.compLpL 2 μ u) n = B.compLpL 2 μ (lift μ U u n) := by
  apply Lp.ext
  filter_upwards [lift_coordinate_ae μ U (A.compLpL 2 μ u) n,
    lift_coordinate_ae μ U u n, A.coeFn_compLpL u,
    B.coeFn_compLpL (lift μ U u n)] with x h₁ h₂ h₃ h₄
  exact h₁.trans ((congrArg (fun v : H => U v n) h₃).trans
    ((h (u x) n).trans ((congrArg B h₂.symm).trans h₄.symm)))

end GptLean.PhysicalFock.KrausL2

namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationFockChannel
open scoped ENNReal

variable {X h H : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Any physically matched photon factorization acts pointwise on the same electronic L² model. -/
def electronicFactorization (F : FockFactorization h H) : FockFactorization h (Lp H 2 μ) where
  factor j := KrausL2.lift μ (F.factor j)

theorem electronicFactorization_ae (F : FockFactorization h H)
    (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (u : Lp H 2 μ) (n : ℕ) :
    (electronicFactorization μ F).factor j u n =ᵐ[μ] fun x => F.factor j (u x) n :=
  KrausL2.lift_coordinate_ae μ (F.factor j) u n

end GptLean.PhysicalFock
