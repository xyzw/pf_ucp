import GptLean.PhysicalFockChannel

/-!
Finite creation words tensored with arbitrary scalar electronic L²
functions determine every bounded operator on the coupled model. The
proof uses actual simple-function density and the matched word density.
The full Kraus action on these simple tensors is pointwise and explicit.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory Filter Topology PhotonLocalizationFockChannel
open scoped ENNReal

variable {X H K : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

private theorem spatial_tensor_indicator {s : Set X} (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) (v : H) :
    PhysicalL2HilbertSum.tensor (indicatorConstLp 2 hs hμs (1 : ℂ)) v =
      indicatorConstLp 2 hs hμs v := by
  apply Lp.ext
  filter_upwards [PhysicalL2HilbertSum.tensor_ae (indicatorConstLp 2 hs hμs (1 : ℂ)) v,
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs) (hμs := hμs) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs) (hμs := hμs) (c := v)]
    with x ht hf hv
  rw [ht, hf, hv]
  by_cases hx : x ∈ s <;> simp [hx]

theorem ext_spatial_tensors (U V : Lp H 2 μ →L[ℂ] K)
    (h : ∀ (f : Lp ℂ 2 μ) (v : H),
      U (PhysicalL2HilbertSum.tensor f v) = V (PhysicalL2HilbertSum.tensor f v)) : U = V := by
  ext u
  apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (fun u => U u = V u)
  · intro v s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst, ← spatial_tensor_indicator hs hμs.ne v]
    exact h _ _
  · intro f g hf hg _ hfm hgm
    simp only [map_add, hfm, hgm]
  · exact isClosed_eq U.continuous V.continuous

variable (BF : StandardSymmetricFockExponential)

theorem lift_tensor (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => H) 2)
    (f : Lp ℂ 2 μ) (v : H) (n : ℕ) :
    KrausL2.lift μ U (PhysicalL2HilbertSum.tensor f v) n =
      PhysicalL2HilbertSum.tensor f (U v n) := by
  apply Lp.ext
  filter_upwards [KrausL2.lift_coordinate_ae μ U (PhysicalL2HilbertSum.tensor f v) n,
    PhysicalL2HilbertSum.tensor_ae f v, PhysicalL2HilbertSum.tensor_ae f (U v n)]
    with x h₁ h₂ h₃
  simp only [h₁, h₂, h₃, map_smul, lp.coeFn_smul, Pi.smul_apply]

include BF in
/-- Word testing includes the full electronic factor and arbitrary bounded outputs. -/
theorem ext_electronic_words (U V : Lp PhotonFock 2 μ →L[ℂ] K)
    (h : ∀ (f : Lp ℂ 2 μ) (w : List (Lp ℂ 2 photonMeasure)),
      U (PhysicalL2HilbertSum.tensor f (creationWord photonMeasure w)) =
        V (PhysicalL2HilbertSum.tensor f (creationWord photonMeasure w))) : U = V := by
  apply ext_spatial_tensors U V
  intro f v
  have he := (photonExponential BF).ext_words photonMeasure
    (U.comp (PhysicalL2HilbertSum.tensor f)) (V.comp (PhysicalL2HilbertSum.tensor f))
    (h f)
  exact congrArg (fun A : PhotonFock →L[ℂ] K => A v) he

theorem electronicFactorization_tensor
    (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
      WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (f : Lp ℂ 2 μ) (v : PhotonFock) (n : ℕ) :
    (electronicFactorization μ (photonFactorization BF)).factor j
      (PhysicalL2HilbertSum.tensor f v) n =
        PhysicalL2HilbertSum.tensor f ((photonFactorization BF).factor j v n) := by
  exact lift_tensor ((photonFactorization BF).factor j) f v n

end GptLean.PhysicalFock
