import GptLean.PhysicalFourierProduct
import GptLean.PhysicalL2FiberSum

/-!
The actual Fourier transform on a Hilbert product agrees with successive
Fourier transforms under the proved L2 Fubini map. Scalar Fourier products,
fiber coefficients and simple-function density prove the identity for all
Hilbert-valued L2 classes.
-/

noncomputable section
namespace GptLean.PhysicalFourierFubini

open MeasureTheory FourierTransform PhysicalL2HilbertSum
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

section FiberExt
variable {X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem eq_of_inner_compLpL {u v : Lp H 2 μ}
    (h : ∀ z : H, (innerSL ℂ z).compLpL 2 μ u = (innerSL ℂ z).compLpL 2 μ v) :
    u = v := by
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℂ H
  apply (PhysicalL2FiberSum.fiberCoefficients (μ := μ) b).injective
  apply lp.ext
  funext j
  simpa only [PhysicalL2FiberSum.fiberCoefficients_apply] using h (b j)
end FiberExt

variable {X Y H : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Join iterated L2 classes in the actual Hilbert product coordinates. -/
def join : Lp (Lp H 2 (volume : Measure Y)) 2 (volume : Measure X) →ₗᵢ[ℂ]
    Lp H 2 (volume : Measure (WithLp 2 (X × Y))) :=
  (Lp.compMeasurePreservingₗᵢ ℂ WithLp.ofLp
    (WithLp.volume_preserving_ofLp X Y)).comp
      PhysicalSourceFubini.curryEquiv.symm.toLinearIsometry

private theorem uncurry_tensor_ae (f : Lp ℂ 2 (volume : Measure X))
    (g : Lp H 2 (volume : Measure Y)) :
    PhysicalSourceFubini.curryEquiv.symm (tensor f g) =ᵐ[volume.prod volume]
      fun z : X × Y => f z.1 • g z.2 := by
  let u : Lp H 2 ((volume : Measure X).prod (volume : Measure Y)) :=
    PhysicalSourceFubini.curryEquiv.symm (tensor f g)
  have hu := PhysicalSourceFubini.curryEquiv_represents_ae u
  have he : PhysicalSourceFubini.curryEquiv u = tensor f g :=
    LinearIsometryEquiv.apply_symm_apply _ _
  rw [he] at hu
  apply (Measure.ae_prod_iff_ae_ae
    ((Lp.stronglyMeasurable u).measurableSet_eq_fun
      (((Lp.stronglyMeasurable f).comp_measurable measurable_fst).smul
        ((Lp.stronglyMeasurable g).comp_measurable measurable_snd)))).mpr
  filter_upwards [hu, tensor_ae f g] with x hx ht
  rw [ht] at hx
  filter_upwards [hx, Lp.coeFn_smul (f x) g] with y hy hs
  exact hy.symm.trans hs

theorem join_tensor_ae (f : Lp ℂ 2 (volume : Measure X))
    (g : Lp H 2 (volume : Measure Y)) :
    join (tensor f g) =ᵐ[volume] fun z : WithLp 2 (X × Y) => f z.fst • g z.snd := by
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (PhysicalSourceFubini.curryEquiv.symm (tensor f g))
      (WithLp.volume_preserving_ofLp X Y),
    (WithLp.volume_preserving_ofLp X Y).quasiMeasurePreserving.ae
      (uncurry_tensor_ae f g)] with z hz ht
  exact hz.trans ht

private theorem scalar_join_tensor (B : H →L[ℂ] ℂ)
    (f : Lp ℂ 2 (volume : Measure X)) (g : Lp H 2 (volume : Measure Y)) :
    B.compLpL 2 volume (join (tensor f g)) =
      PhysicalFourierProduct.product f (B.compLpL 2 volume g) := by
  apply Lp.ext
  filter_upwards [B.coeFn_compLpL (join (tensor f g)), join_tensor_ae f g,
    PhysicalFourierProduct.product_ae f (B.compLpL 2 volume g),
    (WithLp.volume_preserving_ofLp X Y).quasiMeasurePreserving.ae
      ((Measure.quasiMeasurePreserving_snd (μ := (volume : Measure X))).ae
        (B.coeFn_compLpL g))] with z hz ht hp hg
  have hg' : (B.compLpL 2 volume g) z.snd = B (g z.snd) := hg
  rw [hz, ht, hp, hg', map_smul, smul_eq_mul]

/-- Fourier factorization for a scalar spatial factor and a Hilbert-valued factor. -/
theorem fourier_join_tensor (f : Lp ℂ 2 (volume : Measure X))
    (g : Lp H 2 (volume : Measure Y)) :
    Lp.fourierTransformₗᵢ (WithLp 2 (X × Y)) H (join (tensor f g)) =
      join (tensor (Lp.fourierTransformₗᵢ X ℂ f) (Lp.fourierTransformₗᵢ Y H g)) := by
  apply eq_of_inner_compLpL
  intro z
  rw [← PhysicalL2FourierTransport.fourier_compLpL,
    scalar_join_tensor, PhysicalFourierProduct.fourier_productL2,
    scalar_join_tensor, PhysicalL2FourierTransport.fourier_compLpL]

omit [TopologicalSpace.SeparableSpace H] in
theorem fourier_tensor (f : Lp ℂ 2 (volume : Measure X)) (v : H) :
    Lp.fourierTransformₗᵢ X H (tensor f v) = tensor (Lp.fourierTransformₗᵢ X ℂ f) v :=
  PhysicalL2FourierTransport.fourier_compLpL
    ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] H →L[ℂ] H).flip v) f

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
private theorem compLpL_tensor
    (B : Lp H 2 (volume : Measure Y) →L[ℂ] Lp H 2 (volume : Measure Y))
    (f : Lp ℂ 2 (volume : Measure X)) (g : Lp H 2 (volume : Measure Y)) :
    B.compLpL 2 volume (tensor f g) = tensor f (B g) := by
  apply Lp.ext
  filter_upwards [B.coeFn_compLpL (tensor f g), tensor_ae f g, tensor_ae f (B g)]
    with x hx ht hs
  rw [hx, ht, hs, map_smul]

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
private theorem tensor_indicator {s : Set X} (hs : MeasurableSet s)
    (hμs : volume s ≠ ⊤) (g : Lp H 2 (volume : Measure Y)) :
    tensor (indicatorConstLp 2 hs hμs (1 : ℂ)) g = indicatorConstLp 2 hs hμs g := by
  apply Lp.ext
  filter_upwards [tensor_ae (indicatorConstLp 2 hs hμs (1 : ℂ)) g,
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs) (hμs := hμs) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs) (hμs := hμs) (c := g)]
    with x ht hf hg
  rw [ht, hf, hg]
  by_cases hx : x ∈ s <;> simp [hx]

/-- The joint Fourier transform is exactly the two successive transforms under Fubini. -/
theorem fourier_join (u : Lp (Lp H 2 (volume : Measure Y)) 2 (volume : Measure X)) :
    Lp.fourierTransformₗᵢ (WithLp 2 (X × Y)) H (join u) =
      join ((Lp.fourierTransformₗᵢ Y H).toLinearIsometry.toContinuousLinearMap.compLpL 2 volume
        (Lp.fourierTransformₗᵢ X (Lp H 2 (volume : Measure Y)) u)) := by
  apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (fun u : Lp (Lp H 2 (volume : Measure Y)) 2 (volume : Measure X) =>
      Lp.fourierTransformₗᵢ (WithLp 2 (X × Y)) H (join u) =
        join ((Lp.fourierTransformₗᵢ Y H).toLinearIsometry.toContinuousLinearMap.compLpL 2 volume
          (Lp.fourierTransformₗᵢ X (Lp H 2 (volume : Measure Y)) u)))
  · intro g s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst, ← tensor_indicator hs hμs.ne g,
      fourier_join_tensor, fourier_tensor, compLpL_tensor]
    rfl
  · intro f g hf hg _ hfe hge
    simp only [map_add, hfe, hge]
  · exact isClosed_eq
      ((Lp.fourierTransformₗᵢ (WithLp 2 (X × Y)) H).continuous.comp join.continuous)
      (join.continuous.comp
        (((Lp.fourierTransformₗᵢ Y H).toLinearIsometry.toContinuousLinearMap.compLpL 2 volume).continuous.comp
          (Lp.fourierTransformₗᵢ X (Lp H 2 (volume : Measure Y))).continuous))

end GptLean.PhysicalFourierFubini
