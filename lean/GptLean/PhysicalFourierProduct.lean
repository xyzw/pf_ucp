import GptLean.PhysicalL2FourierTransport
import GptLean.PhysicalFockKernelLinearity
import Mathlib.MeasureTheory.Integral.Prod

/-!
The Fourier integral of a product of independent coordinates factors
into its one-coordinate Fourier integrals. The coordinate transport is
the actual volume-preserving Hilbert product equivalence.
-/

noncomputable section

namespace GptLean.PhysicalFourierProduct

open MeasureTheory FourierTransform PhysicalFock
open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency.types true

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- The factorization is valid for the actual Fourier integral, with no normalizing factor. -/
theorem fourier_product (f : X → ℂ) (g : Y → ℂ) (ξ : WithLp 2 (X × Y)) :
    𝓕 (fun z : WithLp 2 (X × Y) => f z.fst * g z.snd) ξ =
      𝓕 f ξ.fst * 𝓕 g ξ.snd := by
  rw [Real.fourier_eq, ← (WithLp.volume_preserving_toLp X Y).integral_comp
    (MeasurableEquiv.toLp 2 (X × Y)).measurableEmbedding]
  simp only [WithLp.prod_inner_apply, neg_add_rev,
    AddChar.map_add_eq_mul, Circle.smul_def, Circle.coe_mul, WithLp.toLp_fst, WithLp.toLp_snd,
    smul_eq_mul]
  have he : (fun z : X × Y =>
      ((Real.fourierChar (-inner ℝ z.2 ξ.snd) : Circle) : ℂ) *
        ((Real.fourierChar (-inner ℝ z.1 ξ.fst) : Circle) : ℂ) * (f z.1 * g z.2)) =
      (fun z : X × Y =>
        (((Real.fourierChar (-inner ℝ z.1 ξ.fst) : Circle) : ℂ) * f z.1) *
        (((Real.fourierChar (-inner ℝ z.2 ξ.snd) : Circle) : ℂ) * g z.2)) := by
    funext z
    ring
  change (∫ z : X × Y,
      ((Real.fourierChar (-inner ℝ z.2 ξ.snd) : Circle) : ℂ) *
        ((Real.fourierChar (-inner ℝ z.1 ξ.fst) : Circle) : ℂ) * (f z.1 * g z.2)) = _
  rw [he]
  exact integral_prod_mul
    (fun x : X => ((Real.fourierChar (-inner ℝ x ξ.fst) : Circle) : ℂ) * f x)
    (fun y : Y => ((Real.fourierChar (-inner ℝ y ξ.snd) : Circle) : ℂ) * g y)


private def productLeft (g : Lp ℂ 2 (volume : Measure Y)) :
    Lp ℂ 2 (volume : Measure X) →L[ℂ]
      Lp ℂ 2 ((volume : Measure X).prod (volume : Measure Y)) :=
  LinearMap.mkContinuous
    { toFun f := productL2 f g
      map_add' f h := productL2_add_left f h g
      map_smul' c f := productL2_smul_left f c g }
    ‖g‖ (fun f => by
      change ‖productL2 f g‖ ≤ ‖g‖ * ‖f‖
      rw [productL2_norm, mul_comm])

private def pullProduct : Lp ℂ 2 ((volume : Measure X).prod (volume : Measure Y)) →ₗᵢ[ℂ]
    Lp ℂ 2 (volume : Measure (WithLp 2 (X × Y))) :=
  Lp.compMeasurePreservingₗᵢ ℂ WithLp.ofLp (WithLp.volume_preserving_ofLp X Y)

/-- The actual product of independent L2 classes in Hilbert product coordinates. -/
def product (f : Lp ℂ 2 (volume : Measure X)) (g : Lp ℂ 2 (volume : Measure Y)) :
    Lp ℂ 2 (volume : Measure (WithLp 2 (X × Y))) := pullProduct (productL2 f g)

theorem product_ae (f : Lp ℂ 2 (volume : Measure X))
    (g : Lp ℂ 2 (volume : Measure Y)) :
    product f g =ᵐ[volume] fun z => f z.fst * g z.snd := by
  filter_upwards [Lp.coeFn_compMeasurePreserving (productL2 f g)
      (WithLp.volume_preserving_ofLp X Y),
    (WithLp.volume_preserving_ofLp X Y).quasiMeasurePreserving.ae (productL2_ae f g)]
    with z hz ht
  exact hz.trans ht

private theorem ae_fst {P : X → Prop} (h : ∀ᵐ x ∂volume, P x) :
    ∀ᵐ z : WithLp 2 (X × Y) ∂volume, P z.fst :=
  (WithLp.volume_preserving_ofLp X Y).quasiMeasurePreserving.ae
    ((Measure.quasiMeasurePreserving_fst (ν := (volume : Measure Y))).ae h)

private theorem ae_snd {P : Y → Prop} (h : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ z : WithLp 2 (X × Y) ∂volume, P z.snd :=
  (WithLp.volume_preserving_ofLp X Y).quasiMeasurePreserving.ae
    ((Measure.quasiMeasurePreserving_snd (μ := (volume : Measure X))).ae h)

private theorem product_toLp (f : SchwartzMap X ℂ) (g : SchwartzMap Y ℂ)
    (s : SchwartzMap (WithLp 2 (X × Y)) ℂ)
    (hs : ∀ z, s z = f z.fst * g z.snd) :
    product (f.toLp 2 volume) (g.toLp 2 volume) = s.toLp 2 volume := by
  apply Lp.ext
  filter_upwards [product_ae (X := X) (Y := Y) (f.toLp 2 volume) (g.toLp 2 volume),
    s.coeFn_toLp 2 volume, ae_fst (Y := Y) (f.coeFn_toLp 2 volume),
    ae_snd (X := X) (g.coeFn_toLp 2 volume)] with z hz ht hf hg
  exact hz.trans ((congrArg₂ (· * ·) hf hg).trans ((hs z).symm.trans ht.symm))

private theorem fourier_toLp (f : SchwartzMap X ℂ) :
    Lp.fourierTransformₗᵢ X ℂ (f.toLp 2 volume) = (𝓕 f).toLp 2 volume :=
  SchwartzMap.toLp_fourier_eq f

private theorem product_schwartz_of_eq (f : SchwartzMap X ℂ) (g : SchwartzMap Y ℂ)
    (s : SchwartzMap (WithLp 2 (X × Y)) ℂ)
    (hs : ∀ z, s z = f z.fst * g z.snd) :
    Lp.fourierTransformₗᵢ (WithLp 2 (X × Y)) ℂ (product (f.toLp 2) (g.toLp 2)) =
      product (Lp.fourierTransformₗᵢ X ℂ (f.toLp 2))
        (Lp.fourierTransformₗᵢ Y ℂ (g.toLp 2)) := by
  have hp := product_toLp f g s hs
  have hF : ∀ ξ, (𝓕 s) ξ = (𝓕 f) ξ.fst * (𝓕 g) ξ.snd := by
    intro ξ
    have he : (s : WithLp 2 (X × Y) → ℂ) = fun z => f z.fst * g z.snd := funext hs
    change 𝓕 (s : WithLp 2 (X × Y) → ℂ) ξ = _
    rw [he]
    exact fourier_product f g ξ
  exact (congrArg (Lp.fourierTransformₗᵢ (WithLp 2 (X × Y)) ℂ) hp).trans
    ((fourier_toLp s).trans
      ((product_toLp (𝓕 f) (𝓕 g) (𝓕 s) hF).symm.trans
        (congrArg₂ (product (X := X) (Y := Y))
          (fourier_toLp f).symm (fourier_toLp g).symm)))

private theorem product_schwartz (f : SchwartzMap X ℂ) (g : SchwartzMap Y ℂ)
    (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) :
    Lp.fourierTransformₗᵢ (WithLp 2 (X × Y)) ℂ (product (f.toLp 2) (g.toLp 2)) =
      product (Lp.fourierTransformₗᵢ X ℂ (f.toLp 2))
        (Lp.fourierTransformₗᵢ Y ℂ (g.toLp 2)) := by
  let h : WithLp 2 (X × Y) → ℂ := fun z => f z.fst * g z.snd
  have hs : HasCompactSupport h := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((WithLp.homeomorphProd 2 X Y).isClosedEmbedding.isCompact_preimage (hsf.prod hsg))
    intro z hz
    have hz' : f z.fst ≠ 0 ∧ g z.snd ≠ 0 := mul_ne_zero_iff.mp hz
    exact ⟨subset_tsupport _ hz'.1, subset_tsupport _ hz'.2⟩
  have hd : ContDiff ℝ (⊤ : ℕ∞) h :=
    (f.smooth _ |>.comp (WithLp.fstL 2 ℝ X Y).contDiff).mul
      (g.smooth _ |>.comp (WithLp.sndL 2 ℝ X Y).contDiff)
  let s := hs.toSchwartzMap hd
  exact product_schwartz_of_eq f g s (fun _ => rfl)

private theorem dense_rect {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {S : Set A} {T : Set B} (hS : Dense S) (hT : Dense T) (P : A → B → Prop)
    (hleft : ∀ b, IsClosed {a | P a b}) (hright : ∀ a, IsClosed {b | P a b})
    (h : ∀ a ∈ S, ∀ b ∈ T, P a b) (a : A) (b : B) : P a b := by
  refine hS.induction ?_ (hleft b) a
  intro x hx
  exact hT.induction (fun y hy => h x hx y hy) (hright x) b

/-- Fourier factorization extends from smooth compact representatives to all L2 classes. -/
theorem fourier_productL2 (f : Lp ℂ 2 (volume : Measure X))
    (g : Lp ℂ 2 (volume : Measure Y)) :
    Lp.fourierTransformₗᵢ (WithLp 2 (X × Y)) ℂ (product f g) =
      product (Lp.fourierTransformₗᵢ X ℂ f) (Lp.fourierTransformₗᵢ Y ℂ g) := by
  let P (f : Lp ℂ 2 (volume : Measure X)) (g : Lp ℂ 2 (volume : Measure Y)) : Prop :=
    Lp.fourierTransformₗᵢ (WithLp 2 (X × Y)) ℂ (product f g) =
      product (Lp.fourierTransformₗᵢ X ℂ f) (Lp.fourierTransformₗᵢ Y ℂ g)
  have hc_left (g) : IsClosed {f | P f g} :=
    isClosed_eq
      ((Lp.fourierTransformₗᵢ (WithLp 2 (X × Y)) ℂ).continuous.comp
        (pullProduct.continuous.comp (productLeft g).continuous))
      ((pullProduct.continuous.comp
        (productLeft (Lp.fourierTransformₗᵢ Y ℂ g)).continuous).comp
          (Lp.fourierTransformₗᵢ X ℂ).continuous)
  have hc_right (f) : IsClosed {g | P f g} :=
    isClosed_eq
      ((Lp.fourierTransformₗᵢ (WithLp 2 (X × Y)) ℂ).continuous.comp
        (pullProduct.continuous.comp (productL2Right f).continuous))
      ((pullProduct.continuous.comp
        (productL2Right (Lp.fourierTransformₗᵢ X ℂ f)).continuous).comp
          (Lp.fourierTransformₗᵢ Y ℂ).continuous)
  have hX := Lp.dense_hasCompactSupport_contDiff (E := X) (F := ℂ)
    (μ := volume) (p := 2) (by norm_num)
  have hY := Lp.dense_hasCompactSupport_contDiff (E := Y) (F := ℂ)
    (μ := volume) (p := 2) (by norm_num)
  apply dense_rect hX hY P hc_left hc_right ?_ f g
  rintro f ⟨φ, hf, hφs, hφd⟩ g ⟨ψ, hg, hψs, hψd⟩
  let φs := hφs.toSchwartzMap hφd
  let ψs := hψs.toSchwartzMap hψd
  have he_f : f = φs.toLp 2 volume := Lp.ext (hf.trans (φs.coeFn_toLp 2 volume).symm)
  have he_g : g = ψs.toLp 2 volume := Lp.ext (hg.trans (ψs.coeFn_toLp 2 volume).symm)
  exact (congrArg₂ P he_f he_g).mpr (product_schwartz φs ψs hφs hψs)

/-- The same tensor factorization holds for photon position coordinates. -/
theorem fourierInv_productL2 (f : Lp ℂ 2 (volume : Measure X))
    (g : Lp ℂ 2 (volume : Measure Y)) :
    (Lp.fourierTransformₗᵢ (WithLp 2 (X × Y)) ℂ).symm (product f g) =
      product ((Lp.fourierTransformₗᵢ X ℂ).symm f) ((Lp.fourierTransformₗᵢ Y ℂ).symm g) := by
  apply (Lp.fourierTransformₗᵢ (WithLp 2 (X × Y)) ℂ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, fourier_productL2,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

end GptLean.PhysicalFourierProduct
