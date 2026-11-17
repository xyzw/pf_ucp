import GptLean.Repair.ParameterSections

/-!
Actual Hilbert-valued source sections obtained from a product-space L2
wave function. Fubini constructs an isometric linear map into iterated L2,
including almost-everywhere norm and current-pairing formulas. This is the
measure-theoretic source construction needed for particle marginals.
-/

noncomputable section

namespace GptLean.PhysicalSourceFubini

open MeasureTheory Filter Repair
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {X Y H : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] [IsSeparable ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

abbrev ProductL2 := Lp H 2 (μ.prod ν)
abbrev IteratedL2 := Lp (Lp H 2 ν) 2 μ

def sourceSection (u : ProductL2 (H := H) (μ := μ) (ν := ν)) (x : X) : Lp H 2 ν :=
  toL2Section (μ := ν) (fun x y => u (x, y)) x

omit [SFinite μ] in
theorem section_stronglyMeasurable (u : ProductL2 (H := H) (μ := μ) (ν := ν)) :
    StronglyMeasurable (sourceSection u) :=
  stronglyMeasurable_toL2Section (Lp.stronglyMeasurable u)

omit [IsSeparable ν] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H] in
theorem section_memLp_ae (u : ProductL2 (H := H) (μ := μ) (ν := ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => u (x, y)) 2 ν := by
  have hsm : StronglyMeasurable (Function.uncurry (fun x y => u (x, y))) :=
    Lp.stronglyMeasurable u
  have hint : Integrable (fun z => ‖u z‖ ^ 2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  filter_upwards [hint.prod_right_ae] with x hx
  exact (memLp_two_iff_integrable_sq_norm
    hsm.of_uncurry_left.aestronglyMeasurable).mpr hx

omit [IsSeparable ν] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H] in
theorem section_represents_ae (u : ProductL2 (H := H) (μ := μ) (ν := ν)) :
    ∀ᵐ x ∂μ, (sourceSection u x : Y → H) =ᵐ[ν] (fun y => u (x, y)) :=
  toL2Section_ae_represents (section_memLp_ae u)

omit [IsSeparable ν] [TopologicalSpace.SeparableSpace H] in
theorem section_norm_sq_ae (u : ProductL2 (H := H) (μ := μ) (ν := ν)) :
    (fun x => ‖sourceSection u x‖ ^ 2) =ᵐ[μ] (fun x => ∫ y, ‖u (x, y)‖ ^ 2 ∂ν) := by
  filter_upwards [section_memLp_ae u] with x hx
  rw [sourceSection, toL2Section_eq hx]
  exact toL2_norm_sq hx

theorem section_memLp (u : ProductL2 (H := H) (μ := μ) (ν := ν)) :
    MemLp (sourceSection u) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (section_stronglyMeasurable u).aestronglyMeasurable).mpr
  have hint : Integrable (fun z => ‖u z‖ ^ 2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  exact hint.integral_prod_left.congr (section_norm_sq_ae u).symm

def curry (u : ProductL2 (H := H) (μ := μ) (ν := ν)) :
    IteratedL2 (H := H) (μ := μ) (ν := ν) :=
  (section_memLp u).toLp (sourceSection u)

theorem curry_ae (u : ProductL2 (H := H) (μ := μ) (ν := ν)) :
    (curry u : X → Lp H 2 ν) =ᵐ[μ] sourceSection u := (section_memLp u).coeFn_toLp

theorem norm_curry (u : ProductL2 (H := H) (μ := μ) (ν := ν)) : ‖curry u‖ = ‖u‖ := by
  have hint : Integrable (fun z => ‖u z‖ ^ 2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hsquare : ‖curry u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [curry, toL2_norm_sq, integral_congr_ae (section_norm_sq_ae u),
      ← integral_prod _ hint]
    simpa only [Lp.toLp_coeFn] using (toL2_norm_sq (Lp.memLp u)).symm
  nlinarith [norm_nonneg (curry u), norm_nonneg u]

theorem curry_add (u v : ProductL2 (H := H) (μ := μ) (ν := ν)) :
    curry (u + v) = curry u + curry v := by
  apply Lp.ext
  filter_upwards [curry_ae (u + v), curry_ae u, curry_ae v,
    Lp.coeFn_add (curry u) (curry v), section_memLp_ae u, section_memLp_ae v,
    Measure.ae_ae_of_ae_prod (Lp.coeFn_add u v)] with x huv hu hv hadd hmu hmv hsum
  rw [huv, hadd, Pi.add_apply, hu, hv]
  rw [sourceSection, sourceSection, sourceSection,
    toL2Section_congr (f := fun x y => (u + v) (x, y))
      (g := fun x y => u (x, y) + v (x, y)) (q := x) hsum,
    toL2Section_eq (f := fun x y => u (x, y) + v (x, y)) (q := x) (hmu.add hmv),
    toL2Section_eq (f := fun x y => u (x, y)) (q := x) hmu,
    toL2Section_eq (f := fun x y => v (x, y)) (q := x) hmv]
  exact MemLp.toLp_add hmu hmv

theorem curry_smul (c : ℂ) (u : ProductL2 (H := H) (μ := μ) (ν := ν)) :
    curry (c • u) = c • curry u := by
  apply Lp.ext
  filter_upwards [curry_ae (c • u), curry_ae u, Lp.coeFn_smul c (curry u),
    section_memLp_ae u, Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c u)] with x hcu hu hsm hmu hsource
  rw [hcu, hsm, Pi.smul_apply, hu]
  rw [sourceSection, sourceSection,
    toL2Section_congr (f := fun x y => (c • u) (x, y))
      (g := fun x y => c • u (x, y)) (q := x) hsource,
    toL2Section_eq (f := fun x y => c • u (x, y)) (q := x) (hmu.const_smul c),
    toL2Section_eq (f := fun x y => u (x, y)) (q := x) hmu]
  exact MemLp.toLp_const_smul c hmu

/-- The product-to-iterated-L2 Fubini map is constructed from actual sections. -/
def curryIsometry : ProductL2 (H := H) (μ := μ) (ν := ν) →ₗᵢ[ℂ]
    IteratedL2 (H := H) (μ := μ) (ν := ν) where
  toFun := curry
  map_add' := curry_add
  map_smul' := curry_smul
  norm_map' := norm_curry

/-- Norm squared of a marginal source is the actual integrated density. -/
theorem curry_norm_sq_ae (u : ProductL2 (H := H) (μ := μ) (ν := ν)) :
    (fun x => ‖curry u x‖ ^ 2) =ᵐ[μ] (fun x => ∫ y, ‖u (x, y)‖ ^ 2 ∂ν) := by
  filter_upwards [curry_ae u, section_norm_sq_ae u] with x hu hn
  rw [hu, hn]

/-- The marginal-source inner product is the actual integrated current
pairing, on one common full-measure set for the two source functions. -/
theorem curry_inner_ae (u v : ProductL2 (H := H) (μ := μ) (ν := ν)) :
    (fun x => inner ℂ (curry u x) (curry v x)) =ᵐ[μ]
      (fun x => ∫ y, inner ℂ (u (x, y)) (v (x, y)) ∂ν) := by
  filter_upwards [curry_ae u, curry_ae v, section_represents_ae u, section_represents_ae v]
    with x hu hv hsu hsv
  rw [hu, hv, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hsu, hsv] with y hyu hyv
  rw [hyu, hyv]

end GptLean.PhysicalSourceFubini
