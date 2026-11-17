import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
The density and current Banach spaces used by the physical constrained
search. An intersection is a compatible pair of actual Lp classes, with
the maximum of their two norms. Compatibility is proved closed using
uniqueness of convergence in measure on an arbitrary measure space.
-/

noncomputable section

namespace GptLean.PhysicalPairSpace

open MeasureTheory Filter Topology
open scoped ENNReal

section Intersection

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {μ : Measure α}

/-- The two Lp classes represent the same almost-everywhere function. -/
def compatibleSubmodule (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (μ : Measure α) :
    Submodule ℝ (Lp E p μ × Lp E q μ) where
  carrier := {u | (u.1 : α → E) =ᵐ[μ] (u.2 : α → E)}
  zero_mem' := (Lp.coeFn_zero E p μ).trans (Lp.coeFn_zero E q μ).symm
  add_mem' := by
    intro u v hu hv
    change ⇑(u.1 + v.1) =ᵐ[μ] ⇑(u.2 + v.2)
    change (u.1 : α → E) =ᵐ[μ] (u.2 : α → E) at hu
    change (v.1 : α → E) =ᵐ[μ] (v.2 : α → E) at hv
    filter_upwards [Lp.coeFn_add u.1 v.1, Lp.coeFn_add u.2 v.2, hu, hv]
      with x hx hy hu hv
    exact hx.trans ((congrArg₂ (· + ·) hu hv).trans hy.symm)
  smul_mem' := by
    intro c u hu
    change ⇑(c • u.1) =ᵐ[μ] ⇑(c • u.2)
    change (u.1 : α → E) =ᵐ[μ] (u.2 : α → E) at hu
    filter_upwards [Lp.coeFn_smul c u.1, Lp.coeFn_smul c u.2, hu] with x hx hy hu
    exact hx.trans ((congrArg (c • ·) hu).trans hy.symm)

/-- The normed intersection uses the inherited maximum product norm. -/
abbrev LpIntersection (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (μ : Measure α) :=
  compatibleSubmodule E p q μ

/-- The first continuous inclusion of the intersection. -/
def fst : LpIntersection E p q μ →L[ℝ] Lp E p μ :=
  (ContinuousLinearMap.fst ℝ (Lp E p μ) (Lp E q μ)).comp
    (compatibleSubmodule E p q μ).subtypeL

/-- The second continuous inclusion of the intersection. -/
def snd : LpIntersection E p q μ →L[ℝ] Lp E q μ :=
  (ContinuousLinearMap.snd ℝ (Lp E p μ) (Lp E q μ)).comp
    (compatibleSubmodule E p q μ).subtypeL

@[simp] theorem fst_apply (u : LpIntersection E p q μ) : fst u = u.val.1 := rfl
@[simp] theorem snd_apply (u : LpIntersection E p q μ) : snd u = u.val.2 := rfl

theorem compatible (u : LpIntersection E p q μ) :
    (fst u : α → E) =ᵐ[μ] (snd u : α → E) := u.property

theorem coe_fst_eq_coe_snd (u : LpIntersection E p q μ) :
    (fst u : α → E) =ᵐ[μ] (snd u : α → E) := compatible u

/-- Closedness uses neither finiteness nor sigma-finiteness of the measure. -/
theorem isClosed_compatibleSubmodule :
    IsClosed (compatibleSubmodule E p q μ : Set (Lp E p μ × Lp E q μ)) := by
  apply IsSeqClosed.isClosed
  intro u v hu huv
  have hp := tendstoInMeasure_of_tendsto_Lp (continuous_fst.tendsto v |>.comp huv)
  have hq := tendstoInMeasure_of_tendsto_Lp (continuous_snd.tendsto v |>.comp huv)
  exact tendstoInMeasure_ae_unique hp
    (hq.congr_left fun n => (show (u n).1 =ᵐ[μ] (u n).2 from hu n).symm)

instance instCompleteSpace [CompleteSpace E] : CompleteSpace (LpIntersection E p q μ) :=
  isClosed_compatibleSubmodule.completeSpace_coe

@[simp] theorem norm_eq_max (u : LpIntersection E p q μ) :
    ‖u‖ = max ‖fst u‖ ‖snd u‖ := rfl

theorem norm_fst_le (u : LpIntersection E p q μ) : ‖fst u‖ ≤ ‖u‖ :=
  _root_.norm_fst_le u.val

theorem norm_snd_le (u : LpIntersection E p q μ) : ‖snd u‖ ≤ ‖u‖ :=
  _root_.norm_snd_le u.val

@[ext] theorem ext_ae {u v : LpIntersection E p q μ}
    (h : (fst u : α → E) =ᵐ[μ] (fst v : α → E)) : u = v := by
  apply Subtype.ext
  apply Prod.ext
  · exact Lp.ext h
  · exact Lp.ext ((compatible u).symm.trans (h.trans (compatible v)))

theorem fst_injective : Function.Injective (fst (E := E) (p := p) (q := q) (μ := μ)) := by
  intro u v h
  apply ext_ae
  rw [h]

theorem snd_injective : Function.Injective (snd (E := E) (p := p) (q := q) (μ := μ)) := by
  intro u v h
  apply ext_ae
  exact (compatible u).trans ((Filter.EventuallyEq.of_eq (congrArg (fun f : Lp E q μ =>
    (f : α → E)) h)).trans (compatible v).symm)

/-- A compatible pair of existing Lp classes gives an intersection element. -/
def mk (f : Lp E p μ) (g : Lp E q μ) (h : (f : α → E) =ᵐ[μ] (g : α → E)) :
    LpIntersection E p q μ := ⟨(f, g), h⟩

/-- The canonical intersection class of one function with both memberships. -/
def ofMemLp (f : α → E) (hp : MemLp f p μ) (hq : MemLp f q μ) :
    LpIntersection E p q μ :=
  mk (hp.toLp f) (hq.toLp f) (hp.coeFn_toLp.trans hq.coeFn_toLp.symm)

@[simp] theorem fst_ofMemLp (f : α → E) (hp : MemLp f p μ) (hq : MemLp f q μ) :
    fst (ofMemLp f hp hq) = hp.toLp f := rfl

@[simp] theorem snd_ofMemLp (f : α → E) (hp : MemLp f p μ) (hq : MemLp f q μ) :
    snd (ofMemLp f hp hq) = hq.toLp f := rfl

theorem fst_ofMemLp_ae (f : α → E) (hp : MemLp f p μ) (hq : MemLp f q μ) :
    (fst (ofMemLp f hp hq) : α → E) =ᵐ[μ] f := hp.coeFn_toLp

theorem snd_ofMemLp_ae (f : α → E) (hp : MemLp f p μ) (hq : MemLp f q μ) :
    (snd (ofMemLp f hp hq) : α → E) =ᵐ[μ] f := hq.coeFn_toLp

theorem ofMemLp_eq_of_ae {f g : α → E}
    (hfp : MemLp f p μ) (hfq : MemLp f q μ)
    (hgp : MemLp g p μ) (hgq : MemLp g q μ) (h : f =ᵐ[μ] g) :
    ofMemLp f hfp hfq = ofMemLp g hgp hgq :=
  ext_ae (hfp.coeFn_toLp.trans (h.trans hgp.coeFn_toLp.symm))

theorem ofMemLp_eq_iff {f g : α → E}
    (hfp : MemLp f p μ) (hfq : MemLp f q μ)
    (hgp : MemLp g p μ) (hgq : MemLp g q μ) :
    ofMemLp f hfp hfq = ofMemLp g hgp hgq ↔ f =ᵐ[μ] g := by
  constructor
  · intro h
    exact (MemLp.toLp_eq_toLp_iff hfp hgp).mp (congrArg fst h)
  · exact ofMemLp_eq_of_ae hfp hfq hgp hgq

end Intersection

abbrev Position := EuclideanSpace ℝ (Fin 3)
abbrev Vector := EuclideanSpace ℝ (Fin 3)

instance fact_one_le_three : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
instance fact_one_le_three_halves : Fact (1 ≤ (3 / 2 : ℝ≥0∞)) := ⟨by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  norm_num⟩

/-- The physical scalar density space L¹(R³) ∩ L³(R³). -/
abbrev Density := LpIntersection ℝ 1 3 (volume : Measure Position)

/-- The physical vector current space L¹(R³,R³) ∩ L^(3/2)(R³,R³),
using the Euclidean norm on the current vector. -/
abbrev Current := LpIntersection Vector 1 (3 / 2) (volume : Measure Position)

abbrev Pair := Density × Current

def densityL1 : Pair →L[ℝ] Lp ℝ 1 (volume : Measure Position) :=
  fst.comp (ContinuousLinearMap.fst ℝ Density Current)

def densityL3 : Pair →L[ℝ] Lp ℝ 3 (volume : Measure Position) :=
  snd.comp (ContinuousLinearMap.fst ℝ Density Current)

def currentL1 : Pair →L[ℝ] Lp Vector 1 (volume : Measure Position) :=
  fst.comp (ContinuousLinearMap.snd ℝ Density Current)

def currentL32 : Pair →L[ℝ] Lp Vector (3 / 2) (volume : Measure Position) :=
  snd.comp (ContinuousLinearMap.snd ℝ Density Current)

theorem norm_densityL1_le (u : Pair) : ‖densityL1 u‖ ≤ ‖u‖ :=
  (norm_fst_le u.1).trans (_root_.norm_fst_le u)

theorem norm_densityL3_le (u : Pair) : ‖densityL3 u‖ ≤ ‖u‖ :=
  (norm_snd_le u.1).trans (_root_.norm_fst_le u)

theorem norm_currentL1_le (u : Pair) : ‖currentL1 u‖ ≤ ‖u‖ :=
  (norm_fst_le u.2).trans (_root_.norm_snd_le u)

theorem norm_currentL32_le (u : Pair) : ‖currentL32 u‖ ≤ ‖u‖ :=
  (norm_snd_le u.2).trans (_root_.norm_snd_le u)

@[fun_prop] theorem continuous_densityL1 : Continuous densityL1 := densityL1.continuous

/-- The actual density and current functions define a physical pair as
soon as their four stated integrability properties hold. -/
def ofFunctions (rho : Position → ℝ) (current : Position → Vector)
    (hρ1 : MemLp rho 1 volume) (hρ3 : MemLp rho 3 volume)
    (hj1 : MemLp current 1 volume) (hj32 : MemLp current (3 / 2) volume) : Pair :=
  (ofMemLp rho hρ1 hρ3, ofMemLp current hj1 hj32)

@[simp] theorem densityL1_ofFunctions (rho : Position → ℝ) (current : Position → Vector)
    (hρ1 : MemLp rho 1 volume) (hρ3 : MemLp rho 3 volume)
    (hj1 : MemLp current 1 volume) (hj32 : MemLp current (3 / 2) volume) :
    densityL1 (ofFunctions rho current hρ1 hρ3 hj1 hj32) = hρ1.toLp rho := rfl

@[simp] theorem currentL1_ofFunctions (rho : Position → ℝ) (current : Position → Vector)
    (hρ1 : MemLp rho 1 volume) (hρ3 : MemLp rho 3 volume)
    (hj1 : MemLp current 1 volume) (hj32 : MemLp current (3 / 2) volume) :
    currentL1 (ofFunctions rho current hρ1 hρ3 hj1 hj32) = hj1.toLp current := rfl

@[simp] theorem densityL3_ofFunctions (rho : Position → ℝ) (current : Position → Vector)
    (hρ1 : MemLp rho 1 volume) (hρ3 : MemLp rho 3 volume)
    (hj1 : MemLp current 1 volume) (hj32 : MemLp current (3 / 2) volume) :
    densityL3 (ofFunctions rho current hρ1 hρ3 hj1 hj32) = hρ3.toLp rho := rfl

@[simp] theorem currentL32_ofFunctions (rho : Position → ℝ) (current : Position → Vector)
    (hρ1 : MemLp rho 1 volume) (hρ3 : MemLp rho 3 volume)
    (hj1 : MemLp current 1 volume) (hj32 : MemLp current (3 / 2) volume) :
    currentL32 (ofFunctions rho current hρ1 hρ3 hj1 hj32) = hj32.toLp current := rfl

theorem ofFunctions_eq_of_ae {rho rho' : Position → ℝ} {current current' : Position → Vector}
    (hρ1 : MemLp rho 1 volume) (hρ3 : MemLp rho 3 volume)
    (hj1 : MemLp current 1 volume) (hj32 : MemLp current (3 / 2) volume)
    (hρ1' : MemLp rho' 1 volume) (hρ3' : MemLp rho' 3 volume)
    (hj1' : MemLp current' 1 volume) (hj32' : MemLp current' (3 / 2) volume)
    (hρ : rho =ᵐ[volume] rho') (hj : current =ᵐ[volume] current') :
    ofFunctions rho current hρ1 hρ3 hj1 hj32 =
      ofFunctions rho' current' hρ1' hρ3' hj1' hj32' :=
  Prod.ext (ofMemLp_eq_of_ae hρ1 hρ3 hρ1' hρ3' hρ)
    (ofMemLp_eq_of_ae hj1 hj32 hj1' hj32' hj)

@[ext] theorem pair_ext_ae {u v : Pair}
    (hρ : (densityL1 u : Position → ℝ) =ᵐ[volume] (densityL1 v : Position → ℝ))
    (hj : (currentL1 u : Position → Vector) =ᵐ[volume] (currentL1 v : Position → Vector)) :
    u = v := Prod.ext (ext_ae hρ) (ext_ae hj)

end GptLean.PhysicalPairSpace
