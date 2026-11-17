import GptLean.PhysicalPairSpace
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
The density-current Banach pair as a continuous real bilinear expression
in one common source domain. All four Lp components are actual Holder
products. Compatibility is proved from the common representatives.
-/

noncomputable section

namespace GptLean.PhysicalPairBilinear

open MeasureTheory PhysicalPairSpace
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

private theorem summable_bilinear_diagonal {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] E →L[ℝ] F) (u : ℕ → E)
    (hu : Summable (fun n => ‖u n‖ ^ 2)) : Summable (fun n => A (u n) (u n)) := by
  have hs : Summable (fun n => ‖A‖ * ‖u n‖ ^ 2) := hu.mul_left ‖A‖
  apply hs.of_norm_bounded
  intro n
  exact (A.le_opNorm₂ (u n) (u n)).trans_eq (by ring)

section Assembly

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  (d₁ : Q →L[ℝ] Q →L[ℝ] Lp ℝ 1 (volume : Measure Position))
  (d₃ : Q →L[ℝ] Q →L[ℝ] Lp ℝ 3 (volume : Measure Position))
  (j₁ : Q →L[ℝ] Q →L[ℝ] Lp Vector 1 (volume : Measure Position))
  (j₃₂ : Q →L[ℝ] Q →L[ℝ] Lp Vector (3 / 2) (volume : Measure Position))
  (hd : ∀ u v, (d₁ u v : Position → ℝ) =ᵐ[volume] d₃ u v)
  (hj : ∀ u v, (j₁ u v : Position → Vector) =ᵐ[volume] j₃₂ u v)

def assembleValue (u v : Q) : Pair :=
  (PhysicalPairSpace.mk (d₁ u v) (d₃ u v) (hd u v),
    PhysicalPairSpace.mk (j₁ u v) (j₃₂ u v) (hj u v))

def assembleLinear : Q →ₗ[ℝ] Q →ₗ[ℝ] Pair :=
  LinearMap.mk₂ ℝ (assembleValue d₁ d₃ j₁ j₃₂ hd hj)
    (fun u v w => by
      apply Prod.ext
      · apply fst_injective
        change d₁ (u + v) w = d₁ u w + d₁ v w
        simp only [map_add, add_apply]
      · apply fst_injective
        change j₁ (u + v) w = j₁ u w + j₁ v w
        simp only [map_add, add_apply])
    (fun c u v => by
      apply Prod.ext
      · apply fst_injective
        change d₁ (c • u) v = c • d₁ u v
        simp only [map_smul, smul_apply]
      · apply fst_injective
        change j₁ (c • u) v = c • j₁ u v
        simp only [map_smul, smul_apply])
    (fun u v w => by
      apply Prod.ext
      · apply fst_injective
        exact (d₁ u).map_add v w
      · apply fst_injective
        exact (j₁ u).map_add v w)
    (fun c u v => by
      apply Prod.ext
      · apply fst_injective
        exact (d₁ u).map_smul c v
      · apply fst_injective
        exact (j₁ u).map_smul c v)

theorem assembleValue_norm_le (u v : Q) :
    ‖assembleValue d₁ d₃ j₁ j₃₂ hd hj u v‖ ≤
      (‖d₁‖ + ‖d₃‖ + ‖j₁‖ + ‖j₃₂‖) * ‖u‖ * ‖v‖ := by
  have h₁ : ‖d₁‖ ≤ ‖d₁‖ + ‖d₃‖ + ‖j₁‖ + ‖j₃₂‖ := by
    linarith [norm_nonneg d₃, norm_nonneg j₁, norm_nonneg j₃₂]
  have h₃ : ‖d₃‖ ≤ ‖d₁‖ + ‖d₃‖ + ‖j₁‖ + ‖j₃₂‖ := by
    linarith [norm_nonneg d₁, norm_nonneg j₁, norm_nonneg j₃₂]
  have hj₁ : ‖j₁‖ ≤ ‖d₁‖ + ‖d₃‖ + ‖j₁‖ + ‖j₃₂‖ := by
    linarith [norm_nonneg d₁, norm_nonneg d₃, norm_nonneg j₃₂]
  have hj₃₂ : ‖j₃₂‖ ≤ ‖d₁‖ + ‖d₃‖ + ‖j₁‖ + ‖j₃₂‖ := by
    linarith [norm_nonneg d₁, norm_nonneg d₃, norm_nonneg j₁]
  change max (max ‖d₁ u v‖ ‖d₃ u v‖) (max ‖j₁ u v‖ ‖j₃₂ u v‖) ≤ _
  exact max_le
    (max_le ((d₁.le_opNorm₂ u v).trans (by gcongr))
      ((d₃.le_opNorm₂ u v).trans (by gcongr)))
    (max_le ((j₁.le_opNorm₂ u v).trans (by gcongr))
      ((j₃₂.le_opNorm₂ u v).trans (by gcongr)))

def assemble : Q →L[ℝ] Q →L[ℝ] Pair :=
  LinearMap.mkContinuous₂ (assembleLinear d₁ d₃ j₁ j₃₂ hd hj)
    (‖d₁‖ + ‖d₃‖ + ‖j₁‖ + ‖j₃₂‖) (assembleValue_norm_le d₁ d₃ j₁ j₃₂ hd hj)

end Assembly

section HolderSources

variable {Q H : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def coordinate (a : Fin 3) : ℝ →L[ℝ] Vector :=
  ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single a 1)

def scalarHolder {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p q r]
    (L : Q →L[ℝ] Lp H p (volume : Measure Position))
    (R : Q →L[ℝ] Lp H q (volume : Measure Position)) :
    Q →L[ℝ] Q →L[ℝ] Lp ℝ r (volume : Measure Position) :=
  ((innerSL ℝ (E := H)).holderL volume p q r).bilinearComp L R

theorem scalarHolder_ae {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p q r]
    (L : Q →L[ℝ] Lp H p (volume : Measure Position))
    (R : Q →L[ℝ] Lp H q (volume : Measure Position)) (u v : Q) :
    (scalarHolder (r := r) L R u v : Position → ℝ) =ᵐ[volume]
      (fun x => inner ℝ (L u x) (R v x)) :=
  (innerSL ℝ (E := H)).coeFn_holder (L u) (R v)

def vectorHolder {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p q r]
    (L : Q →L[ℝ] Lp H p (volume : Measure Position))
    (R : Fin 3 → Q →L[ℝ] Lp H q (volume : Measure Position)) :
    Q →L[ℝ] Q →L[ℝ] Lp Vector r (volume : Measure Position) :=
  ∑ a, (((coordinate a).compLpL r volume).postcomp Q).comp (scalarHolder (r := r) L (R a))

theorem vectorHolder_ae {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p q r]
    (L : Q →L[ℝ] Lp H p (volume : Measure Position))
    (R : Fin 3 → Q →L[ℝ] Lp H q (volume : Measure Position)) (u v : Q) :
    (vectorHolder (r := r) L R u v : Position → Vector) =ᵐ[volume]
      (fun x => WithLp.toLp 2 (fun a => inner ℝ (L u x) (R a v x))) := by
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ
    (fun a => (coordinate a).compLpL r volume (scalarHolder (r := r) L (R a) u v))
  have hcoord : ∀ᵐ x ∂volume, ∀ a : Fin 3,
      ((coordinate a).compLpL r volume (scalarHolder (r := r) L (R a) u v)) x =
        coordinate a (inner ℝ (L u x) (R a v x)) := by
    apply ae_all_iff.mpr
    intro a
    filter_upwards [(coordinate a).coeFn_compLpL (scalarHolder (r := r) L (R a) u v),
      scalarHolder_ae (r := r) L (R a) u v] with x hx hy
    exact hx.trans (congrArg (coordinate a) hy)
  have happ : vectorHolder (r := r) L R u v =
      ∑ a, (coordinate a).compLpL r volume (scalarHolder (r := r) L (R a) u v) := by
    simp only [vectorHolder, sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.postcomp_apply]
  rw [happ]
  filter_upwards [hsum, hcoord] with x hx hcoord
  rw [hx]
  apply PiLp.ext
  intro a
  change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) a)
    (∑ b, ((coordinate b).compLpL r volume (scalarHolder (r := r) L (R b) u v)) x) = _
  rw [map_sum]
  have he (b : Fin 3) :
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) a)
        (((coordinate b).compLpL r volume (scalarHolder (r := r) L (R b) u v)) x) =
      if a = b then inner ℝ (L u x) (R b v x) else 0 := by
    exact (congrArg (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) a) (hcoord b)).trans
      (by simp [coordinate, PiLp.proj_apply])
  simp only [he]
  simp

private instance fact_six : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩

private instance holder_six_six : ENNReal.HolderTriple 6 6 3 :=
  ENNReal.HolderTriple.of_toReal ⟨by norm_num, by norm_num, by norm_num⟩

variable (N : ℕ)
  (L₂ : Q →L[ℝ] Lp H 2 (volume : Measure Position))
  (L₆ : Q →L[ℝ] Lp H 6 (volume : Measure Position))
  (hL : ∀ u, (L₂ u : Position → H) =ᵐ[volume] L₆ u)
  (D : Fin 3 → Q →L[ℝ] Lp H 2 (volume : Measure Position))

private instance holder_six_two : ENNReal.HolderTriple 6 2 (3 / 2) :=
  ENNReal.HolderTriple.of_toReal ⟨by norm_num [ENNReal.toReal_div], by norm_num, by norm_num⟩

def densityOne := (N : ℝ) • scalarHolder (r := 1) L₂ L₂
def densityThree := (N : ℝ) • scalarHolder (r := 3) L₆ L₆
def currentOne := (N : ℝ) • vectorHolder (r := 1) L₂ D
def currentThreeHalves := (N : ℝ) • vectorHolder (r := 3 / 2) L₆ D

include hL in
theorem density_compatible (u v : Q) :
    (densityOne N L₂ u v : Position → ℝ) =ᵐ[volume] densityThree N L₆ u v := by
  filter_upwards [Lp.coeFn_smul (N : ℝ) (scalarHolder (r := 1) L₂ L₂ u v),
    Lp.coeFn_smul (N : ℝ) (scalarHolder (r := 3) L₆ L₆ u v),
    scalarHolder_ae (r := 1) L₂ L₂ u v, scalarHolder_ae (r := 3) L₆ L₆ u v,
    hL u, hL v] with x h₁ h₃ hs ht hu hv
  exact h₁.trans ((congrArg ((N : ℝ) • ·) (hs.trans
    ((congrArg₂ (inner ℝ) hu hv).trans ht.symm))).trans h₃.symm)

include hL in
theorem current_compatible (u v : Q) :
    (currentOne N L₂ D u v : Position → Vector) =ᵐ[volume]
      currentThreeHalves N L₆ D u v := by
  filter_upwards [Lp.coeFn_smul (N : ℝ) (vectorHolder (r := 1) L₂ D u v),
    Lp.coeFn_smul (N : ℝ) (vectorHolder (r := 3 / 2) L₆ D u v),
    vectorHolder_ae (r := 1) L₂ D u v, vectorHolder_ae (r := 3 / 2) L₆ D u v,
    hL u] with x h₁ h₃ hs ht hu
  rw [hu] at hs
  exact h₁.trans ((congrArg ((N : ℝ) • ·) (hs.trans ht.symm)).trans h₃.symm)

def form : Q →L[ℝ] Q →L[ℝ] Pair :=
  assemble (densityOne N L₂) (densityThree N L₆) (currentOne N L₂ D)
    (currentThreeHalves N L₆ D) (density_compatible N L₂ L₆ hL)
    (current_compatible N L₂ L₆ hL D)

theorem density_form_ae (u v : Q) :
    (densityL1 (form N L₂ L₆ hL D u v) : Position → ℝ) =ᵐ[volume]
      (fun x => (N : ℝ) * inner ℝ (L₂ u x) (L₂ v x)) := by
  filter_upwards [Lp.coeFn_smul (N : ℝ) (scalarHolder (r := 1) L₂ L₂ u v),
    scalarHolder_ae (r := 1) L₂ L₂ u v] with x hx hy
  exact hx.trans (congrArg ((N : ℝ) * ·) hy)

theorem current_form_ae (u v : Q) :
    (currentL1 (form N L₂ L₆ hL D u v) : Position → Vector) =ᵐ[volume]
      (fun x => WithLp.toLp 2 (fun a => (N : ℝ) * inner ℝ (L₂ u x) (D a v x))) := by
  filter_upwards [Lp.coeFn_smul (N : ℝ) (vectorHolder (r := 1) L₂ D u v),
    vectorHolder_ae (r := 1) L₂ D u v] with x hx hy
  exact hx.trans (congrArg ((N : ℝ) • ·) hy)

theorem summable_diagonal (u : ℕ → Q) (hu : Summable (fun n => ‖u n‖ ^ 2)) :
    Summable (fun n => form N L₂ L₆ hL D (u n) (u n)) := by
  exact summable_bilinear_diagonal (form N L₂ L₆ hL D) u hu

end HolderSources

end GptLean.PhysicalPairBilinear
