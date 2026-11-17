import GptLean.TransformationsGaugePair
import GptLean.PhysicalPairDuality
import GptLean.Transformations
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

/-!
Gauge, time-reversal and translation covariance of the Lieb functional on
the article pair space `X × Y`, with potentials
`(L∞ + L^{3/2}) × (L∞ + L³)` and the pairing `pairPotential`.

Each transformation acts on pairs through a bijection `τ` and on potentials
through a bijection `σ` with `⟨σ u, d⟩ = ⟨u₀, d⟩ + ⟨u, τ d⟩`. Then
`Transformations.lieb_covariance` transfers covariance of the constrained
search to the Lieb functional.

* Gauge: `σ(v, A) = (v + A·∇g + ½|∇g|², A + ∇g)` and `u₀ = (½|∇g|², ∇g)`,
  whose pairing with `(ρ, j)` is the energy shift `∫ ∇g·j + ½ ∫ ρ|∇g|²`.
  The `L³` part of `A·∇g` is split at height one into `L∞ + L^{3/2}`.
* Time reversal: `(ρ, j) ↦ (ρ, -j)` and `(v, A) ↦ (v, -A)`.
* Translation: `f ↦ f(· - b)` on every component. The pairing is invariant
  because Lebesgue measure is translation invariant.

The covariance of the constrained search itself is a hypothesis here.
-/

noncomputable section

namespace GptLean.TransformationsPotentials

open MeasureTheory PhysicalPairSpace PhysicalPairDuality TransformationsGauge
open scoped ENNReal

set_option maxHeartbeats 400000

/-! ### Algebra of `L∞ + Lq` classes and their pairing -/

section SumAlgebra

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure α} {q : ℝ≥0∞}

/-- An `L∞ + Lq` class is determined by its almost-everywhere values. -/
theorem sum_ext_ae {u w : LpSum E q μ}
    (h : (u.val : α → E) =ᵐ[μ] (w.val : α → E)) : u = w :=
  Subtype.ext (AEEqFun.ext h)

theorem coeFn_sum_add (u w : LpSum E q μ) :
    ((u + w).val : α → E) =ᵐ[μ] fun x => u.val x + w.val x :=
  AEEqFun.coeFn_add u.val w.val

theorem coeFn_ofParts (a : Lp E ∞ μ) (b : Lp E q μ) :
    ((ofParts a b).val : α → E) =ᵐ[μ] fun x => a x + b x :=
  AEEqFun.coeFn_add a.val b.val

theorem coeFn_ofParts_zero (a : Lp E ∞ μ) :
    ((ofParts a (0 : Lp E q μ)).val : α → E) =ᵐ[μ] a := by
  filter_upwards [coeFn_ofParts a (0 : Lp E q μ), Lp.coeFn_zero E q μ] with x h₁ h₂
  rw [h₁, h₂, Pi.zero_apply, add_zero]

/-- The chosen decomposition represents the class. -/
theorem coeFn_parts (u : LpSum E q μ) :
    (u.val : α → E) =ᵐ[μ] fun x => (parts u).1 x + (parts u).2 x := by
  have h := AEEqFun.coeFn_add (parts u).1.val (parts u).2.val
  rw [show (parts u).1.val + (parts u).2.val = u.val from parts_spec u] at h
  exact h

end SumAlgebra

section PairingAlgebra

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure α}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate q p]

theorem partsPairing_add (a a' : Lp E ∞ μ) (b b' : Lp E q μ) :
    partsPairing (p := p) (a + a') (b + b') = partsPairing a b + partsPairing a' b' := by
  ext f
  change lpInner (a + a') (fst f) + lpInner (b + b') (snd f) =
    (lpInner a (fst f) + lpInner b (snd f)) + (lpInner a' (fst f) + lpInner b' (snd f))
  simp only [map_add, _root_.add_apply]
  ring

theorem partsPairing_neg (a : Lp E ∞ μ) (b : Lp E q μ) :
    partsPairing (p := p) (-a) (-b) = -partsPairing a b := by
  ext f
  change lpInner (-a) (fst f) + lpInner (-b) (snd f) =
    -(lpInner a (fst f) + lpInner b (snd f))
  simp only [map_neg, _root_.neg_apply]
  ring

theorem partsPairing_zero :
    partsPairing (p := p) (0 : Lp E ∞ μ) (0 : Lp E q μ) = 0 := by
  ext f
  change lpInner (0 : Lp E ∞ μ) (fst f) + lpInner (0 : Lp E q μ) (snd f) = 0
  simp only [map_zero, _root_.zero_apply, add_zero]

/-- The pairing is additive in the potential. -/
theorem pairing_add (u w : LpSum E q μ) :
    pairing (p := p) (u + w) = pairing u + pairing w := by
  have h : sumLp ((parts u).1 + (parts w).1, (parts u).2 + (parts w).2) = (u + w).val := by
    change sumLp (parts u + parts w) = u.val + w.val
    rw [map_add, parts_spec, parts_spec]
  exact (pairing_eq_of_parts (p := p) (u + w) _ _ h).trans (partsPairing_add _ _ _ _)

theorem pairing_neg (u : LpSum E q μ) : pairing (p := p) (-u) = -pairing u := by
  have h : sumLp (-(parts u).1, -(parts u).2) = (-u).val := by
    change sumLp (-parts u) = -u.val
    rw [map_neg, parts_spec]
  exact (pairing_eq_of_parts (p := p) (-u) _ _ h).trans (partsPairing_neg _ _)

theorem pairing_zero : pairing (p := p) (0 : LpSum E q μ) = 0 := by
  have h : sumLp ((0 : Lp E ∞ μ), (0 : Lp E q μ)) = (0 : LpSum E q μ).val := by
    change sumLp 0 = 0
    exact map_zero _
  exact (pairing_eq_of_parts (p := p) (0 : LpSum E q μ) _ _ h).trans partsPairing_zero

end PairingAlgebra

section PhysicalPairing

theorem pairPotential_apply (u : Potential) (d : Pair) :
    pairPotential u d = pairing u.1 d.1 + pairing u.2 d.2 := rfl

theorem pairPotential_zero (d : Pair) : pairPotential (0 : Potential) d = 0 := by
  change pairing (0 : ScalarPotential) d.1 + pairing (0 : VectorPotential) d.2 = 0
  simp only [pairing_zero, _root_.zero_apply, add_zero]

theorem pairing_density (v : ScalarPotential) (d : Pair) :
    pairing v d.1 = ∫ x, v.val x * densityL1 d x := by
  rw [pairing_eq_integral]
  simp only [Real.inner_apply]
  rfl

theorem pairing_current (A : VectorPotential) (d : Pair) :
    pairing A d.2 = ∫ x, inner ℝ (A.val x) (currentL1 d x) := by
  rw [pairing_eq_integral]
  rfl

/-- Invariance of the search under a pair bijection `τ` passes to the Lieb
functional when a potential bijection `σ` is adjoint to `τ`. -/
theorem lieb_invariance {S : Type*} (A : DFT.StateModel S Pair) (τ : Pair ≃ Pair)
    (σ : Potential ≃ Potential) (hσ : ∀ u d, pairPotential (σ u) d = pairPotential u (τ d))
    (hsym : ∀ d, DFT.search A (τ d) = DFT.search A d) (d : Pair) :
    DFT.lieb A (fun u p => pairPotential u p) (τ d) =
      DFT.lieb A (fun u p => pairPotential u p) d := by
  have h := Transformations.lieb_covariance A (fun u p => pairPotential u p) τ σ 0
    (fun u e => by
      show pairPotential (σ u) e = pairPotential 0 e + pairPotential u (τ e)
      rw [pairPotential_zero, zero_add]
      exact hσ u e)
    (fun e => by
      show DFT.search A (τ e) = DFT.search A e + ((pairPotential 0 e : ℝ) : EReal)
      rw [pairPotential_zero, EReal.coe_zero, add_zero]
      exact hsym e) d
  calc DFT.lieb A (fun u p => pairPotential u p) (τ d)
      = DFT.lieb A (fun u p => pairPotential u p) d + ((pairPotential 0 d : ℝ) : EReal) := h
    _ = _ := by rw [pairPotential_zero, EReal.coe_zero, add_zero]

end PhysicalPairing

/-! ### Time reversal: odd reflection of the current -/

section Flip

/-- Time reversal on pairs, `(ρ, j) ↦ (ρ, -j)`. -/
def currentFlip : Pair ≃ Pair where
  toFun d := (d.1, -d.2)
  invFun d := (d.1, -d.2)
  left_inv d := Prod.ext rfl (neg_neg d.2)
  right_inv d := Prod.ext rfl (neg_neg d.2)

theorem currentFlip_apply (d : Pair) : currentFlip d = (d.1, -d.2) := rfl

theorem densityL1_currentFlip (d : Pair) : densityL1 (currentFlip d) = densityL1 d := rfl

theorem currentL1_currentFlip (d : Pair) : currentL1 (currentFlip d) = -currentL1 d := by
  change PhysicalPairSpace.fst (-d.2) = -PhysicalPairSpace.fst d.2
  exact map_neg _ _

/-- Reflection of the vector potential, `(v, A) ↦ (v, -A)`. -/
def potentialFlip : Potential ≃ Potential where
  toFun u := (u.1, -u.2)
  invFun u := (u.1, -u.2)
  left_inv u := Prod.ext rfl (neg_neg u.2)
  right_inv u := Prod.ext rfl (neg_neg u.2)

theorem potentialFlip_apply (u : Potential) : potentialFlip u = (u.1, -u.2) := rfl

theorem pairPotential_potentialFlip (u : Potential) (d : Pair) :
    pairPotential (potentialFlip u) d = pairPotential u (currentFlip d) := by
  change pairing u.1 d.1 + pairing (-u.2) d.2 = pairing u.1 d.1 + pairing u.2 (-d.2)
  rw [pairing_neg, _root_.neg_apply, map_neg]

/-- Time-reversal invariance passes from the constrained search to the Lieb
functional. -/
theorem lieb_flip {S : Type*} (A : DFT.StateModel S Pair)
    (hsym : ∀ d, DFT.search A (currentFlip d) = DFT.search A d) (d : Pair) :
    DFT.lieb A (fun u p => pairPotential u p) (currentFlip d) =
      DFT.lieb A (fun u p => pairPotential u p) d :=
  lieb_invariance A currentFlip potentialFlip pairPotential_potentialFlip hsym d

end Flip

/-! ### Spatial translation -/

section Translation

/-- Translation `x ↦ x - b` preserves Lebesgue measure. -/
theorem measurePreserving_translate (b : Position) :
    MeasurePreserving (fun x : Position => x - b) volume volume :=
  measurePreserving_sub_right volume b

theorem ae_comp_translate {β : Type*} {f f' : Position → β} (b : Position)
    (h : f =ᵐ[volume] f') : (fun x => f (x - b)) =ᵐ[volume] fun x => f' (x - b) :=
  (measurePreserving_translate b).quasiMeasurePreserving.ae_eq_comp h

/-- Translation `f ↦ f(· - b)` of one `Lp` class. -/
def translateLp {F : Type*} [NormedAddCommGroup F] {r : ℝ≥0∞} (b : Position)
    (f : Lp F r (volume : Measure Position)) : Lp F r (volume : Measure Position) :=
  Lp.compMeasurePreserving (fun x => x - b) (measurePreserving_translate b) f

theorem coeFn_translateLp {F : Type*} [NormedAddCommGroup F] {r : ℝ≥0∞} (b : Position)
    (f : Lp F r (volume : Measure Position)) :
    (translateLp b f : Position → F) =ᵐ[volume] fun x => f (x - b) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_translate b)

section Intersection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Translation `f ↦ f(· - b)` of a compatible pair of `Lp` classes. -/
def translateIntersection (b : Position)
    (u : LpIntersection E p q (volume : Measure Position)) :
    LpIntersection E p q (volume : Measure Position) :=
  ofMemLp (fun x => PhysicalPairSpace.fst u (x - b))
    ((Lp.memLp (PhysicalPairSpace.fst u)).comp_measurePreserving
      (measurePreserving_translate b))
    (((Lp.memLp (PhysicalPairSpace.snd u)).comp_measurePreserving
      (measurePreserving_translate b)).ae_eq
        (ae_comp_translate b (PhysicalPairSpace.compatible u)).symm)

theorem fst_translateIntersection (b : Position)
    (u : LpIntersection E p q (volume : Measure Position)) :
    (PhysicalPairSpace.fst (translateIntersection b u) : Position → E) =ᵐ[volume]
      fun x => PhysicalPairSpace.fst u (x - b) :=
  fst_ofMemLp_ae _ _ _

theorem translateIntersection_add (b c : Position)
    (u : LpIntersection E p q (volume : Measure Position)) :
    translateIntersection c (translateIntersection b u) = translateIntersection (b + c) u := by
  apply PhysicalPairSpace.ext_ae
  filter_upwards [fst_translateIntersection c (translateIntersection b u),
    ae_comp_translate c (fst_translateIntersection b u),
    fst_translateIntersection (b + c) u] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, sub_sub, add_comm c b]

theorem translateIntersection_zero (u : LpIntersection E p q (volume : Measure Position)) :
    translateIntersection 0 u = u := by
  apply PhysicalPairSpace.ext_ae
  filter_upwards [fst_translateIntersection 0 u] with x h
  rw [h, sub_zero]

theorem translateIntersection_neg_left (b : Position)
    (u : LpIntersection E p q (volume : Measure Position)) :
    translateIntersection (-b) (translateIntersection b u) = u := by
  rw [translateIntersection_add, add_neg_cancel, translateIntersection_zero]

theorem translateIntersection_neg_right (b : Position)
    (u : LpIntersection E p q (volume : Measure Position)) :
    translateIntersection b (translateIntersection (-b) u) = u := by
  rw [translateIntersection_add, neg_add_cancel, translateIntersection_zero]

end Intersection

section Sum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {q : ℝ≥0∞}

/-- Translation of an `L∞ + Lq` class, acting on both parts of its chosen
decomposition. -/
def translateSum (b : Position) (u : LpSum F q (volume : Measure Position)) :
    LpSum F q (volume : Measure Position) :=
  ofParts (translateLp b (parts u).1) (translateLp b (parts u).2)

theorem coeFn_translateSum (b : Position) (u : LpSum F q (volume : Measure Position)) :
    ((translateSum b u).val : Position → F) =ᵐ[volume] fun x => u.val (x - b) := by
  have h : ((translateSum b u).val : Position → F) =ᵐ[volume]
      fun x => translateLp b (parts u).1 x + translateLp b (parts u).2 x :=
    coeFn_ofParts _ _
  filter_upwards [h, coeFn_translateLp b (parts u).1, coeFn_translateLp b (parts u).2,
    ae_comp_translate b (coeFn_parts u)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

theorem translateSum_add (b c : Position) (u : LpSum F q (volume : Measure Position)) :
    translateSum c (translateSum b u) = translateSum (b + c) u := by
  apply sum_ext_ae
  filter_upwards [coeFn_translateSum c (translateSum b u),
    ae_comp_translate c (coeFn_translateSum b u), coeFn_translateSum (b + c) u]
    with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, sub_sub, add_comm c b]

theorem translateSum_zero (u : LpSum F q (volume : Measure Position)) :
    translateSum 0 u = u := by
  apply sum_ext_ae
  filter_upwards [coeFn_translateSum 0 u] with x h
  rw [h, sub_zero]

theorem translateSum_neg_left (b : Position) (u : LpSum F q (volume : Measure Position)) :
    translateSum (-b) (translateSum b u) = u := by
  rw [translateSum_add, add_neg_cancel, translateSum_zero]

theorem translateSum_neg_right (b : Position) (u : LpSum F q (volume : Measure Position)) :
    translateSum b (translateSum (-b) u) = u := by
  rw [translateSum_add, neg_add_cancel, translateSum_zero]

/-- Translating the potential and the paired function together leaves the
pairing unchanged. -/
theorem pairing_translate {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate q p] (b : Position)
    (u : LpSum F q (volume : Measure Position))
    (f : LpIntersection F 1 p (volume : Measure Position)) :
    pairing (translateSum b u) (translateIntersection b f) = pairing u f := by
  rw [pairing_eq_integral, pairing_eq_integral]
  refine (integral_congr_ae ?_).trans (integral_sub_right_eq_self (μ := volume)
    (fun x => inner ℝ (u.val x) (PhysicalPairSpace.fst f x)) b)
  filter_upwards [coeFn_translateSum b u, fst_translateIntersection b f] with x h₁ h₂
  rw [h₁, h₂]

end Sum

/-- Spatial translation of pairs, `(ρ, j) ↦ (ρ(· - b), j(· - b))`. -/
def translatePair (b : Position) : Pair ≃ Pair where
  toFun d := (translateIntersection b d.1, translateIntersection b d.2)
  invFun d := (translateIntersection (-b) d.1, translateIntersection (-b) d.2)
  left_inv d := Prod.ext (translateIntersection_neg_left b d.1)
    (translateIntersection_neg_left b d.2)
  right_inv d := Prod.ext (translateIntersection_neg_right b d.1)
    (translateIntersection_neg_right b d.2)

theorem densityL1_translatePair (b : Position) (d : Pair) :
    (densityL1 (translatePair b d) : Position → ℝ) =ᵐ[volume]
      fun x => densityL1 d (x - b) :=
  fst_translateIntersection b d.1

theorem currentL1_translatePair (b : Position) (d : Pair) :
    (currentL1 (translatePair b d) : Position → Vector) =ᵐ[volume]
      fun x => currentL1 d (x - b) :=
  fst_translateIntersection b d.2

/-- Spatial translation of potentials, `(v, A) ↦ (v(· - b), A(· - b))`. -/
def translatePotential (b : Position) : Potential ≃ Potential where
  toFun u := (translateSum b u.1, translateSum b u.2)
  invFun u := (translateSum (-b) u.1, translateSum (-b) u.2)
  left_inv u := Prod.ext (translateSum_neg_left b u.1) (translateSum_neg_left b u.2)
  right_inv u := Prod.ext (translateSum_neg_right b u.1) (translateSum_neg_right b u.2)

theorem coeFn_translatePotential_fst (b : Position) (u : Potential) :
    ((translatePotential b u).1.val : Position → ℝ) =ᵐ[volume] fun x => u.1.val (x - b) :=
  coeFn_translateSum b u.1

theorem coeFn_translatePotential_snd (b : Position) (u : Potential) :
    ((translatePotential b u).2.val : Position → Vector) =ᵐ[volume]
      fun x => u.2.val (x - b) :=
  coeFn_translateSum b u.2

/-- Change of variables: the pairing is translation invariant. -/
theorem pairPotential_translate (b : Position) (u : Potential) (d : Pair) :
    pairPotential (translatePotential b u) (translatePair b d) = pairPotential u d := by
  change pairing (translateSum b u.1) (translateIntersection b d.1) +
      pairing (translateSum b u.2) (translateIntersection b d.2) =
    pairing u.1 d.1 + pairing u.2 d.2
  rw [pairing_translate, pairing_translate]

/-- Translation invariance passes from the constrained search to the Lieb
functional. -/
theorem lieb_translate {S : Type*} (A : DFT.StateModel S Pair) (b : Position)
    (hsym : ∀ d, DFT.search A (translatePair b d) = DFT.search A d) (d : Pair) :
    DFT.lieb A (fun u p => pairPotential u p) (translatePair b d) =
      DFT.lieb A (fun u p => pairPotential u p) d :=
  lieb_invariance A (translatePair b) (translatePotential b).symm
    (fun u e => by
      rw [← pairPotential_translate b ((translatePotential b).symm u) e,
        Equiv.apply_symm_apply])
    hsym d

end Translation

/-! ### Truncation of `L³` into `L∞ + L^{3/2}` -/

section Truncation

/-- Truncation of a real number at height one. -/
def clampOne (t : ℝ) : ℝ := max (-1) (min 1 t)

theorem continuous_clampOne : Continuous clampOne := by
  unfold clampOne
  exact continuous_const.max (continuous_const.min continuous_id')

theorem abs_clampOne_le (t : ℝ) : |clampOne t| ≤ 1 := by
  unfold clampOne
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem abs_sub_clampOne_le_abs (t : ℝ) : |t - clampOne t| ≤ |t| := by
  unfold clampOne
  rcases le_total t (-1) with h | h
  · have h1 : min 1 t = t := min_eq_right (by linarith)
    have h2 : max (-1) t = -1 := max_eq_left h
    rw [h1, h2, abs_of_nonpos (by linarith : t - -1 ≤ 0), abs_of_nonpos (by linarith : t ≤ 0)]
    linarith
  · rcases le_total t 1 with h' | h'
    · have h1 : min 1 t = t := min_eq_right h'
      have h2 : max (-1) t = t := max_eq_right h
      rw [h1, h2, sub_self, abs_zero]
      exact abs_nonneg t
    · have h1 : min 1 t = 1 := min_eq_left h'
      have h2 : max (-1 : ℝ) 1 = 1 := max_eq_right (by norm_num)
      rw [h1, h2, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - 1),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)]
      linarith

theorem abs_sub_clampOne_le_cube (t : ℝ) : |t - clampOne t| ≤ |t| ^ 3 := by
  unfold clampOne
  rcases le_total t (-1) with h | h
  · have h1 : min 1 t = t := min_eq_right (by linarith)
    have h2 : max (-1) t = -1 := max_eq_left h
    rw [h1, h2, abs_of_nonpos (by linarith : t - -1 ≤ 0), abs_of_nonpos (by linarith : t ≤ 0)]
    have h3 : 0 ≤ (-t) * (-t - 1) * (-t + 1) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith
  · rcases le_total t 1 with h' | h'
    · have h1 : min 1 t = t := min_eq_right h'
      have h2 : max (-1) t = t := max_eq_right h
      rw [h1, h2, sub_self, abs_zero]
      positivity
    · have h1 : min 1 t = 1 := min_eq_left h'
      have h2 : max (-1 : ℝ) 1 = 1 := max_eq_right (by norm_num)
      rw [h1, h2, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - 1),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)]
      have h3 : 0 ≤ t * (t - 1) * (t + 1) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      nlinarith

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The truncation `max(-1, min(1, f))` is bounded. -/
theorem memLp_top_clampOne {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    MemLp (fun x => clampOne (f x)) ∞ μ :=
  memLp_top_of_bound (continuous_clampOne.comp_aestronglyMeasurable hf) 1
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact abs_clampOne_le (f x))

/-- The remainder `f - max(-1, min(1, f))` of an `L³` function lies in
`L¹ ∩ L³ ⊆ L^{3/2}`, since it vanishes where `|f| ≤ 1`. -/
theorem memLp_three_halves_sub_clampOne {f : X → ℝ} (hf : MemLp f 3 μ) :
    MemLp (fun x => f x - clampOne (f x)) (3 / 2) μ := by
  have hm : AEStronglyMeasurable (fun x => f x - clampOne (f x)) μ :=
    hf.aestronglyMeasurable.sub
      (continuous_clampOne.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  have h3 : MemLp (fun x => f x - clampOne (f x)) 3 μ :=
    hf.of_le hm (ae_of_all _ fun x => by
      simp only [Real.norm_eq_abs]
      exact abs_sub_clampOne_le_abs (f x))
  have hf3 : MemLp f ((3 : ℕ) : ℝ≥0∞) μ := by simpa using hf
  have h1 : MemLp (fun x => f x - clampOne (f x)) 1 μ := by
    rw [memLp_one_iff_integrable]
    refine (hf3.integrable_norm_pow (by norm_num)).mono' hm (ae_of_all _ fun x => ?_)
    simp only [Real.norm_eq_abs]
    exact abs_sub_clampOne_le_cube (f x)
  exact TransformationsGauge.memLp_three_halves h1 h3

end Truncation

/-! ### Gauge transformations -/

section Gauge

variable (g : SpatialGauge)

theorem sum_gradient_sq (x : Position) :
    ∑ a, g.gradient a x ^ 2 = ‖g.gradientVector x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [SpatialGauge.gradientVector_apply, Real.norm_eq_abs, sq_abs]

theorem gradientVector_aesm :
    AEStronglyMeasurable g.gradientVector (volume : Measure Position) :=
  g.gradientVector_measurable.aestronglyMeasurable

/-- `∇g` as a bounded vector-valued class. -/
def gradientLp : Lp Vector ∞ (volume : Measure Position) :=
  (memLp_top_of_bound (gradientVector_aesm g) g.vectorBound
    (ae_of_all _ g.norm_gradientVector_le)).toLp g.gradientVector

theorem coeFn_gradientLp :
    (gradientLp g : Position → Vector) =ᵐ[volume] g.gradientVector :=
  MemLp.coeFn_toLp _

/-- The function `½|∇g|²`, written as in `energyShift`. -/
def halfSquare (x : Position) : ℝ := (1 / 2 : ℝ) * ∑ a, g.gradient a x ^ 2

theorem halfSquare_eq (x : Position) :
    halfSquare g x = (1 / 2 : ℝ) * ‖g.gradientVector x‖ ^ 2 := by
  rw [halfSquare, sum_gradient_sq]

theorem halfSquare_aesm : AEStronglyMeasurable (halfSquare g) (volume : Measure Position) := by
  have h : halfSquare g = fun x => (1 / 2 : ℝ) * ‖g.gradientVector x‖ ^ 2 :=
    funext (halfSquare_eq g)
  rw [h]
  exact ((g.gradientVector_measurable.norm.pow_const 2).const_mul (1 / 2 : ℝ)).aestronglyMeasurable

theorem norm_halfSquare_le (x : Position) :
    ‖halfSquare g x‖ ≤ (1 / 2 : ℝ) * g.vectorBound ^ 2 := by
  have h := g.norm_gradientVector_le x
  have h0 := norm_nonneg (g.gradientVector x)
  rw [halfSquare_eq, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2 * ‖g.gradientVector x‖ ^ 2)]
  nlinarith

/-- `½|∇g|²` as a bounded scalar class. -/
def halfSquareLp : Lp ℝ ∞ (volume : Measure Position) :=
  (memLp_top_of_bound (halfSquare_aesm g) _ (ae_of_all _ (norm_halfSquare_le g))).toLp
    (halfSquare g)

theorem coeFn_halfSquareLp :
    (halfSquareLp g : Position → ℝ) =ᵐ[volume] halfSquare g :=
  MemLp.coeFn_toLp _

/-- The scalar potential `½|∇g|²`. -/
def gaugeSquare : ScalarPotential := ofParts (halfSquareLp g) 0

/-- The vector potential `∇g`. -/
def gaugeGradient : VectorPotential := ofParts (gradientLp g) 0

theorem coeFn_gaugeSquare :
    ((gaugeSquare g).val : Position → ℝ) =ᵐ[volume] halfSquare g :=
  (coeFn_ofParts_zero (q := 3 / 2) (halfSquareLp g)).trans (coeFn_halfSquareLp g)

theorem coeFn_gaugeGradient :
    ((gaugeGradient g).val : Position → Vector) =ᵐ[volume] g.gradientVector :=
  (coeFn_ofParts_zero (q := 3) (gradientLp g)).trans (coeFn_gradientLp g)

/-- The potential `(½|∇g|², ∇g)` whose pairing is the gauge energy shift. -/
def gaugeBase : Potential := (gaugeSquare g, gaugeGradient g)

/-- A vector class tested against `∇g` stays in the same `Lr` space. -/
theorem memLp_inner_gradient {r : ℝ≥0∞} (f : Lp Vector r (volume : Measure Position)) :
    MemLp (fun x => inner ℝ (f x) (g.gradientVector x)) r volume :=
  (Lp.memLp f).of_le_mul (c := g.vectorBound)
    ((Lp.aestronglyMeasurable f).inner (gradientVector_aesm g))
    (ae_of_all _ fun x =>
      calc ‖inner ℝ (f x) (g.gradientVector x)‖ ≤ ‖f x‖ * ‖g.gradientVector x‖ :=
            norm_inner_le_norm _ _
        _ ≤ ‖f x‖ * g.vectorBound :=
            mul_le_mul_of_nonneg_left (g.norm_gradientVector_le x) (norm_nonneg _)
        _ = g.vectorBound * ‖f x‖ := mul_comm _ _)

/-- Bounded part of `A·∇g`: the `L∞` part of `A` and the truncated `L³` part. -/
def shiftLowFun (A : VectorPotential) (x : Position) : ℝ :=
  inner ℝ ((parts A).1 x) (g.gradientVector x) +
    clampOne (inner ℝ ((parts A).2 x) (g.gradientVector x))

/-- Remainder of `A·∇g` above height one, in `L^{3/2}`. -/
def shiftHighFun (A : VectorPotential) (x : Position) : ℝ :=
  inner ℝ ((parts A).2 x) (g.gradientVector x) -
    clampOne (inner ℝ ((parts A).2 x) (g.gradientVector x))

theorem memLp_shiftLow (A : VectorPotential) : MemLp (shiftLowFun g A) ∞ volume :=
  (memLp_inner_gradient g (parts A).1).add
    (memLp_top_clampOne (memLp_inner_gradient g (parts A).2).aestronglyMeasurable)

theorem memLp_shiftHigh (A : VectorPotential) : MemLp (shiftHighFun g A) (3 / 2) volume :=
  memLp_three_halves_sub_clampOne (memLp_inner_gradient g (parts A).2)

/-- The scalar potential `A·∇g ∈ L∞ + L^{3/2}`. -/
def scalarShift (A : VectorPotential) : ScalarPotential :=
  ofParts ((memLp_shiftLow g A).toLp (shiftLowFun g A))
    ((memLp_shiftHigh g A).toLp (shiftHighFun g A))

theorem coeFn_scalarShift (A : VectorPotential) :
    ((scalarShift g A).val : Position → ℝ) =ᵐ[volume]
      fun x => inner ℝ (A.val x) (g.gradientVector x) := by
  have h : ((scalarShift g A).val : Position → ℝ) =ᵐ[volume]
      fun x => (memLp_shiftLow g A).toLp (shiftLowFun g A) x +
        (memLp_shiftHigh g A).toLp (shiftHighFun g A) x :=
    coeFn_ofParts _ _
  filter_upwards [h, (memLp_shiftLow g A).coeFn_toLp, (memLp_shiftHigh g A).coeFn_toLp,
    coeFn_parts A] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, inner_add_left]
  simp only [shiftLowFun, shiftHighFun]
  ring

/-- The gauge action on potentials, `(v, A) ↦ (v + A·∇g + ½|∇g|², A + ∇g)`. -/
def gaugePotentialFun (u : Potential) : Potential :=
  (u.1 + scalarShift g u.2 + gaugeSquare g, u.2 + gaugeGradient g)

/-- Two gauge actions with opposite gradients cancel. -/
theorem gaugePotentialFun_cancel (g' : SpatialGauge)
    (hg : ∀ y, g'.gradientVector y = -g.gradientVector y) (u : Potential) :
    gaugePotentialFun g' (gaugePotentialFun g u) = u := by
  refine Prod.ext ?_ ?_
  · apply sum_ext_ae
    change ((u.1 + scalarShift g u.2 + gaugeSquare g +
        scalarShift g' (u.2 + gaugeGradient g) + gaugeSquare g').val : Position → ℝ)
      =ᵐ[volume] u.1.val
    filter_upwards [coeFn_sum_add (u.1 + scalarShift g u.2 + gaugeSquare g +
        scalarShift g' (u.2 + gaugeGradient g)) (gaugeSquare g'),
      coeFn_sum_add (u.1 + scalarShift g u.2 + gaugeSquare g)
        (scalarShift g' (u.2 + gaugeGradient g)),
      coeFn_sum_add (u.1 + scalarShift g u.2) (gaugeSquare g),
      coeFn_sum_add u.1 (scalarShift g u.2),
      coeFn_scalarShift g u.2, coeFn_gaugeSquare g,
      coeFn_scalarShift g' (u.2 + gaugeGradient g), coeFn_gaugeSquare g',
      coeFn_sum_add u.2 (gaugeGradient g), coeFn_gaugeGradient g]
      with x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀
    rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, halfSquare_eq, halfSquare_eq, hg x,
      norm_neg, inner_neg_right, inner_add_left, real_inner_self_eq_norm_sq]
    ring
  · apply sum_ext_ae
    change (((u.2 + gaugeGradient g) + gaugeGradient g').val : Position → Vector)
      =ᵐ[volume] u.2.val
    filter_upwards [coeFn_sum_add (u.2 + gaugeGradient g) (gaugeGradient g'),
      coeFn_sum_add u.2 (gaugeGradient g), coeFn_gaugeGradient g, coeFn_gaugeGradient g']
      with x h₁ h₂ h₃ h₄
    rw [h₁, h₂, h₃, h₄, hg x, add_neg_cancel_right]

/-- The gauge action on potentials as a bijection; the inverse is the action
of `-g`. -/
def gaugePotential : Potential ≃ Potential where
  toFun := gaugePotentialFun g
  invFun := gaugePotentialFun g.neg
  left_inv := gaugePotentialFun_cancel g g.neg g.neg_gradientVector
  right_inv := gaugePotentialFun_cancel g.neg g fun y => by
    rw [g.neg_gradientVector, neg_neg]

theorem gaugePotential_apply (u : Potential) :
    gaugePotential g u = (u.1 + scalarShift g u.2 + gaugeSquare g, u.2 + gaugeGradient g) :=
  rfl

/-- The current shift `ρ ∇g` as an element of the current space. -/
def shiftCurrent (d : Pair) : Current :=
  ofMemLp (fun x => densityL1 d x • g.gradientVector x) (g.shift_memLp_one d)
    (g.shift_memLp_three_halves d)

theorem fst_shiftCurrent (d : Pair) :
    (PhysicalPairSpace.fst (shiftCurrent g d) : Position → Vector) =ᵐ[volume]
      fun x => densityL1 d x • g.gradientVector x :=
  fst_ofMemLp_ae _ _ _

theorem shiftPair_fst (d : Pair) : (g.shiftPair d).1 = d.1 := by
  apply PhysicalPairSpace.fst_injective
  exact g.densityL1_shiftPair d

theorem shiftPair_snd (d : Pair) : (g.shiftPair d).2 = d.2 + shiftCurrent g d := by
  apply PhysicalPairSpace.ext_ae
  rw [map_add]
  change (currentL1 (g.shiftPair d) : Position → Vector) =ᵐ[volume]
    ⇑(currentL1 d + PhysicalPairSpace.fst (shiftCurrent g d))
  filter_upwards [g.currentL1_shiftPair d,
    Lp.coeFn_add (currentL1 d) (PhysicalPairSpace.fst (shiftCurrent g d)),
    fst_shiftCurrent g d] with x h₁ h₂ h₃
  simp only [h₁, h₂, h₃, Pi.add_apply]

/-- `⟨A·∇g, ρ⟩ = ⟨A, ρ∇g⟩`. -/
theorem pairing_scalarShift (A : VectorPotential) (d : Pair) :
    pairing (scalarShift g A) d.1 = pairing A (shiftCurrent g d) := by
  rw [pairing_density, pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [coeFn_scalarShift g A, fst_shiftCurrent g d] with x h₁ h₂
  rw [h₁, h₂, inner_smul_right]
  ring

/-- The gauge action is adjoint to the pair shift up to the base potential:
`⟨σ_g u, d⟩ = ⟨(½|∇g|², ∇g), d⟩ + ⟨u, (ρ, j + ρ∇g)⟩`. -/
theorem pairPotential_gaugePotential (u : Potential) (d : Pair) :
    pairPotential (gaugePotential g u) d =
      pairPotential (gaugeBase g) d + pairPotential u (g.shiftPair d) := by
  change pairing (u.1 + scalarShift g u.2 + gaugeSquare g) d.1 +
      pairing (u.2 + gaugeGradient g) d.2 =
    (pairing (gaugeSquare g) d.1 + pairing (gaugeGradient g) d.2) +
      (pairing u.1 (g.shiftPair d).1 + pairing u.2 (g.shiftPair d).2)
  have e₁ : pairing (u.1 + scalarShift g u.2 + gaugeSquare g) d.1 =
      pairing (u.1 + scalarShift g u.2) d.1 + pairing (gaugeSquare g) d.1 :=
    congrArg (fun L : Density →L[ℝ] ℝ => L d.1)
      (pairing_add (p := 3) (u.1 + scalarShift g u.2) (gaugeSquare g))
  have e₂ : pairing (u.1 + scalarShift g u.2) d.1 =
      pairing u.1 d.1 + pairing (scalarShift g u.2) d.1 :=
    congrArg (fun L : Density →L[ℝ] ℝ => L d.1) (pairing_add (p := 3) u.1 (scalarShift g u.2))
  have e₃ : pairing (u.2 + gaugeGradient g) d.2 =
      pairing u.2 d.2 + pairing (gaugeGradient g) d.2 :=
    congrArg (fun L : Current →L[ℝ] ℝ => L d.2)
      (pairing_add (p := 3 / 2) u.2 (gaugeGradient g))
  have e₄ : pairing u.1 (g.shiftPair d).1 = pairing u.1 d.1 :=
    congrArg (fun f : Density => pairing u.1 f) (shiftPair_fst g d)
  have e₅ : pairing u.2 (g.shiftPair d).2 =
      pairing u.2 d.2 + pairing u.2 (shiftCurrent g d) :=
    (congrArg (fun f : Current => pairing u.2 f) (shiftPair_snd g d)).trans
      (map_add (pairing u.2) d.2 (shiftCurrent g d))
  have e₆ := pairing_scalarShift g u.2 d
  linarith [e₁, e₂, e₃, e₄, e₅, e₆]

/-- The base potential pairs to the energy shift `∫ ∇g·j + ½ ∫ ρ|∇g|²`. -/
theorem pairPotential_gaugeBase (d : Pair) :
    pairPotential (gaugeBase g) d = g.energyShift d := by
  change pairing (gaugeSquare g) d.1 + pairing (gaugeGradient g) d.2 = _
  have h1 : (∫ x, (gaugeSquare g).val x * densityL1 d x) =
      (1 / 2 : ℝ) * ∫ x, (∑ a, g.gradient a x ^ 2) * densityL1 d x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [coeFn_gaugeSquare g] with x hx
    rw [hx, halfSquare]
    ring
  have hint : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun x => g.gradient a x * currentL1 d x a) volume := fun a _ =>
    (PhysicalPairSpace.current_component_integrable d a).bdd_mul
      (g.gradient_measurable a).aestronglyMeasurable (c := g.derivativeBound)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        exact g.abs_gradient_le a x)
  have h2 : (∫ x, inner ℝ ((gaugeGradient g).val x) (currentL1 d x)) =
      ∑ a, ∫ x, g.gradient a x * currentL1 d x a := by
    rw [← integral_finsetSum _ hint]
    apply integral_congr_ae
    filter_upwards [coeFn_gaugeGradient g] with x hx
    rw [hx, PiLp.inner_apply]
    simp only [Real.inner_apply, SpatialGauge.gradientVector_apply]
  rw [pairing_density, pairing_current, h1, h2, SpatialGauge.energyShift]
  ring

/-- **Gauge covariance of the Lieb functional.** If the constrained search
satisfies `F(ρ, j + ρ∇g) = F(ρ, j) + ∫ ∇g·j + ½ ∫ ρ|∇g|²`, so does the
Lieb functional. -/
theorem lieb_gauge {S : Type*} (A : DFT.StateModel S Pair)
    (hcov : ∀ d, DFT.search A (g.shiftPair d) =
      DFT.search A d + ((g.energyShift d : ℝ) : EReal)) (d : Pair) :
    DFT.lieb A (fun u p => pairPotential u p) (g.shiftPair d) =
      DFT.lieb A (fun u p => pairPotential u p) d + ((g.energyShift d : ℝ) : EReal) := by
  have h := Transformations.lieb_covariance A (fun u p => pairPotential u p) g.shiftEquiv
    (gaugePotential g) (gaugeBase g) (fun u e => pairPotential_gaugePotential g u e)
    (fun e => by
      show DFT.search A (g.shiftPair e) =
        DFT.search A e + ((pairPotential (gaugeBase g) e : ℝ) : EReal)
      rw [pairPotential_gaugeBase]
      exact hcov e) d
  calc DFT.lieb A (fun u p => pairPotential u p) (g.shiftPair d)
      = DFT.lieb A (fun u p => pairPotential u p) d +
          ((pairPotential (gaugeBase g) d : ℝ) : EReal) := h
    _ = _ := by rw [pairPotential_gaugeBase]

end Gauge

end GptLean.TransformationsPotentials
