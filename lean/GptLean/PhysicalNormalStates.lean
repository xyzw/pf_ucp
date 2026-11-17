import GptLean.PhysicalNormalTrace
import GptLean.PositiveForm
import GptLean.ObservableAssembly
import GptLean.DFT

/-!
Pure states, finite-energy normal states, and their actual mixtures on
one positive form and one Hilbert-space projection. Form additivity and
homogeneity follow from monotone bounded truncations. Rank-one inclusion
therefore supplies the pure embedding, and ordinary operator mixtures
supply the energy part of mixture closure.

Affinity of the physical density-current map is kept as a separate
observable identity. No attainment or constraint-preserving pure recovery
is assumed in this construction.
-/

noncomputable section

namespace GptLean.PhysicalNormalStates

open RemovalState PhotonLocalizationChannel PhysicalNormalTrace
open scoped ENNReal

section Forms

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
  {Tr : PositiveTraceData T} (E : PositiveForm Tr)

theorem expectation_add {x y : T} (hx : x ∈ Tr.positive) (hy : y ∈ Tr.positive) :
    E.expectation (x + y) = E.expectation x + E.expectation y := by
  unfold PositiveForm.expectation
  simp_rw [map_add, ENNReal.ofReal_add (E.nonneg _ x hx) (E.nonneg _ y hy)]
  exact (ENNReal.iSup_add_iSup_of_monotone
    (fun i j hij => ENNReal.ofReal_le_ofReal (E.monotone x hx hij))
    (fun i j hij => ENNReal.ofReal_le_ofReal (E.monotone y hy hij))).symm

theorem expectation_smul {r : ℝ} (hr : 0 ≤ r) (x : T) :
    E.expectation (r • x) = ENNReal.ofReal r * E.expectation x := by
  unfold PositiveForm.expectation
  simp_rw [map_smul, smul_eq_mul, ENNReal.ofReal_mul hr]
  exact (ENNReal.mul_iSup _ _).symm

theorem expectation_mix {x y : T} {t u : ℝ}
    (htx : t • x ∈ Tr.positive) (huy : u • y ∈ Tr.positive)
    (ht : 0 ≤ t) (hu : 0 ≤ u) :
    E.expectation (t • x + u • y) =
      ENNReal.ofReal t * E.expectation x + ENNReal.ofReal u * E.expectation y := by
  rw [expectation_add E htx huy, expectation_smul E ht, expectation_smul E hu]

theorem expectation_mix_finite {x y : T} {t u : ℝ}
    (htx : t • x ∈ Tr.positive) (huy : u • y ∈ Tr.positive)
    (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hx : E.expectation x < ⊤) (hy : E.expectation y < ⊤) :
    E.expectation (t • x + u • y) < ⊤ := by
  rw [expectation_mix E htx huy ht hu]
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hx,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hy⟩

theorem expectation_mix_toReal {x y : T} {t u : ℝ}
    (htx : t • x ∈ Tr.positive) (huy : u • y ∈ Tr.positive)
    (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hx : E.expectation x < ⊤) (hy : E.expectation y < ⊤) :
    (E.expectation (t • x + u • y)).toReal =
      t * (E.expectation x).toReal + u * (E.expectation y).toReal := by
  rw [expectation_mix E htx huy ht hu,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx.ne)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy.ne),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ht, ENNReal.toReal_ofReal hu]

end Forms

section States

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData H T}
  {normal : NormalTraceData R} {F : NormalFunctionalData R}
  (E : PositiveForm (positiveTrace normal F))
  (C : NormalConjugationData R) (P : H →L[ℂ] H)

abbrev Mixed := {s : E.State // C.conjugate P s.val = s.val}

abbrev Pure := {v : H // ‖v‖ = 1 ∧ P v = v ∧ E.expectation (R.rankOne v) < ⊤}

def pureToMixed (v : Pure E P) : Mixed E C P :=
  ⟨⟨R.rankOne v.val, R.rankOne_positive v.val,
    by change R.trace (R.rankOne v.val) = 1; rw [R.trace_rankOne, v.property.1]; norm_num,
    v.property.2.2⟩,
    by
      change C.conjugate P (R.rankOne v.val) = R.rankOne v.val
      rw [C.rankOne]
      exact congrArg R.rankOne v.property.2.1⟩

def mixture (m n : Mixed E C P) (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hs : t + u = 1) : Mixed E C P := by
  have hm := positive_smul normal F m.val.property.1 ht
  have hn := positive_smul normal F n.val.property.1 hu
  refine ⟨⟨t • m.val.val + u • n.val.val, R.add_positive hm hn, ?_, ?_⟩, ?_⟩
  · change R.trace (t • m.val.val + u • n.val.val) = 1
    have hmt : R.trace m.val.val = 1 := m.val.property.2.1
    have hnt : R.trace n.val.val = 1 := n.val.property.2.1
    rw [map_add, map_smul, map_smul, hmt, hnt]
    simpa only [smul_eq_mul, mul_one] using hs
  · exact expectation_mix_finite E hm hn ht hu m.val.property.2.2 n.val.property.2.2
  · rw [map_add, map_smul, map_smul, m.property, n.property]

@[simp] theorem mixture_val (m n : Mixed E C P) (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hs : t + u = 1) :
    (mixture E C P m n t u ht hu hs).val.val = t • m.val.val + u • n.val.val := rfl

theorem mixture_energy (m n : Mixed E C P) (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hs : t + u = 1) :
    (E.expectation (mixture E C P m n t u ht hu hs).val.val).toReal =
      t * (E.expectation m.val.val).toReal + u * (E.expectation n.val.val).toReal :=
  expectation_mix_toReal E (positive_smul normal F m.val.property.1 ht)
    (positive_smul normal F n.val.property.1 hu) ht hu m.val.property.2.2 n.val.property.2.2

variable {Pair : Type*}

def mixedModel (pair : Mixed E C P → Pair) : DFT.StateModel (Mixed E C P) Pair where
  energy m := (E.expectation m.val.val).toReal
  density := pair

def pureModel (pair : Mixed E C P → Pair) : DFT.StateModel (Pure E P) Pair where
  energy v := (E.expectation (R.rankOne v.val)).toReal
  density v := pair (pureToMixed E C P v)

def pureEmbedding (pair : Mixed E C P → Pair) :
    DFT.PureEmbedding (pureModel E C P pair) (mixedModel E C P pair) where
  toMixed := pureToMixed E C P
  energy_eq _ := rfl
  density_eq _ := rfl

variable [AddCommGroup Pair] [Module ℝ Pair]

/-- The state and energy parts of convexity are constructed. The sole
observable premise is the affine identity of the physical pair map. -/
theorem mixtureClosed (pair : Mixed E C P → Pair)
    (hpair : ∀ m n t u ht hu hs,
      pair (mixture E C P m n t u ht hu hs) = t • pair m + u • pair n) :
    DFT.MixtureClosed (mixedModel E C P pair) := by
  intro m n t u ht hu hs
  exact ⟨mixture E C P m n t u ht hu hs, hpair m n t u ht hu hs,
    (mixture_energy E C P m n t u ht hu hs).le⟩

theorem mixture_observable (J : FormObservable E)
    (m n : Mixed E C P) (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hs : t + u = 1) :
    J.value (mixture E C P m n t u ht hu hs).val.val =
      t * J.value m.val.val + u * J.value n.val.val := by
  have hlim := ((J.converges m.val.val m.val.property.1 m.val.property.2.2).const_mul t).add
    ((J.converges n.val.val n.val.property.1 n.val.property.2.2).const_mul u)
  have hlinear : Filter.Tendsto
      (fun k => J.approximation k (mixture E C P m n t u ht hu hs).val.val)
      Filter.atTop (nhds (t * J.value m.val.val + u * J.value n.val.val)) := by
    simpa only [mixture_val, map_add, map_smul, smul_eq_mul] using hlim
  exact tendsto_nhds_unique
    (J.converges _ (mixture E C P m n t u ht hu hs).val.property.1
      (mixture E C P m n t u ht hu hs).val.property.2.2) hlinear

variable {Test : Type*}

/-- Test separation converts linear bounded trace limits into affinity
of the entire physical density-current pair. -/
theorem mixture_pair_of_tests (pair : Mixed E C P → Pair)
    (test : Test → Pair →ₗ[ℝ] ℝ) (observable : Test → FormObservable E)
    (hseparates : ∀ p q, (∀ a, test a p = test a q) → p = q)
    (hmatch : ∀ a m, (observable a).value m.val.val = test a (pair m))
    (m n : Mixed E C P) (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hs : t + u = 1) :
    pair (mixture E C P m n t u ht hu hs) = t • pair m + u • pair n := by
  apply hseparates
  intro a
  have h := mixture_observable E C P (observable a) m n t u ht hu hs
  rw [hmatch, hmatch, hmatch] at h
  simpa only [map_add, map_smul, smul_eq_mul] using h

/-- Actual operator mixtures establish mixture closure once the
physical pair is identified by its linear form-observable tests. No
pair-affinity or mixture-closure conclusion is a premise. -/
theorem mixtureClosed_of_tests (pair : Mixed E C P → Pair)
    (test : Test → Pair →ₗ[ℝ] ℝ) (observable : Test → FormObservable E)
    (hseparates : ∀ p q, (∀ a, test a p = test a q) → p = q)
    (hmatch : ∀ a m, (observable a).value m.val.val = test a (pair m)) :
    DFT.MixtureClosed (mixedModel E C P pair) :=
  mixtureClosed E C P pair
    (mixture_pair_of_tests E C P pair test observable hseparates hmatch)

end States
end GptLean.PhysicalNormalStates
