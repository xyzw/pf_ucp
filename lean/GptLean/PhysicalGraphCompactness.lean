import GptLean.CompactGraphTrace
import GptLean.PhysicalLocalFreeGraph
import GptLean.PhotonLocalizationFormBoundsSources

/-!
Trace compactness on the physical free graph. The local spaces depend on
both cutoffs. Their compact inclusions yield the finite-rank trace tail,
while the original free energy controls the sum of local graph norms.
-/

noncomputable section
namespace GptLean.PhysicalGraphCompactness

open MeasureTheory Filter Topology PhysicalFock PhotonLocalization
  PhysicalLocalFreeGraph PhysicalLocalSupport SymmetricLift
open PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option maxHeartbeats 200000

variable (N : ℕ) (r : ℝ)

theorem cutSource_summable (L M : ℕ)
    (u : ℕ → SpatialFreeVector (I := Fin N × Fin 3) radiationRoot)
    (hu : ∀ k, (u k).value ∈ photonSupport N r)
    (hs : Summable (fun k => (u k).form)) :
    Summable (fun k => ‖cutSource N r L M (u k) (hu k)‖ ^ 2) := by
  have hm : Summable (fun k => ‖(u k).value‖ ^ 2) :=
    hs.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => (u k).mass_le_form)
  apply ((hs.mul_left 2).add
    (hm.mul_left (2 * Fintype.card (Fin N × Fin 3) *
      (physicalElectronicFamily (N := N) L).derivativeBound ^ 2))).of_nonneg_of_le
  · exact fun _ => sq_nonneg _
  · exact fun k => cutSource_norm_sq_le N r L M (u k) (hu k)

theorem cutSource_tsum_le (L M : ℕ)
    (u : ℕ → SpatialFreeVector (I := Fin N × Fin 3) radiationRoot)
    (hu : ∀ k, (u k).value ∈ photonSupport N r)
    (hs : Summable (fun k => (u k).form)) {E mass : ℝ}
    (hE : ∑' k, (u k).form ≤ E) (hmass : ∑' k, ‖(u k).value‖ ^ 2 ≤ mass) :
    ∑' k, ‖cutSource N r L M (u k) (hu k)‖ ^ 2 ≤
      2 * E + (2 * Fintype.card (Fin N × Fin 3) *
        (physicalElectronicFamily (N := N) L).derivativeBound ^ 2) * mass := by
  have hm : Summable (fun k => ‖(u k).value‖ ^ 2) :=
    hs.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => (u k).mass_le_form)
  calc
    _ ≤ ∑' k, (2 * (u k).form +
        (2 * Fintype.card (Fin N × Fin 3) *
          (physicalElectronicFamily (N := N) L).derivativeBound ^ 2) * ‖(u k).value‖ ^ 2) :=
      Summable.tsum_le_tsum (fun k => cutSource_norm_sq_le N r L M (u k) (hu k))
        (cutSource_summable N r L M u hu hs)
        ((hs.mul_left 2).add (hm.mul_left _))
    _ = 2 * (∑' k, (u k).form) +
        (2 * Fintype.card (Fin N × Fin 3) *
          (physicalElectronicFamily (N := N) L).derivativeBound ^ 2) *
            (∑' k, ‖(u k).value‖ ^ 2) :=
      ((hs.hasSum.mul_left 2).add (hm.hasSum.mul_left
        (2 * Fintype.card (Fin N × Fin 3) *
          (physicalElectronicFamily (N := N) L).derivativeBound ^ 2))).tsum_eq
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hE (by norm_num))
      (mul_le_mul_of_nonneg_left hmass (by positivity))

private theorem source_mass_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (v : ℕ → H)
    (htrace : ∀ a : H →L[ℂ] H, (φ (star a * a)).re = ∑' k, ‖a (v k)‖ ^ 2)
    (hmass : (φ 1).re ≤ 1) : ∑' k, ‖v k‖ ^ 2 ≤ 1 := by
  have ht := htrace 1
  simp only [star_one, one_mul, one_apply_eq_self] at ht
  exact ht.symm.trans_le hmass

def ofSpatialSources
    (hcompact : ∀ L M, TotallyBounded (supportValue N r L M '' Metric.closedBall 0 1))
    (φ : ℕ → (FullHilbert N →L[ℂ] FullHilbert N) →L[ℂ] ℂ)
    (u : ℕ → ℕ → SpatialFreeVector (I := Fin N × Fin 3) radiationRoot)
    (htrace : ∀ n a, (φ n (star a * a)).re = ∑' k, ‖a (u n k).value‖ ^ 2)
    (hmass : ∀ n, (φ n 1).re ≤ 1)
    (hsupport : ∀ n k, (u n k).value ∈ photonSupport N r)
    (hsummable : ∀ n, Summable (fun k => (u n k).form))
    (E : ℝ) (hE : ∀ n, ∑' k, (u n k).form ≤ E)
    (B : ℝ) (hnumber : ∀ M n,
      (φ n (1 - (cutoff (Sector photonMeasure) M).compLpL 2 volume)).re ≤ B / (M + 1))
    (ρ : ℕ → Lp ℝ 1 (volume : Measure ElectronicPosition))
    (helectronic : ∀ L n, (φ n ((1 - (physicalElectronicFamily (N := N) L).operator (K := PhotonFock)) ^ 2)).re ≤
      densityTail physicalElectronicRegion L (ρ n)) :
    GraphLocalFormData physicalElectronicRegion ρ φ (Domain N r) where
  numberCutoff M := (cutoff (Sector photonMeasure) M).compLpL 2 volume
  electronicCutoff L := (physicalElectronicFamily L).operator (K := PhotonFock)
  number_projection M := compLpL_projection _
    (numberSectorCutoff_projection (photonSector photonMeasure)
      (photonSector_isStarProjection photonMeasure) (photonSector_orthogonal photonMeasure) M)
  electronic_selfadjoint L := (physicalElectronicFamily L).operator_selfadjoint (K := PhotonFock)
  commute L M := (physicalElectronicFamily L).operator_commute _
  inclusion := supportValue N r
  compact := hcompact
  source n k := (u n k).value
  localVector L M n k := cutSource N r L M (u n k) (hsupport n k)
  trace := htrace
  local_identity L M n k := (supportValue_cutSource N r L M (u n k) (hsupport n k)).symm
  local_summable L M n := cutSource_summable N r L M (u n) (hsupport n) (hsummable n)
  energy L := 2 * E + 2 * Fintype.card (Fin N × Fin 3) *
    (physicalElectronicFamily (N := N) L).derivativeBound ^ 2
  local_energy L M n := by
    have hm : ∑' k, ‖(u n k).value‖ ^ 2 ≤ 1 :=
      source_mass_le (φ n) (fun k => (u n k).value) (htrace n) (hmass n)
    simpa only [mul_one] using cutSource_tsum_le N r L M
      (u n) (hsupport n) (hsummable n) (hE n) hm
  numberBound := B
  number_tail := hnumber
  electronic_tail := helectronic

theorem spatialSources_totallyBounded
    (hcompact : ∀ L M, TotallyBounded (supportValue N r L M '' Metric.closedBall 0 1))
    (φ : ℕ → (FullHilbert N →L[ℂ] FullHilbert N) →L[ℂ] ℂ)
    (u : ℕ → ℕ → SpatialFreeVector (I := Fin N × Fin 3) radiationRoot)
    (htrace : ∀ n a, (φ n (star a * a)).re = ∑' k, ‖a (u n k).value‖ ^ 2)
    (hpositive : ∀ n, PhotonTrace.IsPosFunctional (A := FullHilbert N →L[ℂ] FullHilbert N) (φ n))
    (hmass : ∀ n, (φ n 1).re ≤ 1)
    (hsupport : ∀ n k, (u n k).value ∈ photonSupport N r)
    (hsummable : ∀ n, Summable (fun k => (u n k).form))
    (E : ℝ) (hE : ∀ n, ∑' k, (u n k).form ≤ E)
    (B : ℝ) (hnumber : ∀ M n,
      (φ n (1 - (cutoff (Sector photonMeasure) M).compLpL 2 volume)).re ≤ B / (M + 1))
    (ρ : ℕ → Lp ℝ 1 (volume : Measure ElectronicPosition))
    (helectronic : ∀ L n, (φ n ((1 - (physicalElectronicFamily (N := N) L).operator (K := PhotonFock)) ^ 2)).re ≤
      densityTail physicalElectronicRegion L (ρ n))
    {ρlimit : Lp ℝ 1 (volume : Measure ElectronicPosition)}
    (hρ : Tendsto ρ atTop (𝓝 ρlimit)) :
    TotallyBounded (Set.range φ) := by
  let G := ofSpatialSources N r hcompact φ u htrace hmass hsupport hsummable
    E hE B hnumber ρ helectronic
  apply G.totallyBounded_of_density_tendsto hpositive hmass
    (fun _ => measurableSet_closedBall) ?_ ?_ hρ
  · intro L M hLM
    apply Metric.closedBall_subset_closedBall
    exact_mod_cast Nat.add_le_add_right hLM 1
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨L, hL⟩ := exists_nat_ge ‖x‖
    apply Set.mem_iUnion.mpr
    refine ⟨L, ?_⟩
    change dist x 0 ≤ (L : ℝ) + 1
    rw [dist_zero_right]
    linarith

variable (B : PhysicalNormalTrace.StandardNormalTraceBackground)
  (S : PhysicalClosedForms.StandardClosedFormBackground)

theorem free_graph (v : FullHilbert N)
    (hv : (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) B S).expectation
      ((B.realization (FullHilbert N)).rank.rankOne v) < ⊤) :
    ∃ u : SpatialFreeVector (I := Fin N × Fin 3) radiationRoot, u.value = v ∧
      (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) B S).expectation
        ((B.realization (FullHilbert N)).rank.rankOne v) = ENNReal.ofReal u.form := by
  obtain ⟨q, hq⟩ := (PhysicalFreeForm.normalEnergy_finite_iff (Fin N × Fin 3) B S v).mp hv
  refine ⟨PhysicalFreeHilbert.vector (Fin N × Fin 3)
    (PhysicalFreeHilbert.equiv (Fin N × Fin 3) q), ?_, ?_⟩
  · exact (PhysicalFreeHilbert.inclusion_equiv (Fin N × Fin 3) q).trans hq
  · have hnorm : ‖PhysicalFreeHilbert.equiv (Fin N × Fin 3) q‖ ^ 2 =
        PhysicalFreeForm.energy (Fin N × Fin 3) q :=
      PhysicalFreeForm.energyOutput_norm_sq (Fin N × Fin 3) q
    have hform := (PhysicalFreeHilbert.vector_form (Fin N × Fin 3)
      (PhysicalFreeHilbert.equiv (Fin N × Fin 3) q)).trans hnorm
    exact (congrArg (fun w => (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) B S).expectation
      ((B.realization (FullHilbert N)).rank.rankOne w)) hq).symm.trans
      ((PhysicalFreeForm.normalEnergy_rankOne (Fin N × Fin 3) B S q).trans
        (congrArg ENNReal.ofReal hform.symm))

theorem normalSources_totallyBounded
    (hcompact : ∀ L M, TotallyBounded (supportValue N r L M '' Metric.closedBall 0 1))
    (x : ℕ → B.Trace (FullHilbert N)) (hx : ∀ n, x n ∈ B.normal.states)
    (v : ℕ → ℕ → FullHilbert N)
    (hsource : ∀ n, HasSum (fun k => (B.realization (FullHilbert N)).rank.rankOne (v n k)) (x n))
    (hsupport : ∀ n k, v n k ∈ photonSupport N r)
    {E : ℝ} (hE : 0 ≤ E)
    (hfree : ∀ n, (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) B S).expectation (x n) ≤
      ENNReal.ofReal E)
    (numberBound : ℝ) (hnumber : ∀ M n,
      ((B.realization (FullHilbert N)).functional.repr (x n)
        (1 - (cutoff (Sector photonMeasure) M).compLpL 2 volume)).re ≤ numberBound / (M + 1))
    (ρ : ℕ → Lp ℝ 1 (volume : Measure ElectronicPosition))
    (helectronic : ∀ L n, ((B.realization (FullHilbert N)).functional.repr (x n)
      ((1 - (physicalElectronicFamily (N := N) L).operator (K := PhotonFock)) ^ 2)).re ≤
        densityTail physicalElectronicRegion L (ρ n))
    {ρlimit : Lp ℝ 1 (volume : Measure ElectronicPosition)}
    (hρ : Tendsto ρ atTop (𝓝 ρlimit)) :
    TotallyBounded (Set.range x) := by
  choose u hu hs hsum using fun n => spatial_sources_of_finite_form
    (I := Fin N × Fin 3) (K := PhotonFock) (R := radiationRoot)
    (A := (B.realization (FullHilbert N)).rank)
    (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) B S) (fun _ hx => hx)
    (free_graph N B S) (hsource n) hE (hfree n)
  have hpos n := (B.realization (FullHilbert N)).functional.positive B.normal (hx n).1
  have hmass n : ((B.realization (FullHilbert N)).functional.repr (x n) 1).re ≤ 1 := by
    rw [(B.realization (FullHilbert N)).functional.mass B.normal (hx n).1, (hx n).2]
  have htb := spatialSources_totallyBounded N r hcompact
    (fun n => (B.realization (FullHilbert N)).functional.repr (x n)) u
    (fun n a => by simpa only [hu] using (B.realization (FullHilbert N)).functional.square_trace (hsource n) a)
    hpos hmass (fun n k => by rw [hu]; exact hsupport n k)
    hs E hsum numberBound hnumber ρ helectronic hρ
  apply (totallyBounded_image_iff (B.realization (FullHilbert N)).functional.isometry.isUniformInducing).mp
  simpa only [← Set.range_comp, Function.comp_def] using htb

end GptLean.PhysicalGraphCompactness
