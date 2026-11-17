import GptLean.PhysicalPFClosedGraph
import GptLean.PhysicalClosedForms

/-!
The positive normal Pauli--Fierz form from the closed common physical
graph. The only spectral input is the ordinary closed-operator theorem,
quantified over arbitrary Hilbert spaces and operators. Both its domain
and its pure-state value are identified with the constructed physical
reference graph before any mixed-state formula is used.
-/

noncomputable section

namespace GptLean.PhysicalPFReference

open MeasureTheory PhysicalFock PhysicalClosedForms PhysicalNormalTrace
open scoped ENNReal NNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

private theorem norm_sq_sum_two {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] (v : PiLp 2 (fun _ : I ⊕ Fin 2 => E)) :
    ‖v‖ ^ 2 = (∑ i, ‖v (Sum.inl i)‖ ^ 2) +
      ‖v (Sum.inr 0)‖ ^ 2 + ‖v (Sum.inr 1)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

private theorem norm_sq_sqrt_half {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (v : E) :
    ‖(Real.sqrt (1 / 2 : ℝ) : ℂ) • v‖ ^ 2 = (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by norm_num)]

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)

abbrev EnergyOutput := PiLp 2 (fun _ : I ⊕ Fin 2 => WaveSpace I)

def energyOutput (e : ℝ) : Reference I V →L[ℂ] EnergyOutput I :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I ⊕ Fin 2 => WaveSpace I)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Sum.elim
      (fun i => (Real.sqrt (1 / 2 : ℝ) : ℂ) • covariant I V C κ hκ M hbound e i)
      (fun n : Fin 2 => if n = 0 then radiation I V else potential I V)))

def energyGraphMap (e : ℝ) : Reference I V →L[ℂ] WaveSpace I × EnergyOutput I :=
  (inclusion I V).prod (energyOutput I V C κ hκ M hbound e)

@[simp] theorem energyOutput_inl (e : ℝ) (u : Reference I V) (i : I) :
    energyOutput I V C κ hκ M hbound e u (Sum.inl i) =
      (Real.sqrt (1 / 2 : ℝ) : ℂ) • covariant I V C κ hκ M hbound e i u := rfl

@[simp] theorem energyOutput_rad (e : ℝ) (u : Reference I V) :
    energyOutput I V C κ hκ M hbound e u (Sum.inr 0) = radiation I V u := by
  simp [energyOutput]

@[simp] theorem energyOutput_pot (e : ℝ) (u : Reference I V) :
    energyOutput I V C κ hκ M hbound e u (Sum.inr 1) = potential I V u := by
  simp [energyOutput]

theorem energyOutput_norm_sq (e : ℝ) (u : Reference I V) :
    ‖energyOutput I V C κ hκ M hbound e u‖ ^ 2 = energy I V C κ hκ M hbound e u := by
  simpa only [energyOutput_inl, energyOutput_rad, energyOutput_pot,
    norm_sq_sqrt_half, ← Finset.mul_sum, energy, kineticEnergy] using
      norm_sq_sum_two (energyOutput I V C κ hκ M hbound e u)

private theorem sqrt_two_half : Real.sqrt 2 * Real.sqrt (1 / 2 : ℝ) = 1 := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem norm_le_sqrt_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : E) (c : ℝ) (h : ‖(Real.sqrt (1 / 2 : ℝ) : ℂ) • v‖ ≤ c) :
    ‖v‖ ≤ Real.sqrt 2 * c := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at h
  have hs := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg 2)
  simpa only [← mul_assoc, sqrt_two_half, one_mul] using hs

theorem covariant_norm_le_energyOutput (e : ℝ) (i : I) (u : Reference I V) :
    ‖covariant I V C κ hκ M hbound e i u‖ ≤
      Real.sqrt 2 * ‖energyOutput I V C κ hκ M hbound e u‖ := by
  apply norm_le_sqrt_two (covariant I V C κ hκ M hbound e i u)
  exact PiLp.norm_apply_le (energyOutput I V C κ hκ M hbound e u) (Sum.inl i)

theorem formGraph_norm_le_energyGraph (e : ℝ) (u : Reference I V) :
    ‖formGraphMap I V C κ hκ M hbound e u‖ ≤
      (1 + Real.sqrt 2) * ‖energyGraphMap I V C κ hκ M hbound e u‖ := by
  let G := ‖energyGraphMap I V C κ hκ M hbound e u‖
  have hG : 0 ≤ G := norm_nonneg _
  have hv : ‖inclusion I V u‖ ≤ G := norm_fst_le (energyGraphMap I V C κ hκ M hbound e u)
  have he : ‖energyOutput I V C κ hκ M hbound e u‖ ≤ G :=
    norm_snd_le (energyGraphMap I V C κ hκ M hbound e u)
  have hrad : ‖radiation I V u‖ ≤ G := by
    exact ((congrArg norm (energyOutput_rad I V C κ hκ M hbound e u)).symm.le.trans
      (PiLp.norm_apply_le _ (Sum.inr 0))).trans he
  have hpot : ‖potential I V u‖ ≤ G := by
    exact ((congrArg norm (energyOutput_pot I V C κ hκ M hbound e u)).symm.le.trans
      (PiLp.norm_apply_le _ (Sum.inr 1))).trans he
  have hcov : ∀ i, ‖covariant I V C κ hκ M hbound e i u‖ ≤ (1 + Real.sqrt 2) * G := by
    intro i
    have h := (covariant_norm_le_energyOutput I V C κ hκ M hbound e i u).trans
      (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg 2))
    nlinarith
  have hbase : G ≤ (1 + Real.sqrt 2) * G := by nlinarith [Real.sqrt_nonneg 2]
  change max ‖inclusion I V u‖
    (max ‖fun i => covariant I V C κ hκ M hbound e i u‖
      (max ‖radiation I V u‖ ‖potential I V u‖)) ≤ _
  exact max_le (hv.trans hbase) (max_le
    ((pi_norm_le_iff_of_nonneg (by positivity)).mpr hcov)
    (max_le (hrad.trans hbase) (hpot.trans hbase)))

theorem energyGraph_closed (e : ℝ) :
    IsClosed (Set.range (energyGraphMap I V C κ hκ M hbound e)) := by
  let b : ℝ := formComparisonConstant I C κ hκ M hbound e
  have hb : 0 ≤ b := formComparisonConstant_nonneg I C κ hκ M hbound e
  let B : ℝ≥0 := ⟨b * (1 + Real.sqrt 2), mul_nonneg hb (by positivity)⟩
  apply closed_range_of_norm_bound (E := Reference I V) (F := WaveSpace I × EnergyOutput I)
    (energyGraphMap I V C κ hκ M hbound e) B
  intro u
  exact (reference_norm_le_formGraph I V C κ hκ M hbound e u).trans
    ((mul_le_mul_of_nonneg_left (formGraph_norm_le_energyGraph I V C κ hκ M hbound e u) hb).trans_eq
      (mul_assoc _ _ _).symm)

theorem reference_norm_le_energyGraph (e : ℝ) (u : Reference I V) :
    ‖u‖ ≤ (formComparisonConstant I C κ hκ M hbound e * (1 + Real.sqrt 2)) *
      ‖energyGraphMap I V C κ hκ M hbound e u‖ := by
  exact (reference_norm_le_formGraph I V C κ hκ M hbound e u).trans
    ((mul_le_mul_of_nonneg_left (formGraph_norm_le_energyGraph I V C κ hκ M hbound e u)
      (formComparisonConstant_nonneg I C κ hκ M hbound e)).trans_eq (mul_assoc _ _ _).symm)

def energyGraph (e : ℝ) : Submodule ℂ (WaveSpace I × EnergyOutput I) :=
  (energyGraphMap I V C κ hκ M hbound e).range

private theorem energyGraph_fst_zero (e : ℝ) (z : WaveSpace I × EnergyOutput I)
    (hz : z ∈ energyGraph I V C κ hκ M hbound e) (hzero : z.1 = 0) : z.2 = 0 := by
  obtain ⟨u, hu⟩ := hz
  have hv : inclusion I V u = 0 := (congrArg Prod.fst hu).trans hzero
  have hu0 : u = 0 := inclusion_injective I V (hv.trans (map_zero _).symm)
  rw [hu0, map_zero] at hu
  exact (congrArg Prod.snd hu).symm

def energyOperator (e : ℝ) : WaveSpace I →ₗ.[ℂ] EnergyOutput I :=
  (energyGraph I V C κ hκ M hbound e).toLinearPMap

theorem energyOperator_graph (e : ℝ) :
    (energyOperator I V C κ hκ M hbound e).graph = energyGraph I V C κ hκ M hbound e :=
  Submodule.toLinearPMap_graph_eq _ (energyGraph_fst_zero I V C κ hκ M hbound e)

theorem energyOperator_closed (e : ℝ) : (energyOperator I V C κ hκ M hbound e).IsClosed := by
  change IsClosed ((energyOperator I V C κ hκ M hbound e).graph :
    Set (WaveSpace I × EnergyOutput I))
  exact (congrArg (fun G : Submodule ℂ (WaveSpace I × EnergyOutput I) =>
    IsClosed (G : Set (WaveSpace I × EnergyOutput I)))
      (energyOperator_graph I V C κ hκ M hbound e)).mpr
        (energyGraph_closed I V C κ hκ M hbound e)

theorem reference_mem_energyOperator (e : ℝ) (u : Reference I V) :
    (inclusion I V u, energyOutput I V C κ hκ M hbound e u) ∈
      (energyOperator I V C κ hκ M hbound e).graph := by
  exact (congrArg (fun G : Submodule ℂ (WaveSpace I × EnergyOutput I) =>
    (inclusion I V u, energyOutput I V C κ hκ M hbound e u) ∈ G)
      (energyOperator_graph I V C κ hκ M hbound e)).mpr ⟨u, rfl⟩

variable (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

def normalEnergy (e : ℝ) : RemovalState.PositiveForm (B.traceData (H := WaveSpace I)) :=
  PhysicalClosedForms.positiveForm
    (S.resolve (WaveSpace I) (EnergyOutput I) (energyOperator I V C κ hκ M hbound e)
      (energyOperator_closed I V C κ hκ M hbound e)) B.normal (B.realization (WaveSpace I)).functional

theorem normalEnergy_rankOne (e : ℝ) (u : Reference I V) :
    (normalEnergy I V C κ hκ M hbound B S e).expectation
      ((B.realization (WaveSpace I)).rank.rankOne (inclusion I V u)) =
        ENNReal.ofReal (energy I V C κ hκ M hbound e u) := by
  exact (PhysicalClosedForms.positiveForm_graph _ _ _ _ _
    (reference_mem_energyOperator I V C κ hκ M hbound e u)).trans
      (congrArg ENNReal.ofReal (energyOutput_norm_sq I V C κ hκ M hbound e u))

theorem normalEnergy_source (e : ℝ) (u : ℕ → Reference I V) (x : B.Trace (WaveSpace I))
    (hu : HasSum (fun n => (B.realization (WaveSpace I)).rank.rankOne (inclusion I V (u n))) x) :
    (normalEnergy I V C κ hκ M hbound B S e).expectation x =
      ∑' n, ENNReal.ofReal (energy I V C κ hκ M hbound e (u n)) := by
  exact (PhysicalClosedForms.positiveForm_source _ _ _ hu).trans
    (tsum_congr fun n => normalEnergy_rankOne I V C κ hκ M hbound B S e (u n))

end GptLean.PhysicalPFReference
