import GptLean.PhysicalPhotonTraceForm
import GptLean.InfraredRepair

/-!
The canonical momentum occupation density of a positive normal photon state.
Its number, hard-number, soft-energy and radiation moments are the expectations
of the actual momentum multiplier forms. The infrared moment interface is
constructed from these identities. The common electronic-to-photon partial
trace and the bound by the full Pauli–Fierz energy remain separate inputs.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationChannel RemovalState PhysicalNormalTrace
open scoped ENNReal

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData PhotonFock T}

namespace NormalPhoton

variable (normal : NormalTraceData R) (F : NormalFunctionalData R)

def source (x : T) (hx : x ∈ R.positive) : ℕ → PhotonFock :=
  (normal.positive_decomposition x hx).choose

omit [CompleteSpace T] in
theorem source_hasSum (x : T) (hx : x ∈ R.positive) :
    HasSum (fun n => R.rankOne (source normal x hx n)) x :=
  (normal.positive_decomposition x hx).choose_spec

def density (x : T) (hx : x ∈ R.positive) : PhotonMode → ℝ≥0∞ :=
  ensemblePhotonDensity (source normal x hx)

omit [CompleteSpace T] in
theorem density_measurable (x : T) (hx : x ∈ R.positive) : Measurable (density normal x hx) :=
  ensemblePhotonDensity_measurable _

include F in
theorem density_eq_of_source (x : T) (hx : x ∈ R.positive)
    {v : ℕ → PhotonFock} (hv : HasSum (fun n => R.rankOne (v n)) x) :
    density normal x hx =ᵐ[photonMeasure] ensemblePhotonDensity v :=
  ensemblePhotonDensity_independent normal F (source_hasSum normal x hx) hv

theorem density_moment (q : PhotonMode → ℝ≥0∞) (hq : Measurable q)
    (x : T) (hx : x ∈ R.positive) :
    (secondQuantizedPositiveForm q hq normal F).expectation x =
      ∫⁻ p, q p * density normal x hx p ∂photonMeasure :=
  secondQuantizedPositiveForm_occupation q hq normal F (source_hasSum normal x hx)

def frequency (p : PhotonMode) : ℝ := ‖p.1‖

theorem frequency_measurable : Measurable frequency := measurable_fst.norm

theorem frequency_positive : ∀ᵐ p ∂photonMeasure, 0 < frequency p := by
  have h := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Gaussian.FieldSpace))
    (ν := (Measure.count : Measure (Fin 2)))).ae (Measure.ae_ne volume 0)
  filter_upwards [h] with p hp
  exact norm_pos_iff.mpr hp

def hardWeight (κ : ℝ) : PhotonMode → ℝ≥0∞ :=
  {p | κ ≤ frequency p}.indicator (fun _ => 1)

def softWeight (κ : ℝ) : PhotonMode → ℝ≥0∞ :=
  {p | frequency p < κ}.indicator (fun p => ENNReal.ofReal (frequency p))

theorem hardWeight_measurable (κ : ℝ) : Measurable (hardWeight κ) :=
  measurable_const.indicator (measurableSet_le measurable_const frequency_measurable)

theorem softWeight_measurable (κ : ℝ) : Measurable (softWeight κ) :=
  frequency_measurable.ennreal_ofReal.indicator (measurableSet_lt frequency_measurable measurable_const)

def numberForm : PositiveForm (positiveTrace normal F) :=
  secondQuantizedPositiveForm (fun _ => 1) measurable_const normal F

def radiationForm : PositiveForm (positiveTrace normal F) :=
  secondQuantizedPositiveForm (fun p => ENNReal.ofReal (frequency p))
    frequency_measurable.ennreal_ofReal normal F

def hardNumberForm (κ : ℝ) : PositiveForm (positiveTrace normal F) :=
  secondQuantizedPositiveForm (hardWeight κ) (hardWeight_measurable κ) normal F

def softEnergyForm (κ : ℝ) : PositiveForm (positiveTrace normal F) :=
  secondQuantizedPositiveForm (softWeight κ) (softWeight_measurable κ) normal F

theorem numberForm_rankOne (u : PhotonFock) :
    (numberForm normal F).expectation (R.rankOne u) = photonNumberForm photonMeasure u := by
  rw [numberForm, secondQuantizedPositiveForm_rankOne, photonMoment_one]

theorem radiationForm_rankOne (u : PhotonFock) :
    (radiationForm normal F).expectation (R.rankOne u) = PhysicalFock.radiationForm u := by
  rw [radiationForm, secondQuantizedPositiveForm_rankOne]
  exact photonMoment_frequency u

theorem density_number (x : T) (hx : x ∈ R.positive) :
    (numberForm normal F).expectation x = ∫⁻ p, density normal x hx p ∂photonMeasure := by
  simpa only [numberForm, one_mul] using density_moment normal F (fun _ => 1) measurable_const x hx

theorem density_radiation (x : T) (hx : x ∈ R.positive) :
    (radiationForm normal F).expectation x =
      ∫⁻ p, ENNReal.ofReal (frequency p) * density normal x hx p ∂photonMeasure :=
  density_moment normal F _ frequency_measurable.ennreal_ofReal x hx

theorem density_hardNumber (κ : ℝ) (x : T) (hx : x ∈ R.positive) :
    (hardNumberForm normal F κ).expectation x =
      ∫⁻ p in {p | κ ≤ frequency p}, density normal x hx p ∂photonMeasure := by
  rw [hardNumberForm, density_moment normal F _ (hardWeight_measurable κ) x hx]
  have he : (fun p => hardWeight κ p * density normal x hx p) =
      {p | κ ≤ frequency p}.indicator (density normal x hx) := by
    funext p
    simp only [hardWeight, ← Set.indicator_mul_left, one_mul]
  rw [he, lintegral_indicator (measurableSet_le measurable_const frequency_measurable)]

theorem density_softEnergy (κ : ℝ) (x : T) (hx : x ∈ R.positive) :
    (softEnergyForm normal F κ).expectation x =
      ∫⁻ p in {p | frequency p < κ}, ENNReal.ofReal (frequency p) * density normal x hx p
        ∂photonMeasure := by
  rw [softEnergyForm, density_moment normal F _ (softWeight_measurable κ) x hx]
  have he : (fun p => softWeight κ p * density normal x hx p) =
      {p | frequency p < κ}.indicator (fun p => ENNReal.ofReal (frequency p) * density normal x hx p) := by
    funext p
    exact (Set.indicator_mul_left _ _ _).symm
  rw [he, lintegral_indicator (measurableSet_lt frequency_measurable measurable_const)]

/-- Finite actual radiation expectation yields the complete momentum-moment law. -/
theorem hasPhotonDensity (x : T) (hx : x ∈ R.positive)
    (hfinite : (radiationForm normal F).expectation x < ⊤) :
    HardLayerCake.HasPhotonDensity photonMeasure frequency (density normal x hx)
      (fun κ => ((hardNumberForm normal F κ).expectation x).toReal)
      (fun κ => ((softEnergyForm normal F κ).expectation x).toReal)
      ((radiationForm normal F).expectation x).toReal where
  measurable := density_measurable normal x hx
  finite := by rwa [← density_radiation normal F x hx]
  numHard_eq κ := congrArg ENNReal.toReal (density_hardNumber normal F κ x hx)
  Esoft_eq κ := congrArg ENNReal.toReal (density_softEnergy normal F κ x hx)
  Erad_eq := congrArg ENNReal.toReal (density_radiation normal F x hx)

/-- The moment record is derived on any common state model whose actual photon
marginal has finite radiation bounded by the full energy. The remaining cutoff
integrability assumptions are exactly the infrared assumptions of the article. -/
def infraredMoments {State Pair : Type*} (A : DFT.StateModel State Pair)
    (photon : State → T) (hpositive : ∀ s, photon s ∈ R.positive)
    (hradFinite : ∀ s, (radiationForm normal F).expectation (photon s) < ⊤)
    (hradBound : ∀ s, ((radiationForm normal F).expectation (photon s)).toReal ≤ A.energy s)
    (w : PhotonMode → ℝ≥0∞) (hw : Measurable w)
    (hwFinite : ∫⁻ p, w p ∂photonMeasure < ⊤)
    (hwWeighted : ∫⁻ p, w p * ENNReal.ofReal (1 / frequency p) ∂photonMeasure < ⊤) :
    InfraredRepair.InfraredMoments A
      (fun s => (numberForm normal F).expectation (photon s)) photonMeasure frequency w where
  dispersion_measurable := frequency_measurable
  dispersion_positive := frequency_positive
  cutoff_measurable := hw
  cutoff_finite := hwFinite
  weighted_finite := hwWeighted
  photonDensity s := density normal (photon s) (hpositive s)
  hardNumber s κ := ((hardNumberForm normal F κ).expectation (photon s)).toReal
  softEnergy s κ := ((softEnergyForm normal F κ).expectation (photon s)).toReal
  radiationEnergy s := ((radiationForm normal F).expectation (photon s)).toReal
  moments s := hasPhotonDensity normal F (photon s) (hpositive s) (hradFinite s)
  radiation_le := hradBound
  number_eq s := density_number normal F (photon s) (hpositive s)

end NormalPhoton
end GptLean.PhysicalFock
