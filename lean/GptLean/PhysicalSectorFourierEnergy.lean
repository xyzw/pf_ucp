import GptLean.PhysicalSpatialSectorFourier
import GptLean.PhysicalSectorMomentumEnergy
import GptLean.PhysicalSectorCoordinateIdentities
import GptLean.PhysicalFourierGraph
import GptLean.PhysicalH1FourierEnergy
import GptLean.PhysicalFreeHilbert

/-!
The actual free graph controls the joint fractional Fourier energy of
each physical photon sector. Electronic Fourier transform preserves the
closed radiation graph. Sector evaluation is a contraction, so the
electronic and radiation estimates use the same full Fock vector.
-/

noncomputable section
namespace GptLean.PhysicalSectorCoordinates

open MeasureTheory PhysicalFock PhysicalSectorMeasures PhotonLocalization
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
set_option Elab.async false

private theorem enorm_sq_ofReal {H : Type*} [NormedAddCommGroup H] (u : H) :
    ‖u‖ₑ ^ 2 = ENNReal.ofReal (‖u‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

section Electronic
variable {I H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [DecidableEq I] in
private theorem fourier_mass (u : Lp H 2 (volume : Measure (EuclideanSpace ℝ I))) :
    (∫⁻ ξ, ‖Lp.fourierTransformₗᵢ (EuclideanSpace ℝ I) H u ξ‖ₑ ^ 2) =
      ENNReal.ofReal (‖u‖ ^ 2) :=
  (l2_enorm_sq_lintegral (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ I) H u)).symm.trans
    ((enorm_sq_ofReal _).trans (congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2))
      ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ I) H).norm_map u)))

/-- The sum of unscaled electronic frequencies is controlled by the actual weak gradient. -/
theorem electronic_frequency_norm_bound (u : ElectronicH1Complex.ComplexH1 H I) :
    (∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) *
      ‖PhysicalH1Fourier.fourier (ElectronicH1Complex.value u) ξ‖ₑ ^ 2) ≤
        ENNReal.ofReal (∑ i, ‖ElectronicH1Complex.derivative i u‖ ^ 2) := by
  have he (ξ : EuclideanSpace ℝ I) :
      ENNReal.ofReal (‖ξ‖ ^ 2) = ∑ i : I, ENNReal.ofReal ((ξ i) ^ 2) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)
  simp_rw [he, Finset.sum_mul]
  rw [lintegral_finsetSum Finset.univ (fun i _ => by fun_prop)]
  calc
    _ ≤ ∑ i : I, ENNReal.ofReal (‖ElectronicH1Complex.derivative i u‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => PhysicalH1Fourier.complex_coordinate_frequency_bound u i
    _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)).symm

private theorem electronic_mass_frequency_bound (u : ElectronicH1Complex.ComplexH1 H I) :
    (∫⁻ ξ, ENNReal.ofReal (1 + ‖ξ‖ ^ 2) *
      ‖PhysicalH1Fourier.fourier (ElectronicH1Complex.value u) ξ‖ₑ ^ 2) ≤
      ENNReal.ofReal (‖ElectronicH1Complex.value u‖ ^ 2 +
        ∑ i, ‖ElectronicH1Complex.derivative i u‖ ^ 2) := by
  have he (ξ : EuclideanSpace ℝ I) : ENNReal.ofReal (1 + ‖ξ‖ ^ 2) =
      1 + ENNReal.ofReal (‖ξ‖ ^ 2) := by
    rw [ENNReal.ofReal_add (by norm_num) (sq_nonneg _), ENNReal.ofReal_one]
  simp_rw [he, add_mul, one_mul]
  rw [lintegral_add_left (by fun_prop)]
  have hm : (∫⁻ ξ, ‖PhysicalH1Fourier.fourier (ElectronicH1Complex.value u) ξ‖ₑ ^ 2) =
      ENNReal.ofReal (‖ElectronicH1Complex.value u‖ ^ 2) := by
    rw [← l2_enorm_sq_lintegral, enorm_sq_ofReal, PhysicalH1Fourier.fourier.norm_map]
  rw [hm, ENNReal.ofReal_add (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact add_le_add le_rfl (electronic_frequency_norm_bound u)

end Electronic

private theorem momentum_free_weight (m : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (v : Sector photonMeasure m) :
    (∫⁻ y, ENNReal.ofReal (c + momentumRadiationSymbol m y) *
      ‖sectorMomentum m v y‖ₑ ^ 2) =
        ENNReal.ofReal c * ‖v‖ₑ ^ 2 + sectorRadiationForm m v := by
  have hr y : 0 ≤ momentumRadiationSymbol m y :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  simp_rw [ENNReal.ofReal_add hc (hr _), add_mul]
  rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
    ← l2_enorm_sq_lintegral, (sectorMomentum m).enorm_map,
    ← sectorRadiationForm_momentum]

private theorem sectorFreeSymbol_split (N m : ℕ) (ξ : Configuration (N + m)) :
    sectorFreeSymbol N m ξ =
      1 + ‖(configurationSplit N m ξ).1‖ ^ 2 +
        momentumRadiationSymbol m (configurationSplit N m ξ).2 := by
  have he : ‖(configurationSplit N m ξ).1‖ ^ 2 =
      ∑ i : Fin N, ‖SymmetricLift.particle ξ (Fin.castAdd m i)‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [← configurationSplit_particle_fst, EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [he]
  simp only [sectorFreeSymbol, momentumRadiationSymbol, configurationSplit_particle_snd]

private def electronicSource {N : ℕ}
    (u : SpatialFreeVector (I := Fin N × Fin 3) radiationRoot) :
    ElectronicH1Complex.ComplexH1 PhotonFock (Fin N × Fin 3) :=
  ⟨(u.value, u.derivative), u.weak⟩

private theorem fourier_coordinate_ae (N m : ℕ)
    (u : PhysicalFreeForm.WaveSpace (Fin N × Fin 3)) :
    Lp.fourierTransformₗᵢ (Configuration N) (Sector photonMeasure m)
      (PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume m u) =ᵐ[volume]
        fun ξ => (Lp.fourierTransformₗᵢ (Configuration N) PhotonFock u ξ) m := by
  have h : Lp.fourierTransformₗᵢ (Configuration N) (Sector photonMeasure m)
      (PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume m u) =
    PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume m
      (Lp.fourierTransformₗᵢ (Configuration N) PhotonFock u) :=
    PhysicalL2FourierTransport.fourier_compLpL
      (lp.evalCLM ℂ (Sector photonMeasure) 2 m) u
  have hc : Lp.fourierTransformₗᵢ (Configuration N) (Sector photonMeasure m)
      (PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume m u) =ᵐ[volume]
      PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume m
        (Lp.fourierTransformₗᵢ (Configuration N) PhotonFock u) :=
    Filter.Eventually.of_forall fun ξ =>
      congrArg (fun v : Lp (Sector photonMeasure m) 2
        (volume : Measure (Configuration N)) => v ξ) h
  exact hc.trans (PhysicalFiniteSectorCoordinates.coordinate_ae _ _ _ _)

/-- The joint electronic and photon Fourier symbol is bounded by the actual free form. -/
theorem spatialSector_free_energy_le (N m : ℕ)
    (u : SpatialFreeVector (I := Fin N × Fin 3) radiationRoot) :
    sectorFourierEnergy
        (Lp.fourierTransformₗᵢ (PhotonSectorPosition N m) (Coefficient m))
        (sectorFreeSymbol N m)
        (spatialSectorPosition N m
          (PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume m u.value)) ≤
      ENNReal.ofReal u.form := by
  let F := Lp.fourierTransformₗᵢ (Configuration N) PhotonFock u.value
  let R := Lp.fourierTransformₗᵢ (Configuration N) PhotonFock u.radiation
  have hgraph : ∀ᵐ ξ ∂volume, (F ξ, R ξ) ∈ radiationRoot.graph :=
    PhysicalFourierGraph.fourier_mem_graph (X := Configuration N)
      (H := PhotonFock) (K := PhotonFock) radiationRoot.graph radiationRoot_closed
      u.value u.radiation u.radiation_graph
  have hweight := spatialSectorPosition_fourier_weighted N m
    (PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume m u.value)
    (fun z : Configuration N × Configuration m =>
      ENNReal.ofReal (1 + ‖z.1‖ ^ 2 + momentumRadiationSymbol m z.2)) (by
        exact ((measurable_const.add (measurable_fst.norm.pow_const 2)).add
          ((momentumRadiationSymbol_measurable m).comp measurable_snd)).ennreal_ofReal)
  have hsplit : sectorFourierEnergy
      (Lp.fourierTransformₗᵢ (PhotonSectorPosition N m) (Coefficient m))
      (sectorFreeSymbol N m)
      (spatialSectorPosition N m
        (PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume m u.value)) =
      ∫⁻ ξ, ENNReal.ofReal (1 + ‖(configurationSplit N m ξ).1‖ ^ 2 +
        momentumRadiationSymbol m (configurationSplit N m ξ).2) *
        ‖Lp.fourierTransformₗᵢ (Configuration (N + m)) (Coefficient m)
          (spatialSectorPosition N m
            (PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume m u.value)) ξ‖ₑ ^ 2 :=
    lintegral_congr fun ξ => congrArg (fun c : ℝ => ENNReal.ofReal c *
      ‖Lp.fourierTransformₗᵢ (Configuration (N + m)) (Coefficient m)
        (spatialSectorPosition N m
          (PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume m u.value)) ξ‖ₑ ^ 2)
      (sectorFreeSymbol_split N m ξ)
  calc
    _ = ∫⁻ ξ, ∫⁻ y, ENNReal.ofReal (1 + ‖ξ‖ ^ 2 + momentumRadiationSymbol m y) *
        ‖sectorMomentum m
          (Lp.fourierTransformₗᵢ (Configuration N) (Sector photonMeasure m)
            (PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume m u.value) ξ) y‖ₑ ^ 2 :=
      hsplit.trans hweight
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (1 + ‖ξ‖ ^ 2) * ‖F ξ‖ₑ ^ 2 + ‖R ξ‖ₑ ^ 2 := by
      apply lintegral_mono_ae
      filter_upwards [fourier_coordinate_ae N m u.value, hgraph] with ξ hc hg
      rw [hc, momentum_free_weight m (1 + ‖ξ‖ ^ 2) (by positivity)]
      have hn : ‖F ξ m‖ₑ ^ 2 ≤ ‖F ξ‖ₑ ^ 2 := by
        exact pow_le_pow_left₀ (by positivity)
          (enorm_le_iff_norm_le.mpr (lp.norm_apply_le_norm (by norm_num) (F ξ) m)) 2
      have hr : sectorRadiationForm m (F ξ m) ≤ ‖R ξ‖ₑ ^ 2 := by
        have ht : sectorRadiationForm m (F ξ m) ≤ radiationForm (F ξ) :=
          ENNReal.le_tsum m
        obtain ⟨v, hv, hR⟩ := radiationRoot.mem_graph_iff.mp hg
        change (v : PhotonFock) = F ξ at hv
        change radiationRoot v = R ξ at hR
        have he : radiationForm (F ξ) = ‖R ξ‖ₑ ^ 2 := by
          rw [← hv, ← hR, radiationRoot_energy, enorm_sq_ofReal]
        exact ht.trans he.le
      exact add_le_add (mul_le_mul' le_rfl hn) hr
    _ = (∫⁻ ξ, ENNReal.ofReal (1 + ‖ξ‖ ^ 2) * ‖F ξ‖ₑ ^ 2) +
        ENNReal.ofReal (‖u.radiation‖ ^ 2) := by
      have hm : (∫⁻ ξ, ‖R ξ‖ₑ ^ 2) = ENNReal.ofReal (‖u.radiation‖ ^ 2) :=
        fourier_mass u.radiation
      rw [lintegral_add_left (by fun_prop)]
      exact congrArg (fun t : ℝ≥0∞ =>
        (∫⁻ ξ, ENNReal.ofReal (1 + ‖ξ‖ ^ 2) * ‖F ξ‖ₑ ^ 2) + t) hm
    _ ≤ ENNReal.ofReal (‖u.value‖ ^ 2 + ∑ i, ‖u.derivative i‖ ^ 2) +
        ENNReal.ofReal (‖u.radiation‖ ^ 2) :=
      add_le_add (electronic_mass_frequency_bound (electronicSource u)) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (sq_nonneg _)]
      rfl

/-- Every actual free graph vector satisfies the sector estimate used by Rellich. -/
theorem half_energy_le (N m : ℕ)
    (q : PhysicalFreeHilbert.Space (Fin N × Fin 3)) :
    sectorFourierEnergy
        (Lp.fourierTransformₗᵢ (PhotonSectorPosition N m) (Coefficient m))
        (sectorHalfSymbol N m)
        (spatialSectorPosition N m
          (PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume m
            (PhysicalFreeHilbert.inclusion (Fin N × Fin 3) q))) ≤
      ENNReal.ofReal (‖q‖ ^ 2) := by
  have hcoercivity := sectorFourierEnergy_coercivity (N := N) (m := m)
    (Lp.fourierTransformₗᵢ (PhotonSectorPosition N m) (Coefficient m))
    (spatialSectorPosition N m
      (PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume m
        (PhysicalFreeHilbert.inclusion (Fin N × Fin 3) q)))
  have hfree := spatialSector_free_energy_le N m
    (PhysicalFreeHilbert.vector (Fin N × Fin 3) q)
  exact hcoercivity.trans
    (hfree.trans_eq (congrArg ENNReal.ofReal (PhysicalFreeHilbert.vector_form _ q)))

end GptLean.PhysicalSectorCoordinates
