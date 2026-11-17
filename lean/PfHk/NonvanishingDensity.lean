import GptLean.PhysicalElectronicDensity

/-!
Joint almost-everywhere nonvanishing implies strict positivity of the
actual electronic density. The argument uses the constructed Fubini source
and the measure-preserving split of one electron from the configuration.
It does not assume unique continuation and does not require antisymmetry.
-/

noncomputable section

namespace PfHk.NonvanishingDensity

open MeasureTheory Filter GptLean GptLean.PhysicalSourceFubini
  GptLean.PhysicalSourceMarginal GptLean.PhysicalSourceCoordinates
  GptLean.PhysicalElectronicDensity
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- Nonzero almost-everywhere product-space vectors have nonzero L² fibers
for almost every first coordinate. Nontriviality of the spectator measure
is explicit, including when that space has dimension zero. -/
theorem curry_ne_zero_ae {X Y H : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] [IsSeparable ν]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [TopologicalSpace.SeparableSpace H]
    (hν : ν ≠ 0) (u : ProductL2 (H := H) (μ := μ) (ν := ν))
    (hu : ∀ᵐ p ∂μ.prod ν, u p ≠ 0) :
    ∀ᵐ x ∂μ, curry u x ≠ 0 := by
  have : (ae ν).NeBot := ae_neBot.mpr hν
  filter_upwards [curry_ae u, section_represents_ae u,
    Measure.ae_ae_of_ae_prod hu] with x hc hs hn
  intro hz
  have hsz : sourceSection u x = 0 := hc.symm.trans hz
  have hz_ae : ∀ᵐ y ∂ν, u (x, y) = 0 :=
    hs.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hsz)
  obtain ⟨y, hy, hny⟩ := (hz_ae.and hn).exists
  exact hny hy

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

/-- The actual selected-particle source is nonzero almost everywhere when
the original configuration-space wavefunction is nonzero almost everywhere. -/
theorem particleMap_ne_zero_ae (i : Fin N) (u : Wave (N := N) (H := H))
    (hu : ∀ᵐ z ∂volume, u z ≠ 0) :
    ∀ᵐ x ∂volume, particleMap i u x ≠ 0 := by
  let v := productMap (split i) (split_symm_measurePreserving i) u
  have hsplit : ∀ᵐ p ∂(volume : Measure PhysicalSourceCoordinates.Position).prod
      (volume : Measure (Spectator i)), u ((split i).symm p) ≠ 0 :=
    (split_symm_measurePreserving i).quasiMeasurePreserving.ae hu
  have hv : ∀ᵐ p ∂(volume : Measure PhysicalSourceCoordinates.Position).prod
      (volume : Measure (Spectator i)), v p ≠ 0 := by
    filter_upwards [Lp.coeFn_compMeasurePreserving u (split_symm_measurePreserving i),
      hsplit] with p hp hn
    change (Lp.compMeasurePreserving (split i).symm (split_symm_measurePreserving i) u) p ≠ 0
    rw [hp]
    exact hn
  exact curry_ne_zero_ae (NeZero.ne (volume : Measure (Spectator i))) v hv

/-- The positivity conclusion for the physical electronic L¹ density.
Choosing `i : Fin N` expresses positive particle number. The density sums
all electron marginals, so no fermionic symmetry hypothesis is necessary. -/
theorem density_pos_ae (i : Fin N) (u : Wave (N := N) (H := H))
    (hu : ∀ᵐ z ∂volume, u z ≠ 0) :
    ∀ᵐ x ∂volume, 0 < density u x := by
  filter_upwards [particleMap_ne_zero_ae i u hu, density_ae u] with x hx hd
  rw [hd, densityFunction]
  exact lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hx))
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖particleMap j u x‖) (Finset.mem_univ i))

/-- Equivalent norm formulation matching the nonvanishing assertion of
the unique-continuation theorem. -/
theorem density_pos_ae_of_norm_pos (i : Fin N) (u : Wave (N := N) (H := H))
    (hu : ∀ᵐ z ∂volume, 0 < ‖u z‖) :
    ∀ᵐ x ∂volume, 0 < density u x :=
  density_pos_ae i u (hu.mono fun _ hz => norm_pos_iff.mp hz)

/-- The same positivity statement directly for the density component of
the article's constructed density-current pair. The current derivative
arguments are arbitrary and do not enter the conclusion. -/
theorem pair_density_pos_ae [CompleteSpace H] (i : Fin N)
    (u : ElectronicH1Space.H1 H (Fin N × Fin 3))
    (d : Fin 3 → ElectronicH1Space.L2 H (Fin N × Fin 3))
    (hu : ∀ᵐ z ∂volume, ElectronicH1Space.value u z ≠ 0) :
    ∀ᵐ x ∂volume, 0 < PhysicalPairSpace.densityL1
      (PhysicalSourcePair.ofWaveFunction i u d) x := by
  have hρ := PhysicalPairRealization.density_ofSource_ae N
    (particleMap i (ElectronicH1Space.value u)) (fun a => particleMap i (d a))
    (Lp.memLp _) (particleSource_memLp_six i u) (fun _ => Lp.memLp _)
  have hN : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  filter_upwards [hρ, particleMap_ne_zero_ae i (ElectronicH1Space.value u) hu]
    with x hx hn
  change 0 < PhysicalPairSpace.densityL1
    (PhysicalPairRealization.ofSource N (particleMap i (ElectronicH1Space.value u))
      (fun a => particleMap i (d a)) (Lp.memLp _) (particleSource_memLp_six i u)
      (fun _ => Lp.memLp _)) x
  rw [hx]
  exact mul_pos hN (sq_pos_of_pos (norm_pos_iff.mpr hn))

end PfHk.NonvanishingDensity
