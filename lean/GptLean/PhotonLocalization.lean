import GptLean.RemovalEstimates
import GptLean.PhotonLossClosure
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Photon localization errors derived from the creation and annihilation
identities, Fock dilation, vacuum orthogonality, and finite-rank radiation
forms. These are the estimates used in Steps 3 and 4 of
`thm-continuum-compactness` in `qedft.tex`.

The inputs below are vector identities and standard operator facts. None
assumes the combined energy estimate or tested-current estimate proved
here. Sobolev cutoff convergence and the realization of the displayed
operators on concrete Fock space remain separate inputs.
-/

namespace GptLean.PhotonLocalization
open Filter Topology Finset
open scoped InnerProductSpace

section Field
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The annihilation bound and CCR give a field bound with no number
operator. `q` is the negative Sobolev norm, `g` the one-photon norm, `r`
the radiation form norm, and `s` the state norm. -/
theorem field_norm_le (ann cre : V) {q g r s : ℝ}
    (hq : 0 ≤ q) (hg : 0 ≤ g) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hann : ‖ann‖ ≤ q * r)
    (hccr : ‖cre‖ ^ 2 = ‖ann‖ ^ 2 + g ^ 2 * s ^ 2) :
    ‖ann + cre‖ ≤ 2 * q * r + g * s := by
  have hann2 : ‖ann‖ ^ 2 ≤ (q * r) ^ 2 := by
    nlinarith [norm_nonneg ann]
  have hcre : ‖cre‖ ≤ q * r + g * s := by
    apply le_of_sq_le_sq _ (by positivity)
    calc ‖cre‖ ^ 2 = ‖ann‖ ^ 2 + g ^ 2 * s ^ 2 := hccr
      _ ≤ (q * r) ^ 2 + g ^ 2 * s ^ 2 := add_le_add hann2 le_rfl
      _ ≤ (q * r + g * s) ^ 2 := by
        nlinarith only [mul_nonneg (mul_nonneg hq hr) (mul_nonneg hg hs)]
  exact (norm_add_le ann cre).trans (by linarith)

/-- One cutoff error controls both norms of the form factor. -/
theorem field_norm_le_cutoff (ann cre : V) {q g r s ε : ℝ}
    (hq : 0 ≤ q) (hg : 0 ≤ g) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hqε : q ≤ ε) (hgε : g ≤ ε)
    (hann : ‖ann‖ ≤ q * r)
    (hccr : ‖cre‖ ^ 2 = ‖ann‖ ^ 2 + g ^ 2 * s ^ 2) :
    ‖ann + cre‖ ≤ ε * (2 * r + s) := by
  apply (field_norm_le ann cre hq hg hr hs hann hccr).trans
  nlinarith [mul_le_mul_of_nonneg_right hqε hr,
    mul_le_mul_of_nonneg_right hgε hs]

/-- Vacuum orthogonality removes the mixed term and retains the vacuum
fluctuation in the localized quadratic field identity. -/
theorem vacuum_norm_sq (u v : V) (horth : ⟪u, v⟫_ℂ = 0) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  simp [norm_add_sq (𝕜 := ℂ), horth]

/-- Fock intertwining plus vacuum orthogonality determines the localized
covariant kinetic form. The sign is absorbed into `h`. -/
theorem localized_covariant_square {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (U : V →ₗᵢ[ℂ] W)
    (d h : V) (v localized : W) (e fluct mass : ℝ)
    (hintertwine : localized = U (d + (e : ℂ) • h) + v)
    (horth : ⟪U (d + (e : ℂ) • h), v⟫_ℂ = 0)
    (hvariance : ‖v‖ ^ 2 = e ^ 2 * fluct ^ 2 * mass) :
    ‖localized‖ ^ 2 = ‖d + (e : ℂ) • h‖ ^ 2 +
      e ^ 2 * fluct ^ 2 * mass := by
  rw [hintertwine, vacuum_norm_sq _ _ horth, U.norm_map, hvariance]

/-- The same vacuum compression identifies the linear field pairing. -/
theorem vacuum_pairing {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (U : V →ₗᵢ[ℂ] W)
    (ψ h : V) (v : W) (horth : ⟪U ψ, v⟫_ℂ = 0) :
    ⟪U ψ, U h + v⟫_ℂ = ⟪ψ, h⟫_ℂ := by
  rw [inner_add_right, horth, add_zero, U.inner_map_map]

/-- Squared-norm perturbation with coefficient one on the original form. -/
theorem norm_add_sq_le (d h : V) :
    ‖d + h‖ ^ 2 ≤ ‖d‖ ^ 2 + 2 * ‖d‖ * ‖h‖ + ‖h‖ ^ 2 := by
  have hn := norm_add_le d h
  nlinarith [norm_nonneg (d + h), norm_nonneg d, norm_nonneg h]

/-- One covariant component contributes a linear and a quadratic cutoff
error, including the discarded vacuum fluctuation. -/
theorem covariant_component_bound (d h : V) {e ε B v mass : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hmass : 0 ≤ mass)
    (hh : ‖h‖ ≤ ε * B) (hv : |v| ≤ ε) :
    ‖d + (e : ℂ) • h‖ ^ 2 + e ^ 2 * v ^ 2 * mass ≤
      ‖d‖ ^ 2 + 2 * |e| * ‖d‖ * B * ε +
        (e ^ 2 * B ^ 2 + e ^ 2 * mass) * ε ^ 2 := by
  have hnorm : ‖(e : ℂ) • h‖ ≤ |e| * ε * B := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hh (abs_nonneg e)).trans_eq (by ring)
  have hsq : ‖(e : ℂ) • h‖ ^ 2 ≤ (|e| * ε * B) ^ 2 := by
    nlinarith [norm_nonneg ((e : ℂ) • h)]
  have hcross : 2 * ‖d‖ * ‖(e : ℂ) • h‖ ≤
      2 * ‖d‖ * (|e| * ε * B) :=
    mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hv2 : v ^ 2 ≤ ε ^ 2 := by
    nlinarith [sq_abs v, abs_nonneg v]
  have hnoise := mul_le_mul_of_nonneg_right hv2 (mul_nonneg (sq_nonneg e) hmass)
  have hbase := norm_add_sq_le d ((e : ℂ) • h)
  calc ‖d + (e : ℂ) • h‖ ^ 2 + e ^ 2 * v ^ 2 * mass
      ≤ (‖d‖ ^ 2 + 2 * ‖d‖ * ‖(e : ℂ) • h‖ + ‖(e : ℂ) • h‖ ^ 2) +
          e ^ 2 * v ^ 2 * mass := add_le_add hbase le_rfl
    _ ≤ (‖d‖ ^ 2 + 2 * ‖d‖ * (|e| * ε * B) + (|e| * ε * B) ^ 2) +
          ε ^ 2 * (e ^ 2 * mass) := by linarith only [hcross, hsq, hnoise]
    _ = _ := by
      simp only [mul_pow, sq_abs]
      ring

/-- Sum over all electron and Cartesian components. The unchanged Coulomb
term can be added to both sides. -/
theorem kinetic_localization_bound {ι : Type*} [Fintype ι]
    (d h : ι → V) (v : ι → ℝ) {e ε B mass : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hmass : 0 ≤ mass)
    (hh : ∀ i, ‖h i‖ ≤ ε * B) (hv : ∀ i, |v i| ≤ ε) :
    (1 / 2 : ℝ) * ∑ i, (‖d i + (e : ℂ) • h i‖ ^ 2 +
        e ^ 2 * v i ^ 2 * mass) ≤
      (1 / 2 : ℝ) * ∑ i, ‖d i‖ ^ 2 +
      (|e| * B * ∑ i, ‖d i‖) * ε +
      ((Fintype.card ι : ℝ) / 2 * (e ^ 2 * B ^ 2 + e ^ 2 * mass)) * ε ^ 2 := by
  have hsum := sum_le_sum (s := (univ : Finset ι)) fun i _ =>
    covariant_component_bound (d i) (h i) (e := e) hε hB hmass (hh i) (hv i)
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] at hsum
  simp only [← mul_sum, ← sum_mul] at hsum
  simp only [sum_add_distrib, ← mul_sum, ← sum_mul]
  nlinarith only [hsum]

/-- Cauchy–Schwarz gives the tested-current error. This also applies in the
Hilbert–Schmidt space to a mixed state and its square root. -/
theorem tested_current_bound (ψ Aψ : V) {Jloc J C ε B : ℝ}
    (hid : Jloc - J = (⟪ψ, Aψ⟫_ℂ).re)
    (hA : ‖Aψ‖ ≤ C * ε * B) :
    |Jloc - J| ≤ ‖ψ‖ * C * ε * B := by
  rw [hid]
  exact (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left hA (norm_nonneg ψ)).trans_eq (by ring)))

/-- Sum the actual tested fields. Each `test i` is multiplication by a
component of the compactly supported current test. The small relative
operator bound is derived here from the annihilation bounds and CCR. -/
theorem tested_field_sum_bound {ι : Type*} [Fintype ι]
    (ann cre : ι → V) (test : ι → V →L[ℂ] V) (q g Z : ι → ℝ)
    {e ε r s : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hq : ∀ i, 0 ≤ q i) (hg : ∀ i, 0 ≤ g i) (hZ : ∀ i, 0 ≤ Z i)
    (hqε : ∀ i, q i ≤ ε) (hgε : ∀ i, g i ≤ ε)
    (htest : ∀ i, ‖test i‖ ≤ Z i)
    (hann : ∀ i, ‖ann i‖ ≤ q i * r)
    (hccr : ∀ i, ‖cre i‖ ^ 2 = ‖ann i‖ ^ 2 + g i ^ 2 * s ^ 2) :
    ‖(e : ℂ) • ∑ i, test i (ann i + cre i)‖ ≤
      (|e| * ∑ i, Z i) * ε * (2 * r + s) := by
  have hi : ∀ i, ‖test i (ann i + cre i)‖ ≤ Z i * (ε * (2 * r + s)) := by
    intro i
    apply ((test i).le_opNorm (ann i + cre i)).trans
    exact mul_le_mul (htest i)
      (field_norm_le_cutoff (ann i) (cre i) (hq i) (hg i) hr hs
        (hqε i) (hgε i) (hann i) (hccr i)) (norm_nonneg _) (hZ i)
  have hsum : ‖∑ i, test i (ann i + cre i)‖ ≤
      (∑ i, Z i) * (ε * (2 * r + s)) := by
    apply (norm_sum_le _ _).trans
    simpa only [sum_mul] using sum_le_sum (s := (univ : Finset ι)) fun i _ => hi i
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left hsum (abs_nonneg e)).trans_eq (by ring)

/-- Tested-current localization directly from Fock field data. This closes
the relative bound used by `tested_current_bound` rather than assuming it. -/
theorem tested_current_of_fields {ι : Type*} [Fintype ι]
    (ψ : V) (ann cre : ι → V) (test : ι → V →L[ℂ] V) (q g Z : ι → ℝ)
    {e ε r s Jloc J : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hq : ∀ i, 0 ≤ q i) (hg : ∀ i, 0 ≤ g i) (hZ : ∀ i, 0 ≤ Z i)
    (hqε : ∀ i, q i ≤ ε) (hgε : ∀ i, g i ≤ ε)
    (htest : ∀ i, ‖test i‖ ≤ Z i)
    (hann : ∀ i, ‖ann i‖ ≤ q i * r)
    (hccr : ∀ i, ‖cre i‖ ^ 2 = ‖ann i‖ ^ 2 + g i ^ 2 * s ^ 2)
    (hid : Jloc - J = (⟪ψ, (e : ℂ) • ∑ i, test i (ann i + cre i)⟫_ℂ).re) :
    |Jloc - J| ≤ ‖ψ‖ * (|e| * ∑ i, Z i) * ε * (2 * r + s) := by
  exact tested_current_bound ψ _ hid
    (tested_field_sum_bound ann cre test q g Z hε hr hs hq hg hZ hqε hgε htest hann hccr)

/-- Normalized-state specialization, without a mean-photon-number bound. -/
theorem tested_current_bound_normalized (ψ Aψ : V) {Jloc J C ε B : ℝ}
    (hψ : ‖ψ‖ = 1) (hid : Jloc - J = (⟪ψ, Aψ⟫_ℂ).re)
    (hA : ‖Aψ‖ ≤ C * ε * B) : |Jloc - J| ≤ C * ε * B := by
  simpa [hψ] using tested_current_bound ψ Aψ hid hA
end Field

section Radiation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Rank-one quadratic forms vary continuously in their defining vectors. -/
theorem rank_one_form_difference (u v z : V) :
    |‖⟪u, z⟫_ℂ‖ ^ 2 - ‖⟪v, z⟫_ℂ‖ ^ 2| ≤
      (‖u‖ + ‖v‖) * ‖u - v‖ * ‖z‖ ^ 2 := by
  have hdiff : |‖⟪u, z⟫_ℂ‖ - ‖⟪v, z⟫_ℂ‖| ≤ ‖u - v‖ * ‖z‖ := by
    calc |‖⟪u, z⟫_ℂ‖ - ‖⟪v, z⟫_ℂ‖| ≤ ‖⟪u, z⟫_ℂ - ⟪v, z⟫_ℂ‖ :=
          abs_norm_sub_norm_le _ _
      _ = ‖⟪u - v, z⟫_ℂ‖ := by rw [inner_sub_left]
      _ ≤ _ := norm_inner_le_norm _ _
  have hsum : ‖⟪u, z⟫_ℂ‖ + ‖⟪v, z⟫_ℂ‖ ≤ (‖u‖ + ‖v‖) * ‖z‖ := by
    nlinarith [norm_inner_le_norm (𝕜 := ℂ) u z, norm_inner_le_norm (𝕜 := ℂ) v z]
  calc |‖⟪u, z⟫_ℂ‖ ^ 2 - ‖⟪v, z⟫_ℂ‖ ^ 2| =
      |‖⟪u, z⟫_ℂ‖ - ‖⟪v, z⟫_ℂ‖| *
        (‖⟪u, z⟫_ℂ‖ + ‖⟪v, z⟫_ℂ‖) := by
        rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity)]
        ring
    _ ≤ (‖u - v‖ * ‖z‖) * ((‖u‖ + ‖v‖) * ‖z‖) :=
      mul_le_mul hdiff hsum (by positivity) (by positivity)
    _ = _ := by ring

/-- The sharp finite-rank radiation bound. Bessel's inequality for the
unperturbed orthonormal family is the sole spectral input. -/
theorem finite_rank_radiation_bound {ι : Type*} [Fintype ι]
    (u v : ι → V) (z : V)
    (hbessel : ∑ i, ‖⟪v i, z⟫_ℂ‖ ^ 2 ≤ ‖z‖ ^ 2) :
    ∑ i, ‖⟪u i, z⟫_ℂ‖ ^ 2 ≤
      (1 + ∑ i, (‖u i‖ + ‖v i‖) * ‖u i - v i‖) * ‖z‖ ^ 2 := by
  have hdiff : ∀ i, ‖⟪u i, z⟫_ℂ‖ ^ 2 ≤ ‖⟪v i, z⟫_ℂ‖ ^ 2 +
      (‖u i‖ + ‖v i‖) * ‖u i - v i‖ * ‖z‖ ^ 2 := by
    intro i
    have h := (le_abs_self _).trans (rank_one_form_difference (u i) (v i) z)
    linarith
  have hsum := sum_le_sum (s := (univ : Finset ι)) fun i _ => hdiff i
  rw [sum_add_distrib, ← sum_mul] at hsum
  nlinarith

/-- The spectral Bessel input is discharged by Mathlib for an
orthonormal family. -/
theorem finite_rank_radiation_bound_orthonormal {ι : Type*} [Fintype ι]
    (u v : ι → V) (z : V) (hv : Orthonormal ℂ v) :
    ∑ i, ‖⟪u i, z⟫_ℂ‖ ^ 2 ≤
      (1 + ∑ i, (‖u i‖ + ‖v i‖) * ‖u i - v i‖) * ‖z‖ ^ 2 := by
  apply finite_rank_radiation_bound u v z
  simpa using hv.sum_inner_products_le (s := (univ : Finset ι)) z

/-- The radiation error vanishes for each fixed finite-rank truncation.
No uniformity in the rank is asserted. -/
theorem finite_rank_error_tendsto {ι : Type*} [Fintype ι]
    (u : ℕ → ι → V) (v : ι → V)
    (hu : ∀ i, Tendsto (fun R => u R i) atTop (𝓝 (v i))) :
    Tendsto (fun R => ∑ i, (‖u R i‖ + ‖v i‖) * ‖u R i - v i‖)
      atTop (𝓝 0) := by
  have hterm : ∀ i, Tendsto (fun R =>
      (‖u R i‖ + ‖v i‖) * ‖u R i - v i‖) atTop (𝓝 0) := by
    intro i
    simpa using ((hu i).norm.add_const ‖v i‖).mul
      (((hu i).sub_const (v i)).norm)
  simpa using tendsto_finsetSum univ fun i _ => hterm i
end Radiation

/-- Covariant IMS cancellation at a point. Apply this in the underlying
real Hilbert space with `w = -i Ψ`. The two scalar identities are exactly
`η² + η̃² = 1` and its derivative. Integration and summation over electron
components give the covariant IMS identity with coefficient one. -/
theorem covariant_ims_pair {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (d w : F) (a b da db : ℝ)
    (hpartition : a ^ 2 + b ^ 2 = 1) (hderivative : a * da + b * db = 0) :
    ‖a • d + da • w‖ ^ 2 + ‖b • d + db • w‖ ^ 2 =
      ‖d‖ ^ 2 + (da ^ 2 + db ^ 2) * ‖w‖ ^ 2 := by
  calc ‖a • d + da • w‖ ^ 2 + ‖b • d + db • w‖ ^ 2 =
      (a ^ 2 + b ^ 2) * ‖d‖ ^ 2 + (da ^ 2 + db ^ 2) * ‖w‖ ^ 2 +
        2 * (a * da + b * db) * ⟪d, w⟫_ℝ := by
        simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow,
          sq_abs, real_inner_smul_left, real_inner_smul_right]
        ring
    _ = _ := by
      rw [hpartition, hderivative]
      ring

/-- The complement has nonnegative energy and may be discarded after IMS. -/
theorem ims_cutoff_bound {cut complement original error mass C L : ℝ}
    (hidentity : cut + complement = original + error)
    (hpositive : 0 ≤ complement) (herror : error ≤ C / L ^ 2 * mass) :
    cut ≤ original + C / L ^ 2 * mass := by
  linarith only [hidentity, hpositive, herror]

/-- Combine kinetic perturbation, sharp truncated radiation, and IMS
before any limit. The coefficient of the original energy remains one. -/
theorem combined_energy_bound {Eloc Eel Rloc Rrad E C₁ C₂ ε δ ims cap : ℝ}
    (hδ : 0 ≤ δ) (hR : Rrad ≤ cap)
    (hkin : Eloc ≤ Eel + C₁ * ε + C₂ * ε ^ 2)
    (hrad : Rloc ≤ (1 + δ) * Rrad)
    (hims : Eel + Rrad ≤ E + ims) :
    Eloc + Rloc ≤ E + ims + (C₁ * ε + C₂ * ε ^ 2 + δ * cap) := by
  have := mul_le_mul_of_nonneg_left hR hδ
  nlinarith

/-- The uniform rough internal-energy estimate follows from the two
standard PF form-norm equivalences and the one-photon Sobolev multiplier
bound. Ordinary electronic kinetic energy and Coulomb energy are unchanged
by the photon channel. -/
theorem rough_energy_from_form_equivalence
    {ordinary radiation localizedRadiation energy localizedEnergy mass a b c : ℝ}
    (hordinary : 0 ≤ ordinary) (hmass : 0 ≤ mass) (hb : 0 ≤ b) (hc : 1 ≤ c)
    (hinput : ordinary + radiation + mass ≤ a * (energy + mass))
    (houtput : localizedEnergy ≤ b * (ordinary + localizedRadiation + mass))
    (hrad : localizedRadiation ≤ c * radiation) :
    localizedEnergy ≤ b * c * a * (energy + mass) := by
  have hmid : ordinary + localizedRadiation + mass ≤ c * (ordinary + radiation + mass) := by
    nlinarith only [hrad, mul_nonneg (sub_nonneg.mpr hc) hordinary,
      mul_nonneg (sub_nonneg.mpr hc) hmass]
  calc localizedEnergy ≤ b * (ordinary + localizedRadiation + mass) := houtput
    _ ≤ b * (c * (ordinary + radiation + mass)) := mul_le_mul_of_nonneg_left hmid hb
    _ ≤ b * (c * (a * (energy + mass))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinput (by linarith)) hb
    _ = _ := by ring

/-- The local error vanishes with both truncation indices fixed. -/
theorem combined_error_tendsto (ε δ : ℕ → ℝ) (C₁ C₂ cap : ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun R => C₁ * ε R + C₂ * ε R ^ 2 + δ R * cap)
      atTop (𝓝 0) := by
  simpa using ((hε.const_mul C₁).add ((hε.pow 2).const_mul C₂)).add (hδ.mul_const cap)

/-- The current localization error uses the same cutoff convergence. -/
theorem current_error_tendsto (ε : ℕ → ℝ) (C B : ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun R => C * ε R * B) atTop (𝓝 0) := by
  simpa using (hε.const_mul C).mul_const B

end GptLean.PhotonLocalization
