import PfHk.CompactWeightMultipliers
import PfHk.CarlemanAnnularWeights

/-! Continuity of the actual weighted Carleman integrals under L2
convergence when all vectors stay in a fixed compact annulus. -/

noncomputable section
namespace PfHk.CarlemanWeightedL2

open MeasureTheory Filter Set PfHk.CarlemanSpatialDensity PfHk.CarlemanWeights
open scoped Topology

set_option Elab.async false
set_option maxHeartbeats 100000

variable {I H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev SpatialL2 := Lp H 2 (volume : Measure (PfHk.PolarCalculus.Position I))

theorem weights_nonneg {τ α ρ R : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α)
    (hρ : 0 < ρ) (hR : R < 1) {x : PfHk.PolarCalculus.Position I}
    (hx : x ∈ annulus ρ R) :
    0 ≤ massWeight τ α x ∧ 0 ≤ kineticWeight τ α x ∧
      0 ≤ radiationWeight τ α x ∧ 0 ≤ sourceWeight τ α x := by
  have hp := hρ.trans_le (annulus_norm hx).1
  have hs := (annulus_norm hx).2.trans_lt hR
  have hb := (beta_pos hα (neg_pos.mpr (Real.log_neg hp hs))).le
  unfold massWeight kineticWeight radiationWeight sourceWeight
  exact ⟨mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hτ _)) hb)
      (inv_nonneg.mpr (sq_nonneg _)),
    mul_nonneg (mul_nonneg (Real.exp_pos _).le hτ) hb,
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num) hτ),
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)⟩

def massOperator (τ α : ℝ) {ρ R : ℝ} (hρ : 0 < ρ) (hR : R < 1) :
    SpatialL2 (I := I) (H := H) →L[ℂ] SpatialL2 (I := I) (H := H) :=
  CompactWeightMultipliers.sqrtMultiplier (annulus ρ R) (annulus_compact ρ R)
    (annulus_compact ρ R).measurableSet (massWeight τ α) (weights_continuousOn τ α hρ hR).1

def kineticOperator (τ α : ℝ) {ρ R : ℝ} (hρ : 0 < ρ) (hR : R < 1) :
    SpatialL2 (I := I) (H := H) →L[ℂ] SpatialL2 (I := I) (H := H) :=
  CompactWeightMultipliers.sqrtMultiplier (annulus ρ R) (annulus_compact ρ R)
    (annulus_compact ρ R).measurableSet (kineticWeight τ α) (weights_continuousOn τ α hρ hR).2.1

def radiationOperator (τ α : ℝ) {ρ R : ℝ} (hρ : 0 < ρ) (hR : R < 1) :
    SpatialL2 (I := I) (H := H) →L[ℂ] SpatialL2 (I := I) (H := H) :=
  CompactWeightMultipliers.sqrtMultiplier (annulus ρ R) (annulus_compact ρ R)
    (annulus_compact ρ R).measurableSet (radiationWeight τ α) (weights_continuousOn τ α hρ hR).2.2.1

def sourceOperator (τ α : ℝ) {ρ R : ℝ} (hρ : 0 < ρ) (hR : R < 1) :
    SpatialL2 (I := I) (H := H) →L[ℂ] SpatialL2 (I := I) (H := H) :=
  CompactWeightMultipliers.sqrtMultiplier (annulus ρ R) (annulus_compact ρ R)
    (annulus_compact ρ R).measurableSet (sourceWeight τ α) (weights_continuousOn τ α hρ hR).2.2.2

theorem density_integrable_supported (τ α : ℝ) {ρ R : ℝ} (hρ : 0 < ρ) (hR : R < 1)
    (m r : SpatialL2 (I := I) (H := H)) (D : I → SpatialL2 (I := I) (H := H))
    (hm : ∀ᵐ x ∂volume, x ∉ annulus ρ R → m x = 0)
    (hD : ∀ i, ∀ᵐ x ∂volume, x ∉ annulus ρ R → D i x = 0)
    (hr : ∀ᵐ x ∂volume, x ∉ annulus ρ R → r x = 0) :
    Integrable (density τ α (fun x => ‖m x‖ ^ 2) (fun x => ∑ i, ‖D i x‖ ^ 2)
      (fun x => ‖r x‖ ^ 2)) := by
  apply density_integrable τ α hρ hR _ _ _ (Lp.memLp m).norm.integrable_sq
    (integrable_finsetSum Finset.univ fun i _ => (Lp.memLp (D i)).norm.integrable_sq)
    (Lp.memLp r).norm.integrable_sq
  filter_upwards [hm, Filter.eventually_all.mpr hD, hr] with x hm' hD' hr' hx
  simp only [hm' hx, hD' _ hx, hr' hx, norm_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, and_self]

theorem source_integrable_supported (τ α : ℝ) {ρ R : ℝ} (hρ : 0 < ρ) (hR : R < 1)
    (f : SpatialL2 (I := I) (H := H))
    (hf : ∀ᵐ x ∂volume, x ∉ annulus ρ R → f x = 0) :
    Integrable (source τ α (fun x => ‖f x‖ ^ 2)) :=
  source_integrable τ α hρ hR _ (Lp.memLp f).norm.integrable_sq
    (hf.mono fun x hx hxs => by rw [hx hxs]; simp)

theorem density_eq_norms {τ α ρ R : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α)
    (hρ : 0 < ρ) (hR : R < 1)
    (m r : SpatialL2 (I := I) (H := H)) (D : I → SpatialL2 (I := I) (H := H))
    (hm : ∀ᵐ x ∂volume, x ∉ annulus ρ R → m x = 0)
    (hD : ∀ i, ∀ᵐ x ∂volume, x ∉ annulus ρ R → D i x = 0)
    (hr : ∀ᵐ x ∂volume, x ∉ annulus ρ R → r x = 0) :
    (∫ x, density τ α (fun y => ‖m y‖ ^ 2) (fun y => ∑ i, ‖D i y‖ ^ 2)
      (fun y => ‖r y‖ ^ 2) x) =
    ‖massOperator τ α hρ hR m‖ ^ 2 + (∑ i, ‖kineticOperator τ α hρ hR (D i)‖ ^ 2) +
      ‖radiationOperator τ α hρ hR r‖ ^ 2 := by
  have hcont := weights_continuousOn (I := I) τ α hρ hR
  have hi₀ := annular_mul_integrable ρ R _ (fun x => ‖m x‖ ^ 2) hcont.1
    (Lp.memLp m).norm.integrable_sq (hm.mono fun x hx hxs => by rw [hx hxs]; simp)
  have hi₁ (i : I) := annular_mul_integrable ρ R _ (fun x => ‖D i x‖ ^ 2) hcont.2.1
    (Lp.memLp (D i)).norm.integrable_sq ((hD i).mono fun x hx hxs => by rw [hx hxs]; simp)
  have hiᵣ := annular_mul_integrable ρ R _ (fun x => ‖r x‖ ^ 2) hcont.2.2.1
    (Lp.memLp r).norm.integrable_sq (hr.mono fun x hx hxs => by rw [hx hxs]; simp)
  have he : density τ α (fun y => ‖m y‖ ^ 2) (fun y => ∑ i, ‖D i y‖ ^ 2)
      (fun y => ‖r y‖ ^ 2) = fun x => massWeight τ α x * ‖m x‖ ^ 2 +
      (∑ i, kineticWeight τ α x * ‖D i x‖ ^ 2) + radiationWeight τ α x * ‖r x‖ ^ 2 := by
    funext x
    rw [← Finset.mul_sum]
    unfold density massWeight kineticWeight radiationWeight
    ring
  have his : Integrable (fun x => ∑ i, kineticWeight τ α x * ‖D i x‖ ^ 2) :=
    integrable_finsetSum Finset.univ fun i _ => hi₁ i
  have houter := integral_add (hi₀.add his) hiᵣ
  have hinner := integral_add hi₀ his
  dsimp only [Pi.add_apply] at houter hinner
  rw [he, houter, hinner, integral_finsetSum Finset.univ fun i _ => hi₁ i]
  have h₀ := CompactWeightMultipliers.sqrtMultiplier_norm_sq_supported
    (annulus ρ R) (annulus_compact ρ R) (annulus_compact ρ R).measurableSet
    (massWeight τ α) hcont.1 (fun x hx => (weights_nonneg hτ hα hρ hR hx).1) m hm
  have h₁ (i : I) := CompactWeightMultipliers.sqrtMultiplier_norm_sq_supported
    (annulus ρ R) (annulus_compact ρ R) (annulus_compact ρ R).measurableSet
    (kineticWeight τ α) hcont.2.1 (fun x hx => (weights_nonneg hτ hα hρ hR hx).2.1) (D i) (hD i)
  have hᵣ := CompactWeightMultipliers.sqrtMultiplier_norm_sq_supported
    (annulus ρ R) (annulus_compact ρ R) (annulus_compact ρ R).measurableSet
    (radiationWeight τ α) hcont.2.2.1 (fun x hx => (weights_nonneg hτ hα hρ hR hx).2.2.1) r hr
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) h₀.symm
    (Finset.sum_congr rfl fun i _ => (h₁ i).symm)) hᵣ.symm

theorem source_eq_norm {τ α ρ R : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α)
    (hρ : 0 < ρ) (hR : R < 1) (f : SpatialL2 (I := I) (H := H))
    (hf : ∀ᵐ x ∂volume, x ∉ annulus ρ R → f x = 0) :
    (∫ x, source τ α (fun y => ‖f y‖ ^ 2) x) = ‖sourceOperator τ α hρ hR f‖ ^ 2 :=
  (CompactWeightMultipliers.sqrtMultiplier_norm_sq_supported
    (annulus ρ R) (annulus_compact ρ R) (annulus_compact ρ R).measurableSet
    (sourceWeight τ α) (weights_continuousOn τ α hρ hR).2.2.2
    (fun x hx => (weights_nonneg hτ hα hρ hR hx).2.2.2) f hf).symm

theorem estimate_limit {τ α ρ R : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α)
    (hρ : 0 < ρ) (hR : R < 1) (B : ℝ)
    {m r f : ℕ → SpatialL2 (I := I) (H := H)} {D : ℕ → I → SpatialL2 (I := I) (H := H)}
    {m₀ r₀ f₀ : SpatialL2 (I := I) (H := H)} {D₀ : I → SpatialL2 (I := I) (H := H)}
    (hm : Tendsto m atTop (𝓝 m₀)) (hr : Tendsto r atTop (𝓝 r₀))
    (hf : Tendsto f atTop (𝓝 f₀)) (hD : ∀ i, Tendsto (fun n => D n i) atTop (𝓝 (D₀ i)))
    (hms : ∀ n, ∀ᵐ x ∂volume, x ∉ annulus ρ R → m n x = 0)
    (hrs : ∀ n, ∀ᵐ x ∂volume, x ∉ annulus ρ R → r n x = 0)
    (hfs : ∀ n, ∀ᵐ x ∂volume, x ∉ annulus ρ R → f n x = 0)
    (hDs : ∀ n i, ∀ᵐ x ∂volume, x ∉ annulus ρ R → D n i x = 0)
    (hest : ∀ n, (∫ x, density τ α (fun y => ‖m n y‖ ^ 2)
      (fun y => ∑ i, ‖D n i y‖ ^ 2) (fun y => ‖r n y‖ ^ 2) x) ≤
      B * ∫ x, source τ α (fun y => ‖f n y‖ ^ 2) x) :
    (∫ x, density τ α (fun y => ‖m₀ y‖ ^ 2) (fun y => ∑ i, ‖D₀ i y‖ ^ 2)
      (fun y => ‖r₀ y‖ ^ 2) x) ≤ B * ∫ x, source τ α (fun y => ‖f₀ y‖ ^ 2) x := by
  have hs := (annulus_compact (I := I) ρ R).measurableSet
  rw [density_eq_norms hτ hα hρ hR m₀ r₀ D₀
    (CompactWeightMultipliers.supported_limit _ hs hms hm)
    (fun i => CompactWeightMultipliers.supported_limit _ hs (fun n => hDs n i) (hD i))
    (CompactWeightMultipliers.supported_limit _ hs hrs hr),
    source_eq_norm hτ hα hρ hR f₀ (CompactWeightMultipliers.supported_limit _ hs hfs hf)]
  have hm' := (((massOperator τ α hρ hR).continuous.tendsto m₀).comp hm).norm.pow 2
  have hr' := (((radiationOperator τ α hρ hR).continuous.tendsto r₀).comp hr).norm.pow 2
  have hf' := ((((sourceOperator τ α hρ hR).continuous.tendsto f₀).comp hf).norm.pow 2).const_mul B
  have hD' := tendsto_finsetSum Finset.univ fun i _ =>
    (((kineticOperator τ α hρ hR).continuous.tendsto (D₀ i)).comp (hD i)).norm.pow 2
  apply le_of_tendsto_of_tendsto' ((hm'.add hD').add hr') hf'
  intro n
  exact (density_eq_norms hτ hα hρ hR (m n) (r n) (D n) (hms n) (hDs n) (hrs n)).symm.le.trans
    ((hest n).trans_eq (congrArg (B * ·) (source_eq_norm hτ hα hρ hR (f n) (hfs n))))

end PfHk.CarlemanWeightedL2
