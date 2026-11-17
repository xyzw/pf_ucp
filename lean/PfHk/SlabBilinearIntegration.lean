import PfHk.PolarInnerCalculus

/-! Finite bilinear L2 forms and the elementary conformal scaling algebra. -/

noncomputable section
namespace PfHk.SlabBilinearIntegration

open MeasureTheory PfHk.PolarCalculus
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency.types false

variable {X H K J : Type*} [MeasurableSpace X] {μ : Measure X} [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem form_integrable
    (u v : Lp H 2 μ) (A B : J → Lp H 2 μ) (q p : Lp K 2 μ)
    {uf vf : X → H} {Af Bf : J → X → H} {qf pf : X → K}
    (hu : u =ᵐ[μ] uf) (hv : v =ᵐ[μ] vf)
    (hA : ∀ j, A j =ᵐ[μ] Af j) (hB : ∀ j, B j =ᵐ[μ] Bf j)
    (hq : q =ᵐ[μ] qf) (hp : p =ᵐ[μ] pf) :
    Integrable (fun x => inner ℝ (uf x) (vf x) +
      (∑ j, inner ℝ (Af j x) (Bf j x)) + 2 * inner ℝ (qf x) (pf x)) μ :=
  ((l2_inner_integrable u v hu hv).add
    (integrable_finsetSum _ (fun j _ => l2_inner_integrable (A j) (B j) (hA j) (hB j)))).add
      ((l2_inner_integrable q p hq hp).const_mul 2)

theorem form_eq_integral
    (u v : Lp H 2 μ) (A B : J → Lp H 2 μ) (q p : Lp K 2 μ)
    {uf vf : X → H} {Af Bf : J → X → H} {qf pf : X → K}
    (hu : u =ᵐ[μ] uf) (hv : v =ᵐ[μ] vf)
    (hA : ∀ j, A j =ᵐ[μ] Af j) (hB : ∀ j, B j =ᵐ[μ] Bf j)
    (hq : q =ᵐ[μ] qf) (hp : p =ᵐ[μ] pf) :
    inner ℝ u v + (∑ j, inner ℝ (A j) (B j)) + 2 * inner ℝ q p =
      ∫ x, inner ℝ (uf x) (vf x) + (∑ j, inner ℝ (Af j x) (Bf j x)) +
        2 * inner ℝ (qf x) (pf x) ∂μ := by
  have hrad := l2_inner_integrable u v hu hv
  have hang (j : J) := l2_inner_integrable (A j) (B j) (hA j) (hB j)
  have hsum := integrable_finsetSum Finset.univ (fun j _ => hang j)
  have henergy := (l2_inner_integrable q p hq hp).const_mul (2 : ℝ)
  have hadd := integral_add (hrad.add hsum) henergy
  have hfirst := integral_add hrad hsum
  dsimp only [Pi.add_apply] at hadd hfirst
  rw [hadd, hfirst, integral_finsetSum _ (fun j _ => hang j), integral_const_mul]
  exact congrArg₂ (fun a b : ℝ => a + 2 * b)
    (congrArg₂ (fun a b : ℝ => a + b) (l2_inner_eq_integral u v hu hv)
      (Finset.sum_congr rfl (fun j _ => l2_inner_eq_integral (A j) (B j) (hA j) (hB j))))
    (l2_inner_eq_integral q p hq hp)

theorem conformal_density (a r : ℝ) (u v : H) (A B : J → H) (q p : K) :
    inner ℝ ((-(a*r)) • u) ((-(a*r)) • v) +
      (∑ j, inner ℝ (a • A j) (a • B j)) +
      2 * inner ℝ (a • q) (r^2 • (a • p)) =
      a^2 * (r^2 * inner ℝ u v + (∑ j, inner ℝ (A j) (B j)) +
        r^2 * (2 * inner ℝ q p)) := by
  simp only [real_inner_smul_left, real_inner_smul_right]
  simp_rw [← mul_assoc]
  rw [← Finset.mul_sum]
  ring

theorem separated_density (η d c r : ℝ) (v R : H) (A B : J → H) (q p : K) :
    inner ℝ ((d+c*η) • v) R + (∑ j, inner ℝ (η • A j) (B j)) +
      2 * inner ℝ (η • q) (r • p) =
      (d+c*η) * inner ℝ v R + η * (∑ j, inner ℝ (A j) (B j)) +
        (r*η) * (2 * inner ℝ q p) := by
  simp only [real_inner_smul_left, real_inner_smul_right]
  rw [← Finset.mul_sum]
  ring

end PfHk.SlabBilinearIntegration
