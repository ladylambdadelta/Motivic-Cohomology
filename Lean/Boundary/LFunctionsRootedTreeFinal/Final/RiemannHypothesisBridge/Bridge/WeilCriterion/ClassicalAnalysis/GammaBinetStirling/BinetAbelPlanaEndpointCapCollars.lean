import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteHoleSubdivision

/-!
# Endpoint cap-collar Cauchy balances for finite Abel-Plana

This file owns the left and right endpoint half-collar domains, oriented boundary
identifications, and normalized endpoint cap-collar balance theorems.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Algebraic cancellation for the finite-hole subdivision once the cap/collar
boundary has been identified with the missing deleted-arc contribution. -/
theorem Complex.finiteAbelPlana_log_verticalStrip_add_deleted_sub_verticalStrip_sub_deleted
    (A B : ℂ) :
    A + (B - A) - B = 0 := by
  ring

/-- The left endpoint cap/collar domain: the rectangular cap
`0 ≤ Re z ≤ ρ`, `-T ≤ Im z ≤ T`, with the deleted endpoint disk removed.

This is the local planar domain used in the classical Abel-Plana contour proof
near the endpoint pole at `0`. -/
def Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain
    (T ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ [[(0 : ℝ), ρ]] ∧ z.im ∈ [[-T, T]]} : Set ℂ) \
    Metric.ball (0 : ℂ) ρ

/-- Membership in the left endpoint cap/collar domain is coordinatewise
membership in the endpoint rectangular cap plus avoidance of the deleted
endpoint disk. -/
theorem Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff
    {T ρ : ℝ}
    {z : ℂ} :
    z ∈ Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ ↔
      z.re ∈ [[(0 : ℝ), ρ]] ∧ z.im ∈ [[-T, T]] ∧
        z ∉ Metric.ball (0 : ℂ) ρ := by
  dsimp [Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain]
  constructor
  · intro hz
    exact ⟨hz.1.1, hz.1.2, hz.2⟩
  · intro hz
    exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩

/-- A point in the left endpoint cap rectangle, after deleting the endpoint
disk, avoids every deleted integer disk in the finite Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointCapCollarPoint_not_mem_deletedDisk
    {N m : ℕ}
    {T ρ : ℝ}
    (_hm : m ∈ Finset.range (N + 2))
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    {z : ℂ}
    (hzre : z.re ∈ [[(0 : ℝ), ρ]])
    (_hzim : z.im ∈ [[-T, T]])
    (hzcentral : z ∉ Metric.ball (0 : ℂ) ρ) :
    z ∉ Metric.ball (m : ℂ) ρ := by
  by_cases hmzero : m = 0
  · subst m
    simpa using hzcentral
  · intro hzball
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hmzero
    have hone_le_m : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hm_pos
    have hρ_lt_half : ρ < (1 : ℝ) / 2 := by
      linarith
    have hzIcc : z.re ∈ Set.Icc (0 : ℝ) ρ := by
      simpa [Set.uIcc_of_le hρnonneg] using hzre
    have hzre_le : z.re ≤ ρ := hzIcc.2
    have hdist_lt : ‖z - (m : ℂ)‖ < ρ := by
      simpa [dist_eq_norm, sub_eq_add_neg] using Metric.mem_ball.mp hzball
    have hre_norm :
        |(z - (m : ℂ)).re| ≤ ‖z - (m : ℂ)‖ := by
      simpa [Complex.norm_eq_abs] using Complex.abs_re_le_abs (z - (m : ℂ))
    have hre_le_neg : (z - (m : ℂ)).re ≤ -ρ := by
      simp [sub_re]
      linarith
    have hρ_le_abs : ρ ≤ |(z - (m : ℂ)).re| := by
      have hneg : ρ ≤ -((z - (m : ℂ)).re) := by
        linarith
      exact hneg.trans (neg_le_abs _)
    exact not_lt_of_ge (hρ_le_abs.trans hre_norm) hdist_lt

/-- The closed left endpoint cap rectangle lies in the ambient finite
Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointCapCollarClosedRectangle_subset_closedRectangle
    {N : ℕ}
    {T ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    ({z : ℂ | z.re ∈ [[(0 : ℝ), ρ]] ∧ z.im ∈ [[-T, T]]} : Set ℂ) ⊆
      Complex.finiteAbelPlanaClosedRectangle N T := by
  intro z hz
  have hzIcc : z.re ∈ Set.Icc (0 : ℝ) ρ := by
    simpa [Set.uIcc_of_le hρnonneg] using hz.1
  have hρ_lt_one : ρ < 1 := by
    linarith
  refine Complex.mem_reProdIm.mpr ⟨?_, hz.2⟩
  have hone_le_succ : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  exact ⟨hzIcc.1, hzIcc.2.trans (le_of_lt hρ_lt_one).trans hone_le_succ⟩

/-- The left endpoint cap/collar domain lies in the finite Abel-Plana
punctured rectangle. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_subset_puncturedRectangle
    {N : ℕ}
    (T : ℝ)
    {ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ ⊆
      Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
  intro z hz
  have hzdata :
      z.re ∈ [[(0 : ℝ), ρ]] ∧ z.im ∈ [[-T, T]] ∧
        z ∉ Metric.ball (0 : ℂ) ρ :=
    Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mp hz
  have hclosed :
      z ∈ Complex.finiteAbelPlanaClosedRectangle N T :=
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarClosedRectangle_subset_closedRectangle
      hρnonneg hρquarter ⟨hzdata.1, hzdata.2.1⟩
  have havoid :
      ∀ m ∈ Finset.range (N + 2), z ∉ Metric.ball (m : ℂ) ρ := by
    intro m hm
    exact
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPoint_not_mem_deletedDisk
        hm hρnonneg hρquarter hzdata.1 hzdata.2.1 hzdata.2.2
  exact
    Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mpr
      ⟨hclosed, havoid⟩

/-- Continuity of the Abel-Plana rectangle integrand on the left endpoint
cap/collar domain, transported from the ambient punctured rectangle. -/
theorem Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
    {w : ℂ}
    {N : ℕ}
    {T ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    ContinuousOn
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ) := by
  exact
    hcont.mono
      (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_subset_puncturedRectangle
        T hρnonneg hρquarter)

/-- Holomorphy of the Abel-Plana rectangle integrand on the left endpoint
cap/collar domain, transported from the ambient punctured rectangle. -/
theorem Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
    {w : ℂ}
    {N : ℕ}
    {T ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    DifferentiableOn ℂ
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ) := by
  exact
    hdiff.mono
      (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_subset_puncturedRectangle
        T hρnonneg hρquarter)

/-- A point on the right semicircle around the left endpoint lies in the
left endpoint punctured cap/collar domain.

This is the endpoint-specific geometric fact that replaces the false full-disk
containment statement: only the right semicircle, not the whole disk, belongs
to the left cap. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointSemicirclePoint_mem_capCollar
    {T ρ θ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hθ : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ∈
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hre :
      (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re) =
        ρ * Real.cos θ := by
    simp [Complex.exp_re, mul_re]
  have him :
      (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im) =
        ρ * Real.sin θ := by
    simp [Complex.exp_im, mul_im]
  have hcos_nonneg : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc hθ
  have hre_mem :
      (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re) ∈
        [[(0 : ℝ), ρ]] := by
    rw [hre]
    have hleft : 0 ≤ ρ * Real.cos θ :=
      mul_nonneg hρnonneg hcos_nonneg
    have hright : ρ * Real.cos θ ≤ ρ :=
      mul_le_of_le_one_right hρnonneg (Real.cos_le_one θ)
    simpa [Set.uIcc_of_le hρnonneg] using And.intro hleft hright
  have hsin_abs : |Real.sin θ| ≤ 1 := by
    exact abs_le.mpr (Real.sin_mem_Icc θ)
  have him_abs : |ρ * Real.sin θ| ≤ ρ := by
    calc
      |ρ * Real.sin θ| = ρ * |Real.sin θ| := by
        rw [abs_mul, abs_of_nonneg hρnonneg]
      _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hsin_abs hρnonneg
      _ = ρ := mul_one ρ
  have him_mem :
      (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im) ∈
        [[-T, T]] := by
    rw [him]
    have habsT : |ρ * Real.sin θ| ≤ T :=
      him_abs.trans (le_of_lt hρT)
    have hb := abs_le.mp habsT
    simpa [Set.uIcc_of_le (neg_le_self hT.le)] using hb
  have hnot_ball :
      ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ∉
        Metric.ball (0 : ℂ) ρ := by
    have hz_eq :
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
          circleMap (0 : ℂ) ρ θ := by
      dsimp [circleMap]
      rw [zero_add, mul_comm (Complex.I) (θ : ℂ)]
    rw [hz_eq]
    exact circleMap_not_mem_ball (0 : ℂ) ρ θ
  exact
    Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hre_mem, him_mem, hnot_ball⟩

/-- Points on the left principal-value vertical side belong to the left
endpoint punctured cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointPVVerticalPoint_mem_capCollar
    {T ρ y : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hy : y ∈ [[-T, -ρ]] ∨ y ∈ [[ρ, T]]) :
    (Complex.I * (y : ℂ)) ∈
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hre_mem :
      (Complex.I * (y : ℂ)).re ∈ [[(0 : ℝ), ρ]] := by
    have hre : (Complex.I * (y : ℂ)).re = 0 := by simp
    rw [hre]
    simpa [Set.uIcc_of_le hρnonneg] using And.intro le_rfl hρnonneg
  have him_mem :
      (Complex.I * (y : ℂ)).im ∈ [[-T, T]] := by
    rcases hy with hy | hy
    · have horder : -T ≤ -ρ := hy.1
      have hyIcc : y ∈ Set.Icc (-T) (-ρ) := by
        simpa [Set.uIcc_of_le horder] using hy
      have hleT : y ≤ T := hyIcc.2.trans (by linarith [hρ])
      simpa using (And.intro hyIcc.1 hleT)
    · have horder : ρ ≤ T := hy.1
      have hyIcc : y ∈ Set.Icc ρ T := by
        simpa [Set.uIcc_of_le horder] using hy
      have hge_negT : -T ≤ y := by linarith [hT, hρ, hyIcc.1]
      simpa using (And.intro hge_negT hyIcc.2)
  have hnot_ball :
      (Complex.I * (y : ℂ)) ∉ Metric.ball (0 : ℂ) ρ := by
    intro hball
    have hdist : ‖Complex.I * (y : ℂ)‖ < ρ := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hball
    have hρ_le_abs_y : ρ ≤ |y| := by
      rcases hy with hy | hy
      · have horder : -T ≤ -ρ := hy.1
        have hyIcc : y ∈ Set.Icc (-T) (-ρ) := by
          simpa [Set.uIcc_of_le horder] using hy
        have hneg : ρ ≤ -y := by linarith
        exact hneg.trans (neg_le_abs y)
      · have horder : ρ ≤ T := hy.1
        have hyIcc : y ∈ Set.Icc ρ T := by
          simpa [Set.uIcc_of_le horder] using hy
        exact hyIcc.1.trans (le_abs_self y)
    have hnorm : ‖Complex.I * (y : ℂ)‖ = |y| := by
      rw [norm_mul, Complex.normSq_eq_norm_sq]
      simp
    rw [hnorm] at hdist
    exact not_lt_of_ge hρ_le_abs_y hdist
  exact
    Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hre_mem, him_mem, hnot_ball⟩

/-- Points on the safe vertical side `Re z = ρ` belong to the left endpoint
punctured cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointSafeVerticalPoint_mem_capCollar
    {T ρ y : ℝ}
    (hρ : 0 < ρ)
    (hy : y ∈ [[-T, T]]) :
    ((ρ : ℂ) + Complex.I * (y : ℂ)) ∈
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hre_mem :
      (((ρ : ℂ) + Complex.I * (y : ℂ)).re) ∈ [[(0 : ℝ), ρ]] := by
    have hre : ((ρ : ℂ) + Complex.I * (y : ℂ)).re = ρ := by simp
    rw [hre]
    simpa [Set.uIcc_of_le hρnonneg] using And.intro hρnonneg le_rfl
  have him_mem :
      (((ρ : ℂ) + Complex.I * (y : ℂ)).im) ∈ [[-T, T]] := by
    simpa using hy
  have hnot_ball :
      ((ρ : ℂ) + Complex.I * (y : ℂ)) ∉ Metric.ball (0 : ℂ) ρ := by
    intro hball
    have hdist : ‖((ρ : ℂ) + Complex.I * (y : ℂ))‖ < ρ := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hball
    have hre_norm :
        |(((ρ : ℂ) + Complex.I * (y : ℂ))).re| ≤
          ‖((ρ : ℂ) + Complex.I * (y : ℂ))‖ := by
      simpa [Complex.norm_eq_abs] using
        Complex.abs_re_le_abs ((ρ : ℂ) + Complex.I * (y : ℂ))
    have hρ_le_norm : ρ ≤ ‖((ρ : ℂ) + Complex.I * (y : ℂ))‖ := by
      have hre_abs : |(((ρ : ℂ) + Complex.I * (y : ℂ))).re| = ρ := by
        simp [abs_of_nonneg hρnonneg]
      simpa [hre_abs] using hre_norm
    exact not_lt_of_ge hρ_le_norm hdist
  exact
    Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hre_mem, him_mem, hnot_ball⟩

/-- The lower left endpoint rectangle
`0 ≤ Re z ≤ ρ`, `-T ≤ Im z ≤ -ρ` lies in the left endpoint punctured
cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointLowerRectangle_subset_capCollar
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ([[((0 : ℂ).re), ((ρ : ℂ) - Complex.I * (ρ : ℂ)).re]] ×ℂ
        [[(-T), (-ρ)]]) ⊆
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
  intro z hz
  have hzre : z.re ∈ [[(0 : ℝ), ρ]] := by
    simpa using (Complex.mem_reProdIm.mp hz).1
  have hzim_lower : z.im ∈ [[-T, -ρ]] := by
    simpa using (Complex.mem_reProdIm.mp hz).2
  have horder : -T ≤ -ρ := by linarith
  have hzimIcc : z.im ∈ Set.Icc (-T) (-ρ) := by
    simpa [Set.uIcc_of_le horder] using hzim_lower
  have hzim : z.im ∈ [[-T, T]] := by
    have hleT : z.im ≤ T := hzimIcc.2.trans (by linarith [hρ])
    simpa using And.intro hzimIcc.1 hleT
  have hnot_ball : z ∉ Metric.ball (0 : ℂ) ρ := by
    intro hball
    have hdist : ‖z‖ < ρ := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hball
    have him_norm : |z.im| ≤ ‖z‖ := by
      simpa [Complex.norm_eq_abs] using Complex.abs_im_le_abs z
    have hρ_le_abs_im : ρ ≤ |z.im| := by
      have hneg : ρ ≤ -z.im := by linarith
      exact hneg.trans (neg_le_abs z.im)
    exact not_lt_of_ge (hρ_le_abs_im.trans him_norm) hdist
  exact
    Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hzre, hzim, hnot_ball⟩

/-- The upper left endpoint rectangle
`0 ≤ Re z ≤ ρ`, `ρ ≤ Im z ≤ T` lies in the left endpoint punctured
cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointUpperRectangle_subset_capCollar
    {T ρ : ℝ}
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ([[((0 : ℂ).re), ((ρ : ℂ) + Complex.I * (ρ : ℂ)).re]] ×ℂ
        [[ρ, T]]) ⊆
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
  intro z hz
  have hzre : z.re ∈ [[(0 : ℝ), ρ]] := by
    simpa using (Complex.mem_reProdIm.mp hz).1
  have hzim_upper : z.im ∈ [[ρ, T]] := by
    simpa using (Complex.mem_reProdIm.mp hz).2
  have horder : ρ ≤ T := le_of_lt hρT
  have hzimIcc : z.im ∈ Set.Icc ρ T := by
    simpa [Set.uIcc_of_le horder] using hzim_upper
  have hzim : z.im ∈ [[-T, T]] := by
    have hge_negT : -T ≤ z.im := by linarith [hρ, hzimIcc.1]
    simpa using And.intro hge_negT hzimIcc.2
  have hnot_ball : z ∉ Metric.ball (0 : ℂ) ρ := by
    intro hball
    have hdist : ‖z‖ < ρ := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hball
    have him_norm : |z.im| ≤ ‖z‖ := by
      simpa [Complex.norm_eq_abs] using Complex.abs_im_le_abs z
    have hρ_le_abs_im : ρ ≤ |z.im| :=
      hzimIcc.1.trans (le_abs_self z.im)
    exact not_lt_of_ge (hρ_le_abs_im.trans him_norm) hdist
  exact
    Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hzre, hzim, hnot_ball⟩

/-- Cauchy-Goursat on the lower ordinary rectangle in the left endpoint cap.

This is the lower rectangular piece of the classical endpoint indentation
argument.  The remaining endpoint cap theorem is obtained by adding this to
the corresponding upper rectangle and the circular cap deformation. -/
theorem Complex.leftEndpointLowerRectangleBoundaryIntegral_eq_zero
    (f : ℂ → ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ)) :
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (T : ℂ))) -
        (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
          Complex.I *
            (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (-T)..(-ρ), f (Complex.I * (y : ℂ))) =
      0 := by
  let z₀ : ℂ := -Complex.I * (T : ℂ)
  let z₁ : ℂ := (ρ : ℂ) - Complex.I * (ρ : ℂ)
  have hclosed :
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
        Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
    dsimp [z₀, z₁]
    exact
      Complex.finiteAbelPlanaLogLeftEndpointLowerRectangle_subset_capCollar
        hT hρ hρT
  have hopen :
      (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
        Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
    intro z hz
    have hclosed_rect :
        z ∈ ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) := by
      have hzdata := Complex.mem_reProdIm.mp hz
      exact
        Complex.mem_reProdIm.mpr
          ⟨Set.Ioo_subset_Icc_self hzdata.1,
            Set.Ioo_subset_Icc_self hzdata.2⟩
    exact hclosed hclosed_rect
  have hcontinuous_closed :
      ContinuousOn f ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) :=
    hcont.mono hclosed
  have hdifferentiable_open :
      DifferentiableOn ℂ f
        (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) :=
    hdiff.mono hopen
  have hcauchy :
      (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
          (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) =
        0 :=
    Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      f z₀ z₁ hcontinuous_closed hdifferentiable_open
  simpa [z₀, z₁, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]
    using hcauchy

/-- Cauchy-Goursat on the upper ordinary rectangle in the left endpoint cap. -/
theorem Complex.leftEndpointUpperRectangleBoundaryIntegral_eq_zero
    (f : ℂ → ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ)) :
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
        (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (T : ℂ))) +
          Complex.I *
            (∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
            Complex.I *
              (∫ y : ℝ in ρ..T, f (Complex.I * (y : ℂ))) =
      0 := by
  let z₀ : ℂ := Complex.I * (ρ : ℂ)
  let z₁ : ℂ := (ρ : ℂ) + Complex.I * (T : ℂ)
  have hclosed :
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
        Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
    dsimp [z₀, z₁]
    exact
      Complex.finiteAbelPlanaLogLeftEndpointUpperRectangle_subset_capCollar
        hρ hρT
  have hopen :
      (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
        Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
    intro z hz
    have hclosed_rect :
        z ∈ ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) := by
      have hzdata := Complex.mem_reProdIm.mp hz
      exact
        Complex.mem_reProdIm.mpr
          ⟨Set.Ioo_subset_Icc_self hzdata.1,
            Set.Ioo_subset_Icc_self hzdata.2⟩
    exact hclosed hclosed_rect
  have hcontinuous_closed :
      ContinuousOn f ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) :=
    hcont.mono hclosed
  have hdifferentiable_open :
      DifferentiableOn ℂ f
        (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) :=
    hdiff.mono hopen
  have hcauchy :
      (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
          (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) =
        0 :=
    Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      f z₀ z₁ hcontinuous_closed hdifferentiable_open
  simpa [z₀, z₁, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]
    using hcauchy

/-- The local Cauchy-Goursat deformation across the left endpoint
half-rectangle collar outside the deleted disk.

This is the precise topological core of the left endpoint principal-value
indentation.  The two horizontal chord integrals at heights `±ρ`, the middle
safe vertical segment, and the counterclockwise right semicircle bound the
right half-rectangle with the endpoint disk removed.  Since `f` is
holomorphic on the punctured endpoint cap, the oriented boundary integral of
this collar vanishes. -/
theorem Complex.leftEndpointHalfRectangleDeletedDiskBoundary_eq_zero
    (f : ℂ → ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ)) :
    -(∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
        (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ))) +
          Complex.I * (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      0 := by
  have hcont_model :
      ContinuousOn f (Complex.rightHalfRectangleDeletedDiskDomain (0 : ℂ) T ρ ρ) := by
    simpa [Complex.rightHalfRectangleDeletedDiskDomain,
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain]
      using hcont
  have hdiff_model :
      DifferentiableOn ℂ f (Complex.rightHalfRectangleDeletedDiskDomain (0 : ℂ) T ρ ρ) := by
    simpa [Complex.rightHalfRectangleDeletedDiskDomain,
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain]
      using hdiff
  have hmodel :
      -(∫ x : ℝ in (0 : ℝ)..((0 : ℂ).re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * (((0 : ℂ).im - ρ : ℝ) : ℂ))) +
          (∫ x : ℝ in (0 : ℝ)..((0 : ℂ).re + ρ),
            f (((x : ℝ) : ℂ) + Complex.I * (((0 : ℂ).im + ρ : ℝ) : ℂ))) +
            Complex.I *
              (∫ y : ℝ in ((0 : ℂ).im - ρ)..((0 : ℂ).im + ρ),
                f ((((0 : ℂ).re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
          ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
            f ((0 : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        0 :=
    Complex.rightHalfRectangleDeletedDiskBoundary_eq_zero
      f (0 : ℂ) T ρ le_rfl hρ (by simpa [abs_of_pos hT] using hρT)
      hcont_model hdiff_model
  simpa using hmodel

/-- The full safe vertical side in the left endpoint cap is the concatenation
of its lower, middle, and upper pieces. -/
theorem Complex.leftEndpointSafeVerticalIntegral_split_three
    (f : ℂ → ℂ)
    (T ρ : ℝ)
    (hlower :
      IntervalIntegrable
        (fun y : ℝ => f ((ρ : ℂ) + Complex.I * (y : ℂ)))
        volume (-T) (-ρ))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ => f ((ρ : ℂ) + Complex.I * (y : ℂ)))
        volume (-ρ) ρ)
    (hupper :
      IntervalIntegrable
        (fun y : ℝ => f ((ρ : ℂ) + Complex.I * (y : ℂ)))
        volume ρ T) :
    ∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) =
      (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
        (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) := by
  have hleft :
      (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          ∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ)) =
        ∫ y : ℝ in (-T)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ)) :=
    intervalIntegral.integral_add_adjacent_intervals hlower hmiddle
  have hleft_integrable :
      IntervalIntegrable
        (fun y : ℝ => f ((ρ : ℂ) + Complex.I * (y : ℂ)))
        volume (-T) ρ :=
    hlower.trans hmiddle
  have hright :
      (∫ y : ℝ in (-T)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) =
        ∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) :=
    intervalIntegral.integral_add_adjacent_intervals hleft_integrable hupper
  calc
    ∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) =
        (∫ y : ℝ in (-T)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) := hright.symm
    _ =
        ((∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
            ∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) := by
      rw [hleft]
    _ =
        (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
            ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) := by
      ring

/-- Complex-linear algebra assembling the two rectangular endpoint identities
and the deleted-disk collar identity into the full left endpoint cap/collar boundary
identity. -/
theorem Complex.leftEndpointCapCollarBoundary_algebra
    (lowerT upperT lowerChord upperChord safe safeLower safeMiddle safeUpper
      pvLower pvUpper arc : ℂ)
    (hsafe : safe = safeLower + safeMiddle + safeUpper)
    (hlower :
      lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower = 0)
    (hupper :
      upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper = 0)
    (hhalf :
      -lowerChord + upperChord + Complex.I * safeMiddle - arc = 0) :
    lowerT - upperT + Complex.I * safe -
        Complex.I * (pvLower + pvUpper) - arc =
      0 := by
  have hsum :
      (lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower) +
          (upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper) +
            (-lowerChord + upperChord + Complex.I * safeMiddle - arc) =
        0 := by
    rw [hlower, hupper, hhalf]
    ring
  calc
    lowerT - upperT + Complex.I * safe -
        Complex.I * (pvLower + pvUpper) - arc =
        (lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower) +
          (upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper) +
            (-lowerChord + upperChord + Complex.I * safeMiddle - arc) := by
      rw [hsafe]
      ring
    _ = 0 := hsum

/-- Generic oriented boundary integral of a left endpoint cap/collar.

This is the local topological object behind the Abel-Plana endpoint at `0`.
The Abel-Plana rectangle integrand is only a later specialization of this
ordinary deleted-disk collar Cauchy-Goursat boundary. -/
noncomputable def Complex.leftEndpointCapCollarOrientedBoundaryIntegral
    (f : ℂ → ℂ)
    (T ρ : ℝ) : ℂ :=
  (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (T : ℂ))) -
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (T : ℂ))) +
        Complex.I * (∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
          Complex.I *
            ((∫ y : ℝ in (-T)..(-ρ), f (Complex.I * (y : ℂ))) +
              ∫ y : ℝ in ρ..T, f (Complex.I * (y : ℂ))) -
    ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
      f ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Generic Cauchy-Goursat theorem for the left endpoint cap/collar.

This is the classical local deleted-disk collar contour theorem: if `f` is
continuous and holomorphic on the rectangular cap with the endpoint disk
deleted, the oriented boundary integral of that cap is zero. -/
theorem Complex.leftEndpointCapCollarOrientedBoundaryIntegral_eq_zero
    (f : ℂ → ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ)) :
    Complex.leftEndpointCapCollarOrientedBoundaryIntegral f T ρ = 0 := by
  let g : ℝ → ℂ := fun y : ℝ => f ((ρ : ℂ) + Complex.I * (y : ℂ))
  have hsafe_integrable :
      ∀ a b : ℝ,
        (∀ y ∈ [[a, b]], y ∈ [[-T, T]]) →
          IntervalIntegrable g volume a b := by
    intro a b hinterval_subset
    have hpath_cont :
        ContinuousOn
          (fun y : ℝ => ((ρ : ℂ) + Complex.I * (y : ℂ)))
          [[a, b]] := by
      exact (continuous_const.add (continuous_const.mul continuous_ofReal)).continuousOn
    have hpath_mem :
        ∀ y ∈ [[a, b]],
          ((ρ : ℂ) + Complex.I * (y : ℂ)) ∈
            Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
      intro y hy
      exact
        Complex.finiteAbelPlanaLogLeftEndpointSafeVerticalPoint_mem_capCollar
          hρ (hinterval_subset y hy)
    have hg_cont :
        ContinuousOn g [[a, b]] :=
      hcont.comp_continuousOn hpath_cont hpath_mem
    exact hg_cont.intervalIntegrable
  have hlower_interval :
      ∀ y ∈ [[(-T), (-ρ)]], y ∈ [[-T, T]] := by
    intro y hy
    have horder : -T ≤ -ρ := by linarith
    have hyIcc : y ∈ Set.Icc (-T) (-ρ) := by
      simpa [Set.uIcc_of_le horder] using hy
    have hy_le_T : y ≤ T := by linarith [hyIcc.2, hρ]
    simpa using And.intro hyIcc.1 hy_le_T
  have hmiddle_interval :
      ∀ y ∈ [[(-ρ), ρ]], y ∈ [[-T, T]] := by
    intro y hy
    have horder : -ρ ≤ ρ := by linarith
    have hyIcc : y ∈ Set.Icc (-ρ) ρ := by
      simpa [Set.uIcc_of_le horder] using hy
    have hy_ge_negT : -T ≤ y := by linarith [hρT, hyIcc.1]
    have hy_le_T : y ≤ T := by linarith [hρT, hyIcc.2]
    simpa using And.intro hy_ge_negT hy_le_T
  have hupper_interval :
      ∀ y ∈ [[ρ, T]], y ∈ [[-T, T]] := by
    intro y hy
    have horder : ρ ≤ T := le_of_lt hρT
    have hyIcc : y ∈ Set.Icc ρ T := by
      simpa [Set.uIcc_of_le horder] using hy
    have hy_ge_negT : -T ≤ y := by linarith [hT, hρ, hyIcc.1]
    simpa using And.intro hy_ge_negT hyIcc.2
  have hsafe_split :
      ∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) =
        (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
            ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) := by
    exact
      Complex.leftEndpointSafeVerticalIntegral_split_three
        f T ρ
        (hsafe_integrable (-T) (-ρ) hlower_interval)
        (hsafe_integrable (-ρ) ρ hmiddle_interval)
        (hsafe_integrable ρ T hupper_interval)
  have hlower_zero :
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (T : ℂ))) -
          (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
            Complex.I *
              (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
              Complex.I *
                (∫ y : ℝ in (-T)..(-ρ), f (Complex.I * (y : ℂ))) =
        0 :=
    Complex.leftEndpointLowerRectangleBoundaryIntegral_eq_zero
      f T hT hρ hρT hcont hdiff
  have hupper_zero :
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
          (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (T : ℂ))) +
            Complex.I *
              (∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
              Complex.I *
                (∫ y : ℝ in ρ..T, f (Complex.I * (y : ℂ))) =
        0 :=
    Complex.leftEndpointUpperRectangleBoundaryIntegral_eq_zero
      f T hρ hρT hcont hdiff
  have hhalf_zero :
      -(∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
          (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ))) +
            Complex.I * (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
          ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
            f ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        0 :=
    Complex.leftEndpointHalfRectangleDeletedDiskBoundary_eq_zero
      f T hT hρ hρT hcont hdiff
  dsimp [Complex.leftEndpointCapCollarOrientedBoundaryIntegral]
  exact
    Complex.leftEndpointCapCollarBoundary_algebra
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (T : ℂ)))
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (T : ℂ)))
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ)))
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ)))
      (∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in (-T)..(-ρ), f (Complex.I * (y : ℂ)))
      (∫ y : ℝ in ρ..T, f (Complex.I * (y : ℂ)))
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      hsafe_split
      hlower_zero
      hupper_zero
      hhalf_zero

/-- Oriented unnormalized boundary expression of the left endpoint cap/collar.

The five terms are, in order: lower collar, upper collar with opposite
orientation, right safe-strip edge, principal-value left edge with opposite
orientation, and the endpoint semicircle with the punctured-domain orientation
moved to the left-hand side. -/
noncomputable def Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
      Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
        Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ -
    ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
      Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Unfolding of the left endpoint cap/collar oriented boundary into its
straight collar sides and right semicircular deleted-boundary side. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollarOrientedBoundary_unfold
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ =
      Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ -
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  rfl

/-- The Abel-Plana left endpoint oriented boundary is the generic left cap
boundary specialized to the logarithmic cotangent rectangle integrand. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollarOrientedBoundary_eq_generic
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ =
      Complex.leftEndpointCapCollarOrientedBoundaryIntegral
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        T ρ := by
  rfl

/-- Solving the left endpoint oriented-boundary Cauchy equation gives the
left endpoint half-collar balance. -/
theorem Complex.finiteAbelPlana_log_leftEndpointHalfCollar_balance_of_orientedBoundary_zero
    (w : ℂ)
    (T ρ : ℝ)
    (hboundary :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0) :
    Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  dsimp [Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary] at hboundary
  exact sub_eq_zero.mp hboundary

/-- Cauchy-Goursat on the left endpoint cap/collar domain, with the boundary
orientation identified with the existing named side and indentation integrals.

This is the local deleted-disk collar theorem for the endpoint pole at `0`:
the boundary of the right endpoint collar, after deleting the endpoint
semicircle, has zero integral. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero_owner
    {w : ℂ}
    {N : ℕ}
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont_left :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ))
    (hdiff_left :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 := by
  calc
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ =
        Complex.leftEndpointCapCollarOrientedBoundaryIntegral
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          T ρ := by
      exact
        Complex.finiteAbelPlana_log_leftEndpointCapCollarOrientedBoundary_eq_generic
          w T ρ
    _ = 0 := by
      exact
        Complex.leftEndpointCapCollarOrientedBoundaryIntegral_eq_zero
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          T hT hρ (by
            have hρ_abs : ρ < |T| / 2 := hdeleted_geometry.2.1
            have hT_abs : |T| = T := abs_of_pos hT
            rw [hT_abs] at hρ_abs
            linarith)
          hcont_left hdiff_left

/-- The right endpoint cap/collar domain: the rectangular cap
`N + 1 - ρ ≤ Re z ≤ N + 1`, `-T ≤ Im z ≤ T`, with the deleted endpoint
disk removed.

This is the local planar domain used in the classical Abel-Plana contour proof
near the endpoint pole at `N + 1`. -/
def Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain
    (N : ℕ)
    (T ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] ∧
      z.im ∈ [[-T, T]]} : Set ℂ) \
    Metric.ball ((N + 1 : ℕ) : ℂ) ρ

/-- Membership in the right endpoint cap/collar domain is coordinatewise
membership in the endpoint rectangular cap plus avoidance of the deleted
right endpoint disk. -/
theorem Complex.mem_finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_iff
    {N : ℕ}
    {T ρ : ℝ}
    {z : ℂ} :
    z ∈ Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ ↔
      z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] ∧
        z.im ∈ [[-T, T]] ∧
          z ∉ Metric.ball ((N + 1 : ℕ) : ℂ) ρ := by
  dsimp [Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain]
  constructor
  · intro hz
    exact ⟨hz.1.1, hz.1.2, hz.2⟩
  · intro hz
    exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩

/-- A point in the right endpoint cap rectangle, after deleting the endpoint
disk, avoids every deleted integer disk in the finite Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlanaLogRightEndpointCapCollarPoint_not_mem_deletedDisk
    {N m : ℕ}
    {T ρ : ℝ}
    (hm : m ∈ Finset.range (N + 2))
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    {z : ℂ}
    (hzre : z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]])
    (_hzim : z.im ∈ [[-T, T]])
    (hzcentral : z ∉ Metric.ball ((N + 1 : ℕ) : ℂ) ρ) :
    z ∉ Metric.ball (m : ℂ) ρ := by
  by_cases hmcenter : m = N + 1
  · subst m
    simpa using hzcentral
  · intro hzball
    have hm_lt_succ : m < N + 1 := by
      have hm_lt : m < N + 2 := Finset.mem_range.mp hm
      exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hm_lt) hmcenter
    have hm_le_N : m ≤ N := Nat.lt_succ_iff.mp hm_lt_succ
    have hm_real_le_N : ((m : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hm_le_N
    have hρ_lt_half : ρ < (1 : ℝ) / 2 := by
      linarith
    have hleft_le_right :
        ((N + 1 : ℕ) : ℝ) - ρ ≤ ((N + 1 : ℕ) : ℝ) := by
      linarith
    have hzIcc :
        z.re ∈ Set.Icc (((N + 1 : ℕ) : ℝ) - ρ) (((N + 1 : ℕ) : ℝ)) := by
      simpa [Set.uIcc_of_le hleft_le_right] using hzre
    have hzre_ge : ((N + 1 : ℕ) : ℝ) - ρ ≤ z.re := hzIcc.1
    have hdist_lt : ‖z - (m : ℂ)‖ < ρ := by
      simpa [dist_eq_norm, sub_eq_add_neg] using Metric.mem_ball.mp hzball
    have hre_norm :
        |(z - (m : ℂ)).re| ≤ ‖z - (m : ℂ)‖ := by
      simpa [Complex.norm_eq_abs] using Complex.abs_re_le_abs (z - (m : ℂ))
    have hre_ge : ρ ≤ (z - (m : ℂ)).re := by
      simp [sub_re]
      have hsucc_real : (((N + 1 : ℕ) : ℝ) : ℝ) = (N : ℝ) + 1 := by
        norm_num
      linarith
    have hρ_le_abs : ρ ≤ |(z - (m : ℂ)).re| :=
      hre_ge.trans (le_abs_self _)
    exact not_lt_of_ge (hρ_le_abs.trans hre_norm) hdist_lt

/-- The closed right endpoint cap rectangle lies in the ambient finite
Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlanaLogRightEndpointCapCollarClosedRectangle_subset_closedRectangle
    {N : ℕ}
    {T ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    ({z : ℂ | z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] ∧
        z.im ∈ [[-T, T]]} : Set ℂ) ⊆
      Complex.finiteAbelPlanaClosedRectangle N T := by
  intro z hz
  have hleft_le_right :
      ((N + 1 : ℕ) : ℝ) - ρ ≤ ((N + 1 : ℕ) : ℝ) := by
    linarith
  have hzIcc :
      z.re ∈ Set.Icc (((N + 1 : ℕ) : ℝ) - ρ) (((N + 1 : ℕ) : ℝ)) := by
    simpa [Set.uIcc_of_le hleft_le_right] using hz.1
  have hρ_lt_one : ρ < 1 := by
    linarith
  refine Complex.mem_reProdIm.mpr ⟨?_, hz.2⟩
  have hnonneg : 0 ≤ ((N + 1 : ℕ) : ℝ) - ρ := by
    have hone_le_succ : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    linarith
  exact ⟨hnonneg.trans hzIcc.1, hzIcc.2⟩

/-- The right endpoint cap/collar domain lies in the finite Abel-Plana
punctured rectangle. -/
theorem Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_subset_puncturedRectangle
    {N : ℕ}
    (T : ℝ)
    {ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ ⊆
      Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
  intro z hz
  have hzdata :
      z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] ∧
        z.im ∈ [[-T, T]] ∧
          z ∉ Metric.ball ((N + 1 : ℕ) : ℂ) ρ :=
    Complex.mem_finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_iff.mp hz
  have hclosed :
      z ∈ Complex.finiteAbelPlanaClosedRectangle N T :=
    Complex.finiteAbelPlanaLogRightEndpointCapCollarClosedRectangle_subset_closedRectangle
      hρnonneg hρquarter ⟨hzdata.1, hzdata.2.1⟩
  have havoid :
      ∀ m ∈ Finset.range (N + 2), z ∉ Metric.ball (m : ℂ) ρ := by
    intro m hm
    exact
      Complex.finiteAbelPlanaLogRightEndpointCapCollarPoint_not_mem_deletedDisk
        hm hρnonneg hρquarter hzdata.1 hzdata.2.1 hzdata.2.2
  exact
    Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mpr
      ⟨hclosed, havoid⟩

/-- Continuity of the Abel-Plana rectangle integrand on the right endpoint
cap/collar domain, transported from the ambient punctured rectangle. -/
theorem Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_rightEndpointCapCollar
    {w : ℂ}
    {N : ℕ}
    {T ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    ContinuousOn
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ) := by
  exact
    hcont.mono
      (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_subset_puncturedRectangle
        T hρnonneg hρquarter)

/-- Holomorphy of the Abel-Plana rectangle integrand on the right endpoint
cap/collar domain, transported from the ambient punctured rectangle. -/
theorem Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_rightEndpointCapCollar
    {w : ℂ}
    {N : ℕ}
    {T ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    DifferentiableOn ℂ
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ) := by
  exact
    hdiff.mono
      (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_subset_puncturedRectangle
        T hρnonneg hρquarter)

/-- A point on the left semicircle around the right endpoint lies in the
right endpoint punctured cap/collar domain.

This is the reflected endpoint geometry for the cap at `N + 1`: on
`π / 2 ≤ θ ≤ 3π / 2`, the cosine is nonpositive, so the circle lies to the
left of the endpoint. -/
theorem Complex.finiteAbelPlanaLogRightEndpointSemicirclePoint_mem_capCollar
    {N : ℕ}
    {T ρ θ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hθ : θ ∈ Set.Icc (Real.pi / 2) (3 * Real.pi / 2)) :
    (((N + 1 : ℕ) : ℂ) +
        (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ∈
      Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
  let M : ℕ := N + 1
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hre :
      ((((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re)) =
        ((M : ℝ) + ρ * Real.cos θ) := by
    simp [M, Complex.exp_re, mul_re]
  have him :
      ((((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im)) =
        ρ * Real.sin θ := by
    simp [M, Complex.exp_im, mul_im]
  have hcos_nonpos : Real.cos θ ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 hθ.2
  have hcos_ge_neg_one : -1 ≤ Real.cos θ :=
    (Real.cos_mem_Icc θ).1
  have hre_mem :
      (((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re) ∈
        [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] := by
    rw [hre]
    have hleft : (M : ℝ) - ρ ≤ (M : ℝ) + ρ * Real.cos θ := by
      have hmul : -ρ ≤ ρ * Real.cos θ := by
        calc
          -ρ = ρ * (-1) := by ring
          _ ≤ ρ * Real.cos θ :=
            mul_le_mul_of_nonneg_left hcos_ge_neg_one hρnonneg
      linarith
    have hright : (M : ℝ) + ρ * Real.cos θ ≤ (M : ℝ) := by
      have hmul : ρ * Real.cos θ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hρnonneg hcos_nonpos
      linarith
    simpa [M, Set.uIcc_of_le (sub_le_self ((N + 1 : ℕ) : ℝ) hρnonneg)] using
      And.intro hleft hright
  have hsin_abs : |Real.sin θ| ≤ 1 := by
    exact abs_le.mpr (Real.sin_mem_Icc θ)
  have him_abs : |ρ * Real.sin θ| ≤ ρ := by
    calc
      |ρ * Real.sin θ| = ρ * |Real.sin θ| := by
        rw [abs_mul, abs_of_nonneg hρnonneg]
      _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hsin_abs hρnonneg
      _ = ρ := mul_one ρ
  have him_mem :
      (((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im) ∈
        [[-T, T]] := by
    rw [him]
    have habsT : |ρ * Real.sin θ| ≤ T :=
      him_abs.trans (le_of_lt hρT)
    have hb := abs_le.mp habsT
    simpa [Set.uIcc_of_le (neg_le_self hT.le)] using hb
  have hnot_ball :
      (((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) ∉
        Metric.ball ((N + 1 : ℕ) : ℂ) ρ := by
    have hz_eq :
        (((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
          circleMap ((N + 1 : ℕ) : ℂ) ρ θ := by
      dsimp [circleMap, M]
      rw [mul_comm (Complex.I) (θ : ℂ)]
    rw [hz_eq]
    exact circleMap_not_mem_ball ((N + 1 : ℕ) : ℂ) ρ θ
  exact
    Complex.mem_finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hre_mem, him_mem, hnot_ball⟩

/-- Points on the right principal-value vertical side belong to the right
endpoint punctured cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogRightEndpointPVVerticalPoint_mem_capCollar
    {N : ℕ}
    {T ρ y : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hy : y ∈ [[-T, -ρ]] ∨ y ∈ [[ρ, T]]) :
    (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) ∈
      Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
  let M : ℕ := N + 1
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hre_mem :
      (((M : ℂ) + Complex.I * (y : ℂ)).re) ∈
        [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] := by
    have hre : ((M : ℂ) + Complex.I * (y : ℂ)).re = (M : ℝ) := by
      simp [M]
    rw [hre]
    have hleft : ((N + 1 : ℕ) : ℝ) - ρ ≤ ((N + 1 : ℕ) : ℝ) := by
      linarith
    simpa [M, Set.uIcc_of_le hleft] using And.intro hleft le_rfl
  have him_mem :
      (((M : ℂ) + Complex.I * (y : ℂ)).im) ∈ [[-T, T]] := by
    rcases hy with hy | hy
    · have horder : -T ≤ -ρ := hy.1
      have hyIcc : y ∈ Set.Icc (-T) (-ρ) := by
        simpa [Set.uIcc_of_le horder] using hy
      have hleT : y ≤ T := hyIcc.2.trans (by linarith [hρ])
      simpa [M] using (And.intro hyIcc.1 hleT)
    · have horder : ρ ≤ T := hy.1
      have hyIcc : y ∈ Set.Icc ρ T := by
        simpa [Set.uIcc_of_le horder] using hy
      have hge_negT : -T ≤ y := by linarith [hT, hρ, hyIcc.1]
      simpa [M] using (And.intro hge_negT hyIcc.2)
  have hnot_ball :
      (((M : ℂ) + Complex.I * (y : ℂ))) ∉
        Metric.ball ((N + 1 : ℕ) : ℂ) ρ := by
    intro hball
    have hdist : ‖(((M : ℂ) + Complex.I * (y : ℂ)) - ((N + 1 : ℕ) : ℂ))‖ < ρ := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hball
    have hρ_le_abs_y : ρ ≤ |y| := by
      rcases hy with hy | hy
      · have horder : -T ≤ -ρ := hy.1
        have hyIcc : y ∈ Set.Icc (-T) (-ρ) := by
          simpa [Set.uIcc_of_le horder] using hy
        have hneg : ρ ≤ -y := by linarith
        exact hneg.trans (neg_le_abs y)
      · have horder : ρ ≤ T := hy.1
        have hyIcc : y ∈ Set.Icc ρ T := by
          simpa [Set.uIcc_of_le horder] using hy
        exact hyIcc.1.trans (le_abs_self y)
    have hnorm :
        ‖(((M : ℂ) + Complex.I * (y : ℂ)) - ((N + 1 : ℕ) : ℂ))‖ = |y| := by
      dsimp [M]
      ring_nf
      rw [norm_mul]
      simp
    rw [hnorm] at hdist
    exact not_lt_of_ge hρ_le_abs_y hdist
  exact
    Complex.mem_finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hre_mem, him_mem, hnot_ball⟩

/-- Points on the safe vertical side `Re z = N + 1 - ρ` belong to the right
endpoint punctured cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogRightEndpointSafeVerticalPoint_mem_capCollar
    {N : ℕ}
    {T ρ y : ℝ}
    (hρ : 0 < ρ)
    (hy : y ∈ [[-T, T]]) :
    ((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) ∈
      Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hleft_le_right :
      ((N + 1 : ℕ) : ℝ) - ρ ≤ ((N + 1 : ℕ) : ℝ) := by
    linarith
  have hre_mem :
      (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)).re) ∈
        [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] := by
    have hre :
        (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)).re) =
          ((N + 1 : ℕ) : ℝ) - ρ := by
      simp
    rw [hre]
    simpa [Set.uIcc_of_le hleft_le_right] using And.intro le_rfl hleft_le_right
  have him_mem :
      (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)).im) ∈ [[-T, T]] := by
    simpa using hy
  have hnot_ball :
      (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ))) ∉
        Metric.ball ((N + 1 : ℕ) : ℂ) ρ := by
    intro hball
    have hdist :
        ‖(((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
            ((N + 1 : ℕ) : ℂ))‖ < ρ := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hball
    have hre_norm :
        |(((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
            ((N + 1 : ℕ) : ℂ)).re| ≤
          ‖(((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
            ((N + 1 : ℕ) : ℂ))‖ := by
      simpa [Complex.norm_eq_abs] using
        Complex.abs_re_le_abs
          (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
            ((N + 1 : ℕ) : ℂ))
    have hρ_le_norm :
        ρ ≤ ‖(((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
            ((N + 1 : ℕ) : ℂ))‖ := by
      have hre_abs :
          |(((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
              ((N + 1 : ℕ) : ℂ)).re| = ρ := by
        simp [abs_of_nonneg hρnonneg]
      simpa [hre_abs] using hre_norm
    exact not_lt_of_ge hρ_le_norm hdist
  exact
    Complex.mem_finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hre_mem, him_mem, hnot_ball⟩

/-- The lower right endpoint rectangle
`N + 1 - ρ ≤ Re z ≤ N + 1`, `-T ≤ Im z ≤ -ρ` lies in the right endpoint
punctured cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogRightEndpointLowerRectangle_subset_capCollar
    {N : ℕ}
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ([[((((N + 1 : ℕ) : ℝ) - ρ : ℝ) : ℂ).re,
        (((N + 1 : ℕ) : ℂ).re)]] ×ℂ
        [[(-T), (-ρ)]]) ⊆
      Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
  intro z hz
  have hzre :
      z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] := by
    simpa using (Complex.mem_reProdIm.mp hz).1
  have hzim_lower : z.im ∈ [[-T, -ρ]] := by
    simpa using (Complex.mem_reProdIm.mp hz).2
  have horder : -T ≤ -ρ := by linarith
  have hzimIcc : z.im ∈ Set.Icc (-T) (-ρ) := by
    simpa [Set.uIcc_of_le horder] using hzim_lower
  have hzim : z.im ∈ [[-T, T]] := by
    have hleT : z.im ≤ T := hzimIcc.2.trans (by linarith [hρ])
    simpa using And.intro hzimIcc.1 hleT
  have hnot_ball : z ∉ Metric.ball ((N + 1 : ℕ) : ℂ) ρ := by
    intro hball
    have hdist : ‖z - ((N + 1 : ℕ) : ℂ)‖ < ρ := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hball
    have him_norm : |(z - ((N + 1 : ℕ) : ℂ)).im| ≤ ‖z - ((N + 1 : ℕ) : ℂ)‖ := by
      simpa [Complex.norm_eq_abs] using
        Complex.abs_im_le_abs (z - ((N + 1 : ℕ) : ℂ))
    have hρ_le_abs_im : ρ ≤ |(z - ((N + 1 : ℕ) : ℂ)).im| := by
      have hraw : ρ ≤ |z.im| := by
        have hneg : ρ ≤ -z.im := by linarith
        exact hneg.trans (neg_le_abs z.im)
      simpa [sub_im] using hraw
    exact not_lt_of_ge (hρ_le_abs_im.trans him_norm) hdist
  exact
    Complex.mem_finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hzre, hzim, hnot_ball⟩

/-- The upper right endpoint rectangle
`N + 1 - ρ ≤ Re z ≤ N + 1`, `ρ ≤ Im z ≤ T` lies in the right endpoint
punctured cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogRightEndpointUpperRectangle_subset_capCollar
    {N : ℕ}
    {T ρ : ℝ}
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ([[((((N + 1 : ℕ) : ℝ) - ρ : ℝ) : ℂ).re,
        (((N + 1 : ℕ) : ℂ).re)]] ×ℂ
        [[ρ, T]]) ⊆
      Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
  intro z hz
  have hzre :
      z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] := by
    simpa using (Complex.mem_reProdIm.mp hz).1
  have hzim_upper : z.im ∈ [[ρ, T]] := by
    simpa using (Complex.mem_reProdIm.mp hz).2
  have horder : ρ ≤ T := le_of_lt hρT
  have hzimIcc : z.im ∈ Set.Icc ρ T := by
    simpa [Set.uIcc_of_le horder] using hzim_upper
  have hzim : z.im ∈ [[-T, T]] := by
    have hge_negT : -T ≤ z.im := by linarith [hρ, hzimIcc.1]
    simpa using And.intro hge_negT hzimIcc.2
  have hnot_ball : z ∉ Metric.ball ((N + 1 : ℕ) : ℂ) ρ := by
    intro hball
    have hdist : ‖z - ((N + 1 : ℕ) : ℂ)‖ < ρ := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hball
    have him_norm : |(z - ((N + 1 : ℕ) : ℂ)).im| ≤ ‖z - ((N + 1 : ℕ) : ℂ)‖ := by
      simpa [Complex.norm_eq_abs] using
        Complex.abs_im_le_abs (z - ((N + 1 : ℕ) : ℂ))
    have hρ_le_abs_im : ρ ≤ |(z - ((N + 1 : ℕ) : ℂ)).im| := by
      have hraw : ρ ≤ |z.im| :=
        hzimIcc.1.trans (le_abs_self z.im)
      simpa [sub_im] using hraw
    exact not_lt_of_ge (hρ_le_abs_im.trans him_norm) hdist
  exact
    Complex.mem_finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hzre, hzim, hnot_ball⟩

/-- Cauchy-Goursat on the lower ordinary rectangle in the right endpoint cap. -/
theorem Complex.rightEndpointLowerRectangleBoundaryIntegral_eq_zero
    (f : ℂ → ℂ)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ)) :
    (let M : ℕ := N + 1
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (T : ℂ))) -
          (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
            Complex.I *
              (∫ y : ℝ in (-T)..(-ρ), f ((M : ℂ) + Complex.I * (y : ℂ))) -
              Complex.I *
                (∫ y : ℝ in (-T)..(-ρ),
                  f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))) =
      0 := by
  let M : ℕ := N + 1
  let z₀ : ℂ := (((M : ℝ) - ρ : ℝ) : ℂ) - Complex.I * (T : ℂ)
  let z₁ : ℂ := (M : ℂ) - Complex.I * (ρ : ℂ)
  have hclosed :
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
        Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
    dsimp [z₀, z₁, M]
    exact
      Complex.finiteAbelPlanaLogRightEndpointLowerRectangle_subset_capCollar
        hT hρ hρT
  have hopen :
      (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
        Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
    intro z hz
    have hclosed_rect :
        z ∈ ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) := by
      have hzdata := Complex.mem_reProdIm.mp hz
      exact
        Complex.mem_reProdIm.mpr
          ⟨Set.Ioo_subset_Icc_self hzdata.1,
            Set.Ioo_subset_Icc_self hzdata.2⟩
    exact hclosed hclosed_rect
  have hcontinuous_closed :
      ContinuousOn f ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) :=
    hcont.mono hclosed
  have hdifferentiable_open :
      DifferentiableOn ℂ f
        (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) :=
    hdiff.mono hopen
  have hcauchy :
      (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
          (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) =
        0 :=
    Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      f z₀ z₁ hcontinuous_closed hdifferentiable_open
  simpa [z₀, z₁, M, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc,
    sub_eq_add_neg] using hcauchy

/-- Cauchy-Goursat on the upper ordinary rectangle in the right endpoint cap. -/
theorem Complex.rightEndpointUpperRectangleBoundaryIntegral_eq_zero
    (f : ℂ → ℂ)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ)) :
    (let M : ℕ := N + 1
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
          (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (T : ℂ))) +
            Complex.I *
              (∫ y : ℝ in ρ..T, f ((M : ℂ) + Complex.I * (y : ℂ))) -
              Complex.I *
                (∫ y : ℝ in ρ..T,
                  f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))) =
      0 := by
  let M : ℕ := N + 1
  let z₀ : ℂ := (((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (ρ : ℂ)
  let z₁ : ℂ := (M : ℂ) + Complex.I * (T : ℂ)
  have hclosed :
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
        Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
    dsimp [z₀, z₁, M]
    exact
      Complex.finiteAbelPlanaLogRightEndpointUpperRectangle_subset_capCollar
        hρ hρT
  have hopen :
      (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
        Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
    intro z hz
    have hclosed_rect :
        z ∈ ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) := by
      have hzdata := Complex.mem_reProdIm.mp hz
      exact
        Complex.mem_reProdIm.mpr
          ⟨Set.Ioo_subset_Icc_self hzdata.1,
            Set.Ioo_subset_Icc_self hzdata.2⟩
    exact hclosed hclosed_rect
  have hcontinuous_closed :
      ContinuousOn f ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) :=
    hcont.mono hclosed
  have hdifferentiable_open :
      DifferentiableOn ℂ f
        (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) :=
    hdiff.mono hopen
  have hcauchy :
      (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
          (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) =
        0 :=
    Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      f z₀ z₁ hcontinuous_closed hdifferentiable_open
  simpa [z₀, z₁, M, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]
    using hcauchy

/-- The local Cauchy-Goursat deformation across the right endpoint
half-rectangle collar outside the deleted disk.

This is the reflected analogue of the left endpoint half-rectangle theorem.  The
two horizontal chord integrals, the middle adjacent safe vertical segment, and
the counterclockwise left semicircle bound the left half-rectangle with the
endpoint disk removed at `N + 1`. -/
theorem Complex.rightEndpointHalfRectangleDeletedDiskBoundary_eq_zero
    (f : ℂ → ℂ)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ)) :
    (let M : ℕ := N + 1
      -(∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
          f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
        (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
          f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
          Complex.I *
            (∫ y : ℝ in (-ρ)..ρ,
              f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          f ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      0 := by
  let M : ℕ := N + 1
  let c : ℂ := (M : ℂ)
  have hcont_model :
      ContinuousOn f (Complex.leftHalfRectangleDeletedDiskDomain c T ρ ρ) := by
    dsimp [c, M]
    simpa [Complex.leftHalfRectangleDeletedDiskDomain,
      Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain]
      using hcont
  have hdiff_model :
      DifferentiableOn ℂ f (Complex.leftHalfRectangleDeletedDiskDomain c T ρ ρ) := by
    dsimp [c, M]
    simpa [Complex.leftHalfRectangleDeletedDiskDomain,
      Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain]
      using hdiff
  have hmodel :
      -(∫ x : ℝ in (c.re - ρ)..c.re,
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
          (∫ x : ℝ in (c.re - ρ)..c.re,
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
                f (((c.re - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        0 :=
    Complex.leftHalfRectangleDeletedDiskBoundary_eq_zero
      f c T ρ le_rfl hρ (by simpa [abs_of_pos hT] using hρT)
      hcont_model hdiff_model
  dsimp [c, M] at hmodel ⊢
  simpa using hmodel

/-- The full adjacent safe vertical side in the right endpoint cap is the
concatenation of its lower, middle, and upper pieces. -/
theorem Complex.rightEndpointSafeVerticalIntegral_split_three
    (f : ℂ → ℂ)
    (N : ℕ)
    (T ρ : ℝ)
    (hlower :
      IntervalIntegrable
        (fun y : ℝ =>
          let M : ℕ := N + 1
          f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        volume (-T) (-ρ))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ =>
          let M : ℕ := N + 1
          f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        volume (-ρ) ρ)
    (hupper :
      IntervalIntegrable
        (fun y : ℝ =>
          let M : ℕ := N + 1
          f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        volume ρ T) :
    (let M : ℕ := N + 1
      ∫ y : ℝ in (-T)..T,
        f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
      (let M : ℕ := N + 1
        (∫ y : ℝ in (-T)..(-ρ),
          f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) +
          (∫ y : ℝ in (-ρ)..ρ,
            f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) +
            ∫ y : ℝ in ρ..T,
              f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) := by
  let M : ℕ := N + 1
  let g : ℝ → ℂ := fun y : ℝ =>
    f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))
  have hleft :
      (∫ y : ℝ in (-T)..(-ρ), g y) +
          ∫ y : ℝ in (-ρ)..ρ, g y =
        ∫ y : ℝ in (-T)..ρ, g y :=
    intervalIntegral.integral_add_adjacent_intervals hlower hmiddle
  have hleft_integrable :
      IntervalIntegrable g volume (-T) ρ :=
    hlower.trans hmiddle
  have hright :
      (∫ y : ℝ in (-T)..ρ, g y) +
          ∫ y : ℝ in ρ..T, g y =
        ∫ y : ℝ in (-T)..T, g y :=
    intervalIntegral.integral_add_adjacent_intervals hleft_integrable hupper
  calc
    (let M : ℕ := N + 1
      ∫ y : ℝ in (-T)..T,
        f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        ∫ y : ℝ in (-T)..T, g y := by
      rfl
    _ =
        (∫ y : ℝ in (-T)..ρ, g y) +
          ∫ y : ℝ in ρ..T, g y := hright.symm
    _ =
        ((∫ y : ℝ in (-T)..(-ρ), g y) +
            ∫ y : ℝ in (-ρ)..ρ, g y) +
          ∫ y : ℝ in ρ..T, g y := by
      rw [hleft]
    _ =
      (let M : ℕ := N + 1
        (∫ y : ℝ in (-T)..(-ρ),
          f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) +
          (∫ y : ℝ in (-ρ)..ρ,
            f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) +
            ∫ y : ℝ in ρ..T,
              f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) := by
      dsimp [g, M]
      ring

/-- Complex-linear algebra assembling the two rectangular right endpoint
identities and the right deleted-disk collar identity into the full right endpoint
cap/collar boundary identity. -/
theorem Complex.rightEndpointCapCollarBoundary_algebra
    (lowerT upperT lowerChord upperChord pvLower pvUpper safe safeLower
      safeMiddle safeUpper arc : ℂ)
    (hsafe : safe = safeLower + safeMiddle + safeUpper)
    (hlower :
      lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower = 0)
    (hupper :
      upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper = 0)
    (hhalf :
      -lowerChord + upperChord - Complex.I * safeMiddle - arc = 0) :
    lowerT - upperT + Complex.I * (pvLower + pvUpper) -
        Complex.I * safe - arc =
      0 := by
  have hsum :
      (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
          (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
            (-lowerChord + upperChord - Complex.I * safeMiddle - arc) =
        0 := by
    rw [hlower, hupper, hhalf]
    ring
  calc
    lowerT - upperT + Complex.I * (pvLower + pvUpper) -
        Complex.I * safe - arc =
        (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
          (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
            (-lowerChord + upperChord - Complex.I * safeMiddle - arc) := by
      rw [hsafe]
      ring
    _ = 0 := hsum

/-- Oriented unnormalized boundary expression of the right endpoint cap/collar.

The five terms are, in order: lower collar, upper collar with opposite
orientation, principal-value right edge, adjacent safe-strip edge with opposite
orientation, and the endpoint semicircle with the punctured-domain orientation
moved to the left-hand side. -/
noncomputable def Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
      Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
    (let M : ℕ := N + 1
      ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))

/-- Unfolding of the right endpoint cap/collar oriented boundary into its
straight collar sides and left semicircular deleted-boundary side. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollarOrientedBoundary_unfold
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ =
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
  rfl

/-- Generic oriented boundary integral of a right endpoint cap/collar. -/
noncomputable def Complex.rightEndpointCapCollarOrientedBoundaryIntegral
    (f : ℂ → ℂ)
    (N : ℕ)
    (T ρ : ℝ) : ℂ :=
  let M : ℕ := N + 1
  (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (T : ℂ))) -
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (T : ℂ))) +
        Complex.I *
          ((∫ y : ℝ in (-T)..(-ρ), f ((M : ℂ) + Complex.I * (y : ℂ))) +
            ∫ y : ℝ in ρ..T, f ((M : ℂ) + Complex.I * (y : ℂ))) -
          Complex.I *
            (∫ y : ℝ in (-T)..T, f (((M : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ))) -
    ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
      f ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Generic Cauchy-Goursat theorem for the right endpoint cap/collar.

This is the reflected local deleted-disk collar contour theorem at the endpoint
`N + 1`. -/
theorem Complex.rightEndpointCapCollarOrientedBoundaryIntegral_eq_zero
    (f : ℂ → ℂ)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ)) :
    Complex.rightEndpointCapCollarOrientedBoundaryIntegral f N T ρ = 0 := by
  let M : ℕ := N + 1
  let g : ℝ → ℂ := fun y : ℝ =>
    f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))
  have hsafe_integrable :
      ∀ a b : ℝ,
        (∀ y ∈ [[a, b]], y ∈ [[-T, T]]) →
          IntervalIntegrable g volume a b := by
    intro a b hinterval_subset
    have hpath_cont :
        ContinuousOn
          (fun y : ℝ =>
            ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
          [[a, b]] := by
      exact (continuous_const.add (continuous_const.mul continuous_ofReal)).continuousOn
    have hpath_mem :
        ∀ y ∈ [[a, b]],
          ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)) ∈
            Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
      intro y hy
      dsimp [M] at hinterval_subset ⊢
      exact
        Complex.finiteAbelPlanaLogRightEndpointSafeVerticalPoint_mem_capCollar
          hρ (hinterval_subset y hy)
    have hg_cont :
        ContinuousOn g [[a, b]] :=
      hcont.comp_continuousOn hpath_cont hpath_mem
    exact hg_cont.intervalIntegrable
  have hlower_interval :
      ∀ y ∈ [[(-T), (-ρ)]], y ∈ [[-T, T]] := by
    intro y hy
    have horder : -T ≤ -ρ := by linarith
    have hyIcc : y ∈ Set.Icc (-T) (-ρ) := by
      simpa [Set.uIcc_of_le horder] using hy
    have hy_le_T : y ≤ T := by linarith [hyIcc.2, hρ]
    simpa using And.intro hyIcc.1 hy_le_T
  have hmiddle_interval :
      ∀ y ∈ [[(-ρ), ρ]], y ∈ [[-T, T]] := by
    intro y hy
    have horder : -ρ ≤ ρ := by linarith
    have hyIcc : y ∈ Set.Icc (-ρ) ρ := by
      simpa [Set.uIcc_of_le horder] using hy
    have hy_ge_negT : -T ≤ y := by linarith [hρT, hyIcc.1]
    have hy_le_T : y ≤ T := by linarith [hρT, hyIcc.2]
    simpa using And.intro hy_ge_negT hy_le_T
  have hupper_interval :
      ∀ y ∈ [[ρ, T]], y ∈ [[-T, T]] := by
    intro y hy
    have horder : ρ ≤ T := le_of_lt hρT
    have hyIcc : y ∈ Set.Icc ρ T := by
      simpa [Set.uIcc_of_le horder] using hy
    have hy_ge_negT : -T ≤ y := by linarith [hT, hρ, hyIcc.1]
    simpa using And.intro hy_ge_negT hyIcc.2
  have hsafe_split :
      (let M : ℕ := N + 1
        ∫ y : ℝ in (-T)..T,
          f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        (let M : ℕ := N + 1
          (∫ y : ℝ in (-T)..(-ρ),
            f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) +
            (∫ y : ℝ in (-ρ)..ρ,
              f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) +
              ∫ y : ℝ in ρ..T,
                f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) := by
    exact
      Complex.rightEndpointSafeVerticalIntegral_split_three
        f N T ρ
        (hsafe_integrable (-T) (-ρ) hlower_interval)
        (hsafe_integrable (-ρ) ρ hmiddle_interval)
        (hsafe_integrable ρ T hupper_interval)
  have hlower_zero :
      (let M : ℕ := N + 1
        (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (T : ℂ))) -
            (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
              Complex.I *
                (∫ y : ℝ in (-T)..(-ρ), f ((M : ℂ) + Complex.I * (y : ℂ))) -
                Complex.I *
                  (∫ y : ℝ in (-T)..(-ρ),
                    f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))) =
        0 :=
    Complex.rightEndpointLowerRectangleBoundaryIntegral_eq_zero
      f N T hT hρ hρT hcont hdiff
  have hupper_zero :
      (let M : ℕ := N + 1
        (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
            (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (T : ℂ))) +
              Complex.I *
                (∫ y : ℝ in ρ..T, f ((M : ℂ) + Complex.I * (y : ℂ))) -
                Complex.I *
                  (∫ y : ℝ in ρ..T,
                    f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))) =
        0 :=
    Complex.rightEndpointUpperRectangleBoundaryIntegral_eq_zero
      f N T hρ hρT hcont hdiff
  have hhalf_zero :
      (let M : ℕ := N + 1
        -(∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
            f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
          (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
            f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (-ρ)..ρ,
                f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            f ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        0 :=
    Complex.rightEndpointHalfRectangleDeletedDiskBoundary_eq_zero
      f N T hT hρ hρT hcont hdiff
  dsimp [Complex.rightEndpointCapCollarOrientedBoundaryIntegral]
  exact
    Complex.rightEndpointCapCollarBoundary_algebra
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (T : ℂ)))
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (T : ℂ)))
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (ρ : ℂ)))
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (ρ : ℂ)))
      (∫ y : ℝ in (-T)..(-ρ), f ((M : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in ρ..T, f ((M : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in (-T)..T,
        f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in (-T)..(-ρ),
        f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in (-ρ)..ρ,
        f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in ρ..T,
        f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
      (∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
        f ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (by simpa [M] using hsafe_split)
      (by simpa [M] using hlower_zero)
      (by simpa [M] using hupper_zero)
      (by simpa [M] using hhalf_zero)

/-- The Abel-Plana right endpoint oriented boundary is the generic right cap
boundary specialized to the logarithmic cotangent rectangle integrand. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollarOrientedBoundary_eq_generic
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ =
      Complex.rightEndpointCapCollarOrientedBoundaryIntegral
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        N T ρ := by
  rfl

/-- Cauchy-Goursat on the right endpoint cap/collar domain.

This is the local deleted-disk collar theorem for the endpoint pole at
`N + 1`: the boundary of the left endpoint collar, after deleting the endpoint
semicircle, has zero integral. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero_owner
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 := by
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hcont_right :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ) :=
    Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_rightEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hcont
  have hdiff_right :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ) :=
    Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_rightEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hdiff
  calc
    Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ =
        Complex.rightEndpointCapCollarOrientedBoundaryIntegral
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          N T ρ := by
      exact
        Complex.finiteAbelPlana_log_rightEndpointCapCollarOrientedBoundary_eq_generic
          N w T ρ
    _ = 0 := by
      exact
        Complex.rightEndpointCapCollarOrientedBoundaryIntegral_eq_zero
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          N T hT hρ (by
            have hρ_abs : ρ < |T| / 2 := hdeleted_geometry.2.1
            have hT_abs : |T| = T := abs_of_pos hT
            rw [hT_abs] at hρ_abs
            linarith)
          hcont_right hdiff_right

/-- Owner Cauchy-Goursat statement for the two endpoint semicollars, in
oriented-boundary form.

Both endpoints use their named oriented-boundary objects. -/
theorem Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_orientedBoundary_pair_owner
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 ∧
      Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 := by
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hcont_left :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ) :=
    Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hcont
  have hdiff_left :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ) :=
    Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hdiff
  have hleft :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 :=
    Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero_owner
      (N := N) T hT hρ hdeleted_geometry hcont_left hdiff_left
  have hright :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 := by
    Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero_owner
      N T hT hρ hdeleted_geometry hcont hdiff
  exact ⟨hleft, hright⟩

/-- Endpoint half-collar Cauchy-Goursat in balance form.

This is the remaining planar topology input: the left endpoint right
half-collar and the right endpoint left half-collar have oriented boundary
zero, expressed as equality between their straight collar boundary and their
endpoint semicircular indentation.  The statement is deliberately local to the
two endpoint half-collars, not a full rectangle through an endpoint pole. -/
theorem Complex.finiteAbelPlana_log_endpointHalfCollarCauchyGoursat_balance_left_right
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) ∧
      (Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
            Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
          let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
  have hboundary :=
    Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_orientedBoundary_pair_owner
      N T hT hρ hdeleted_geometry hcont hdiff
  constructor
  · exact
      Complex.finiteAbelPlana_log_leftEndpointHalfCollar_balance_of_orientedBoundary_zero
        w T ρ hboundary.1
  · dsimp [Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary] at hboundary
    exact sub_eq_zero.mp hboundary.2

/-- Algebraic conversion from the left endpoint half-collar balance to the
oriented-boundary vanishing statement. -/
theorem Complex.finiteAbelPlana_log_leftEndpointHalfCollar_orientedBoundary_eq_zero_of_balance
    (w : ℂ)
    (T ρ : ℝ)
    (hbalance :
      Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 := by
  dsimp [Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary]
  exact sub_eq_zero.mpr hbalance

/-- Algebraic conversion from the right endpoint half-collar balance to the
unfolded oriented-boundary vanishing statement. -/
theorem Complex.finiteAbelPlana_log_rightEndpointHalfCollar_orientedBoundary_eq_zero_of_balance
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ)
    (hbalance :
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
        let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
        Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
      (let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 := by
  exact sub_eq_zero.mpr hbalance

/-- The two local endpoint half-collar Cauchy-Goursat identities.

This is the exact local topology input for the endpoint collars.  The left
identity is Cauchy-Goursat on the right half-rectangle based at `0`, with its
right semicircular deleted boundary.  The right identity is the translated
left half-rectangle based at `N + 1`, with its left semicircular deleted
boundary.  The displayed signs are the punctured-domain orientations:
lower collar, minus upper collar, adjacent safe vertical edge, minus
principal-value vertical edge, minus the endpoint semicircle. -/
theorem Complex.finiteAbelPlana_log_endpointHalfCollarCauchyGoursat_left_right
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 ∧
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 := by
  have hbalance :=
    Complex.finiteAbelPlana_log_endpointHalfCollarCauchyGoursat_balance_left_right
      N T hT hρ hdeleted_geometry hcont hdiff
  exact
    ⟨Complex.finiteAbelPlana_log_leftEndpointHalfCollar_orientedBoundary_eq_zero_of_balance
        w T ρ hbalance.1,
      Complex.finiteAbelPlana_log_rightEndpointHalfCollar_orientedBoundary_eq_zero_of_balance
        N w T ρ hbalance.2⟩

/-- Left endpoint half-collar Cauchy-Goursat identity, extracted from the
local endpoint half-collar pair. -/
theorem Complex.finiteAbelPlana_log_leftEndpointHalfCollarCauchyGoursat_orientedBoundary_eq_zero
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 := by
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hcont_left :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ) :=
    Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hcont
  have hdiff_left :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ) :=
    Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hdiff
  exact
    Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero_owner
      (N := N) T hT hρ hdeleted_geometry hcont_left hdiff_left

/-- Right endpoint half-collar Cauchy-Goursat identity, extracted from the
local endpoint half-collar pair. -/
theorem Complex.finiteAbelPlana_log_rightEndpointHalfCollarCauchyGoursat_orientedBoundary_eq_zero
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
        Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
      (let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 := by
  have hboundary :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 :=
    Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero_owner
      N T hT hρ hdeleted_geometry hcont hdiff
  dsimp [Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary] at hboundary
  exact hboundary

/-- Assembly of the endpoint semicollar pair from the two local half-collar
Cauchy-Goursat identities. -/
theorem Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_pair_of_halfCollars
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hleft :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0)
    (hright :
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 ∧
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 := by
  exact ⟨hleft, hright⟩

/-- Shared semicollar Cauchy-Goursat owner statement for the endpoint caps.

Each endpoint domain is a half-rectangle with the endpoint disk removed.
Its oriented boundary is
`lower collar - upper collar + safe vertical edge - PV vertical edge -
endpoint semicircle`, with the right endpoint obtained from the same local
semicollar geometry by translation and reflection.  The second conjunct is
written in unfolded form so the same owner theorem can serve the right wrapper
after the right endpoint boundary is named. -/
theorem Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_orientedBoundary_eq_zero_pair
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 ∧
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 := by
  have hleft :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 :=
    Complex.finiteAbelPlana_log_leftEndpointHalfCollarCauchyGoursat_orientedBoundary_eq_zero
      N T hT hρ hdeleted_geometry hcont hdiff
  have hright :
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 :=
    Complex.finiteAbelPlana_log_rightEndpointHalfCollarCauchyGoursat_orientedBoundary_eq_zero
      N T hT hρ hdeleted_geometry hcont hdiff
  exact
    Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_pair_of_halfCollars
      N T hleft hright

/-- Cauchy-Goursat on the left endpoint cap/collar domain, with the boundary
orientation identified with the existing named side and indentation integrals.

This is the exact local classical proof obligation: apply Cauchy-Goursat to the
punctured cap/collar domain and match its oriented boundary to the lower collar,
upper collar, adjacent safe-strip vertical edge, principal-value left edge, and
right endpoint semicircle. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 := by
  exact
    (Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_orientedBoundary_eq_zero_pair
      N T hT hρ hdeleted_geometry hcont hdiff).1

/-- Algebraic extraction of the left endpoint semicircle from the oriented
cap/collar boundary equation. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollar_balance_of_orientedBoundary_eq_zero
    (w : ℂ)
    (T ρ : ℝ)
    (hboundary :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0) :
    Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
        Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
      ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  dsimp [Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary] at hboundary
  exact sub_eq_zero.mp hboundary

/-- The left endpoint oriented boundary vanishes exactly when the straight
collar boundary equals the right semicircular indentation integral. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero_iff_balance
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 ↔
      Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  constructor
  · intro hboundary
    exact
      Complex.finiteAbelPlana_log_leftEndpointCapCollar_balance_of_orientedBoundary_eq_zero
        w T ρ hboundary
  · intro hbalance
    dsimp [Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary]
    exact sub_eq_zero.mpr hbalance

/-- Unnormalized local Cauchy-Goursat balance for the left endpoint collar.

The contour is the left endpoint cap/collar subdomain: the lower horizontal
collar from `0` to `ρ`, the safe-strip vertical edge at `x = ρ`, the upper
horizontal collar with opposite orientation, the principal-value left vertical
edge with opposite orientation, and the right semicircular indentation around
the deleted endpoint pole.  Cauchy's theorem on that punctured collar says the
sum of these oriented pieces is zero; equivalently, the straight cap/collar
boundary equals the endpoint indentation integral with the displayed
orientation. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollar_unnormalizedCauchy_balance
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
        Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
      ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  have hboundary :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 :=
    Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero
      N T hT hρ hdeleted_geometry hcont hdiff
  exact
    Complex.finiteAbelPlana_log_leftEndpointCapCollar_balance_of_orientedBoundary_eq_zero
      w T ρ hboundary

/-- The left endpoint collar, together with the adjacent safe-strip boundary
pieces, contributes exactly the left endpoint deleted semicircle.

This is the one-piece Cauchy-Goursat statement for the left endpoint collar in
the finite Abel-Plana punctured rectangle.  Its proof is the classical local
rectangle argument: apply Cauchy-Goursat on the small endpoint collar
subdomain, then identify the one curved boundary component with the
principal-value left endpoint indentation. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollarCauchy_balance
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarBoundary w T ρ =
      Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ := by
  have hlocal :
      Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
    Complex.finiteAbelPlana_log_leftEndpointCapCollar_unnormalizedCauchy_balance
      N T hT hρ hdeleted_geometry hcont hdiff
  change
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
  exact
    congrArg
      (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
      hlocal

/-- Solving the right endpoint oriented-boundary Cauchy equation gives the
right endpoint half-collar balance. -/
theorem Complex.finiteAbelPlana_log_rightEndpointHalfCollar_balance_of_orientedBoundary_zero
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ)
    (hboundary :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0) :
    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
        let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  dsimp [Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary] at hboundary
  exact sub_eq_zero.mp hboundary

/-- Cauchy-Goursat on the right endpoint cap/collar domain, with the boundary
orientation identified with the existing named side and indentation integrals.

This is the exact local classical proof obligation: apply Cauchy-Goursat to the
punctured cap/collar domain and match its oriented boundary to the lower collar,
upper collar, principal-value right edge, adjacent safe-strip vertical edge, and
left endpoint semicircle. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 := by
  exact
    Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero_owner
      N T hT hρ hdeleted_geometry hcont hdiff

/-- Algebraic extraction of the right endpoint semicircle from the oriented
cap/collar boundary equation. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollar_balance_of_orientedBoundary_eq_zero
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ)
    (hboundary :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0) :
    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
        Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
      let M : ℕ := N + 1
      ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  dsimp [Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary] at hboundary
  exact sub_eq_zero.mp hboundary

/-- The right endpoint oriented boundary vanishes exactly when the straight
collar boundary equals the left semicircular indentation integral. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero_iff_balance
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 ↔
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
        let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  constructor
  · intro hboundary
    exact
      Complex.finiteAbelPlana_log_rightEndpointCapCollar_balance_of_orientedBoundary_eq_zero
        N w T ρ hboundary
  · intro hbalance
    dsimp [Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary]
    exact sub_eq_zero.mpr hbalance

/-- Unnormalized local Cauchy-Goursat balance for the right endpoint collar.

The contour is the right endpoint cap/collar subdomain: the lower horizontal
collar from `N + 1 - ρ` to `N + 1`, the principal-value right vertical edge,
the upper horizontal collar with opposite orientation, the adjacent safe-strip
vertical edge with opposite orientation, and the left semicircular indentation
around the deleted endpoint pole.  Cauchy's theorem on that punctured collar
says the sum of these oriented pieces is zero; equivalently, the straight
cap/collar boundary equals the endpoint indentation integral with the displayed
orientation. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollar_unnormalizedCauchy_balance
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
        Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
      let M : ℕ := N + 1
      ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  have hboundary :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 :=
    Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero
      N T hT hρ hdeleted_geometry hcont hdiff
  exact
    Complex.finiteAbelPlana_log_rightEndpointCapCollar_balance_of_orientedBoundary_eq_zero
      N w T ρ hboundary

/-- The right endpoint collar, together with the adjacent safe-strip boundary
pieces, contributes exactly the right endpoint deleted semicircle.

This is the right endpoint version of the local collar Cauchy-Goursat
calculation.  The ordinary straight edges cancel against the adjacent strip
orientation; the surviving curved boundary is the right endpoint indentation. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollarCauchy_balance
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary N w T ρ =
      Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ := by
  have hlocal :
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
        let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
    Complex.finiteAbelPlana_log_rightEndpointCapCollar_unnormalizedCauchy_balance
      N T hT hρ hdeleted_geometry hcont hdiff
  change
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ) =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
  exact
    congrArg
	      (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
	      hlocal

end

end LFunctions
end Boundary
