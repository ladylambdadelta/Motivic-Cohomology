import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.SetIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteHoleSubdivision
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaEndpointCapCollars.Foundation.Owner

/-!
# Right endpoint cap-collar domains and Cauchy-Goursat theorems

Definitions and theorems for the right endpoint cap-collar domain and its boundary
analysis, corresponding to the endpoint pole at N + 1.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

notation:max "[[" a "," b "]]" => Set.Icc a b

/-- Helper: Real part of complex exponential in cap-collar domain. -/
private lemma capCollar_exp_re (N : ℕ) (ρ θ : ℝ) :
    ((↑(N + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * θ)).re =
      ((N + 1 : ℕ) : ℝ) + ρ * Real.cos θ := by
  have h1 : ((ρ : ℂ) * Complex.exp (Complex.I * θ)).re = ρ * Real.cos θ := by
    calc ((ρ : ℂ) * Complex.exp (Complex.I * θ)).re
        = (ρ : ℂ).re * (Complex.exp (Complex.I * θ)).re -
          (ρ : ℂ).im * (Complex.exp (Complex.I * θ)).im := Complex.mul_re _ _
      _ = ρ * (Complex.exp (Complex.I * θ)).re := by
        simp [Complex.ofReal_re, Complex.ofReal_im]
      _ = ρ * Real.cos θ := by
        simp [Complex.exp_mul_I_re]
  calc ((↑(N + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * θ)).re
      = (↑(N + 1 : ℕ) : ℂ).re + ((ρ : ℂ) * Complex.exp (Complex.I * θ)).re := Complex.add_re _ _
    _ = ((N + 1 : ℕ) : ℝ) + ρ * Real.cos θ := by
      simp [Complex.ofReal_re]; rw [h1]

/-- Helper: Imaginary part of complex exponential in cap-collar domain. -/
private lemma capCollar_exp_im (N : ℕ) (ρ θ : ℝ) :
    ((↑(N + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * θ)).im =
      ρ * Real.sin θ := by
  have h1 : ((ρ : ℂ) * Complex.exp (Complex.I * θ)).im = ρ * Real.sin θ := by
    calc ((ρ : ℂ) * Complex.exp (Complex.I * θ)).im
        = (ρ : ℂ).re * (Complex.exp (Complex.I * θ)).im +
          (ρ : ℂ).im * (Complex.exp (Complex.I * θ)).re := Complex.mul_im _ _
      _ = ρ * (Complex.exp (Complex.I * θ)).im := by
        simp [Complex.ofReal_re, Complex.ofReal_im]
      _ = ρ * Real.sin θ := by
        simp [Complex.exp_mul_I_im]
  calc ((↑(N + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * θ)).im
      = (↑(N + 1 : ℕ) : ℂ).im + ((ρ : ℂ) * Complex.exp (Complex.I * θ)).im := Complex.add_im _ _
    _ = ρ * Real.sin θ := by
      simp [Complex.ofReal_im]; rw [h1]

/-- Helper: Imaginary part of complex number plus pure imaginary. -/
private lemma capCollar_im_pure (N : ℕ) (y : ℝ) :
    ((↑(N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)).im = y := by
  have h1 : (Complex.I * (y : ℂ)).im = y := Complex.I_mul_im y
  calc ((↑(N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)).im
      = (↑(N + 1 : ℕ) : ℂ).im + (Complex.I * (y : ℂ)).im := Complex.add_im _ _
    _ = 0 + y := by simp [Complex.ofReal_im]; rw [h1]
    _ = y := zero_add y

/-- Helper: Equivalence between cap-collar point and circleMap. -/
private lemma capCollar_eq_circleMap (N : ℕ) (ρ θ : ℝ) :
    ((↑(N + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      circleMap ((N + 1 : ℕ) : ℂ) ρ θ := by
  unfold circleMap
  rfl

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
          z ∉ Metric.ball ((N + 1 : ℕ) : ℂ) ρ :=
  ⟨fun hz => ⟨hz.1.1, hz.1.2, hz.2⟩,
   fun hz => ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩⟩

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
    exact hzcentral
  · intro hzball
    have hm_lt_succ : m < N + 1 :=
      let hm_lt : m < N + 2 := Finset.mem_range.mp hm
      Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hm_lt) hmcenter
    have hm_le_N : m ≤ N := Nat.lt_succ_iff.mp hm_lt_succ
    have hm_real_le_N : ((m : ℕ) : ℝ) ≤ (N : ℝ) :=
      Real.natCast_le_natCast hm_le_N
    have hρ_lt_half : ρ < (1 : ℝ) / 2 :=
      Real.lt_one_div_two_of_lt_one_div_four hρquarter
    have hleft_le_right :
        ((N + 1 : ℕ) : ℝ) - ρ ≤ ((N + 1 : ℕ) : ℝ) :=
      Real.sub_nonneg_le_self (((N + 1 : ℕ) : ℝ)) ρ hρnonneg
    have hzIcc :
        z.re ∈ Set.Icc (((N + 1 : ℕ) : ℝ) - ρ) (((N + 1 : ℕ) : ℝ)) :=
      Real.endpoint_bounds_of_mem_uIcc hleft_le_right hzre
    have hzre_ge : ((N + 1 : ℕ) : ℝ) - ρ ≤ z.re := hzIcc.1
    have hdist_lt : ‖z - (m : ℂ)‖ < ρ :=
      Complex.endpoint_norm_lt_of_mem_ball z (m : ℂ) hzball
    have hre_norm :
        |(z - (m : ℂ)).re| ≤ ‖z - (m : ℂ)‖ :=
      Complex.endpoint_abs_re_le_norm (z - (m : ℂ))
    have hre_ge : ρ ≤ (z - (m : ℂ)).re :=
      let hbase :
          ρ ≤ (((N + 1 : ℕ) : ℝ) - ρ) - (N : ℝ) :=
        Real.endpoint_radius_le_successor_minus_radius_sub_nat N hρ_lt_half
      let hmono :
          (((N + 1 : ℕ) : ℝ) - ρ) - (N : ℝ) ≤
            z.re - (m : ℝ) :=
        sub_le_sub hzre_ge hm_real_le_N
      let hreal : ρ ≤ z.re - (m : ℝ) :=
        hbase.trans hmono
      Eq.mpr
        (congrArg (fun r : ℝ => ρ ≤ r)
          (Complex.endpoint_sub_natCast_re z m).symm)
        hreal
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
      ((N + 1 : ℕ) : ℝ) - ρ ≤ ((N + 1 : ℕ) : ℝ) :=
    Real.sub_nonneg_le_self ((N + 1 : ℕ) : ℝ) ρ hρnonneg
  have hzIcc :
      z.re ∈ Set.Icc (((N + 1 : ℕ) : ℝ) - ρ) (((N + 1 : ℕ) : ℝ)) :=
    Real.endpoint_bounds_of_mem_uIcc hleft_le_right hz.1
  have hρ_lt_one : ρ < 1 :=
    Real.lt_one_of_lt_one_div_four hρquarter
  refine Complex.mem_reProdIm.mpr ⟨?_, hz.2⟩
  have hnonneg : 0 ≤ ((N + 1 : ℕ) : ℝ) - ρ :=
    let hone_le_succ : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) :=
      Real.one_le_natCast_succ N
    let hρ_le_succ : ρ ≤ ((N + 1 : ℕ) : ℝ) :=
      (le_of_lt hρ_lt_one).trans hone_le_succ
    sub_nonneg.mpr hρ_le_succ
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
      ∀ m ∈ Finset.range (N + 2), z ∉ Metric.ball (m : ℂ) ρ := fun m hm =>
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
      (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ) :=
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
      (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ) :=
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
    unfold M
    exact capCollar_exp_re (N + 1) ρ θ
  have him :
      ((((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im)) =
        ρ * Real.sin θ := by
    unfold M
    exact capCollar_exp_im (N + 1) ρ θ
  have hcos_nonpos : Real.cos θ ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 hθ.2
  have hcos_ge_neg_one : -1 ≤ Real.cos θ :=
    (Real.cos_mem_Icc θ).1
  have hre_mem :
      (((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re) ∈
        [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] :=
    let hleft : (M : ℝ) - ρ ≤ (M : ℝ) + ρ * Real.cos θ :=
      let hmul : -ρ ≤ ρ * Real.cos θ :=
        calc
          -ρ = ρ * (-1) := (mul_neg_one ρ).symm
          _ ≤ ρ * Real.cos θ :=
            mul_le_mul_of_nonneg_left hcos_ge_neg_one hρnonneg
      calc
        (M : ℝ) - ρ = (M : ℝ) + -ρ :=
          sub_eq_add_neg (M : ℝ) ρ
        _ ≤ (M : ℝ) + ρ * Real.cos θ :=
          add_le_add_left hmul (M : ℝ)
    let hright : (M : ℝ) + ρ * Real.cos θ ≤ (M : ℝ) :=
      let hmul : ρ * Real.cos θ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hρnonneg hcos_nonpos
      add_le_of_nonpos_right hmul
    let hinterval :
        ((M : ℝ) + ρ * Real.cos θ) ∈
          [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] :=
      unfold M at hleft hright
      Real.endpoint_mem_uIcc_of_bounds
        (Real.sub_nonneg_le_self ((N + 1 : ℕ) : ℝ) ρ hρnonneg)
        (And.intro hleft hright)
    Real.endpoint_mem_uIcc_congr hre hinterval
  have hsin_abs : |Real.sin θ| ≤ 1 :=
    abs_le.mpr (Real.sin_mem_Icc θ)
  have him_abs : |ρ * Real.sin θ| ≤ ρ :=
    calc
      |ρ * Real.sin θ| = ρ * |Real.sin θ| :=
        calc
          |ρ * Real.sin θ| = |ρ| * |Real.sin θ| :=
            abs_mul ρ (Real.sin θ)
          _ = ρ * |Real.sin θ| :=
            congrArg (fun r : ℝ => r * |Real.sin θ|)
              (abs_of_nonneg hρnonneg)
      _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hsin_abs hρnonneg
      _ = ρ := mul_one ρ
  have him_mem :
      (((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im) ∈
        [[-T, T]] :=
    let habsT : |ρ * Real.sin θ| ≤ T :=
      him_abs.trans (le_of_lt hρT)
    let hb := abs_le.mp habsT
    Real.endpoint_mem_uIcc_congr him
      (Real.endpoint_mem_uIcc_of_bounds (neg_le_self hT.le) hb)
  have hnot_ball :
      (((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) ∉
        Metric.ball ((N + 1 : ℕ) : ℂ) ρ :=
    let hz_eq :
        (((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
          circleMap ((N + 1 : ℕ) : ℂ) ρ θ := by
      unfold M
      exact capCollar_eq_circleMap (N + 1) ρ θ
    hz_eq ▸ circleMap_not_mem_ball ((N + 1 : ℕ) : ℂ) ρ θ
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
      unfold M
      have h1 : (Complex.I * (y : ℂ)).re = 0 := Complex.I_mul_re y
      calc ((↑(N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)).re
          = (↑(N + 1 : ℕ) : ℂ).re + (Complex.I * (y : ℂ)).re := Complex.add_re _ _
        _ = (↑(N + 1 : ℕ) : ℂ).re + 0 := by rw [h1]
        _ = (↑(N + 1 : ℕ) : ℂ).re := add_zero _
        _ = (↑(N + 1 : ℕ) : ℝ) := Complex.ofReal_re _
    have hleft : ((N + 1 : ℕ) : ℝ) - ρ ≤ ((N + 1 : ℕ) : ℝ) := by
      exact Real.sub_nonneg_le_self ((N + 1 : ℕ) : ℝ) ρ hρnonneg
    exact
      Real.endpoint_mem_uIcc_congr hre
        (Real.endpoint_mem_uIcc_of_bounds hleft
          (And.intro hleft le_rfl))
  have him_mem :
      (((M : ℂ) + Complex.I * (y : ℂ)).im) ∈ [[-T, T]] := by
    rcases hy with hy | hy
    · have horder : -T ≤ -ρ := hy.1
      have hyIcc : y ∈ Set.Icc (-T) (-ρ) :=
        Real.endpoint_bounds_of_mem_uIcc horder hy
      have hleT : y ≤ T :=
        hyIcc.2.trans (Real.endpoint_neg_radius_le_height hT hρ)
      have hy_uIcc : y ∈ [[-T, T]] :=
        Real.endpoint_mem_uIcc_of_bounds (neg_le_self hT.le)
          (And.intro hyIcc.1 hleT)
      have him : (((M : ℂ) + Complex.I * (y : ℂ)).im) = y := by
        unfold M
        exact capCollar_im_pure (N + 1) y
      exact Real.endpoint_mem_uIcc_congr him hy_uIcc
    · have horder : ρ ≤ T := hy.1
      have hyIcc : y ∈ Set.Icc ρ T :=
        Real.endpoint_bounds_of_mem_uIcc horder hy
      have hge_negT : -T ≤ y :=
        (Real.endpoint_neg_height_le_radius hT hρ).trans hyIcc.1
      have hy_uIcc : y ∈ [[-T, T]] :=
        Real.endpoint_mem_uIcc_of_bounds (neg_le_self hT.le)
          (And.intro hge_negT hyIcc.2)
      have him : (((M : ℂ) + Complex.I * (y : ℂ)).im) = y := by
        unfold M
        exact capCollar_im_pure (N + 1) y
      exact Real.endpoint_mem_uIcc_congr him hy_uIcc
  have hnot_ball :
      (((M : ℂ) + Complex.I * (y : ℂ))) ∉
        Metric.ball ((N + 1 : ℕ) : ℂ) ρ := by
    intro hball
    have hdist : ‖(((M : ℂ) + Complex.I * (y : ℂ)) - ((N + 1 : ℕ) : ℂ))‖ < ρ :=
      Complex.endpoint_norm_lt_of_mem_ball
        (((M : ℂ) + Complex.I * (y : ℂ)))
        ((N + 1 : ℕ) : ℂ)
        hball
    have hρ_le_abs_y : ρ ≤ |y| := by
      rcases hy with hy | hy
      · have horder : -T ≤ -ρ := hy.1
        have hyIcc : y ∈ Set.Icc (-T) (-ρ) :=
          Real.endpoint_bounds_of_mem_uIcc horder hy
        have hneg : ρ ≤ -y :=
          Real.endpoint_neg_le_neg_of_le hyIcc.2
        exact hneg.trans (neg_le_abs y)
      · have horder : ρ ≤ T := hy.1
        have hyIcc : y ∈ Set.Icc ρ T :=
          Real.endpoint_bounds_of_mem_uIcc horder hy
        exact hyIcc.1.trans (le_abs_self y)
    have hnorm :
        ‖(((M : ℂ) + Complex.I * (y : ℂ)) - ((N + 1 : ℕ) : ℂ))‖ = |y| := by
      unfold M
      exact
        Complex.norm_centered_vertical_translate_sub_center
          (((N + 1 : ℕ) : ℂ))
          y
    have hdist_abs : |y| < ρ :=
      Eq.subst (motive := fun r : ℝ => r < ρ) hnorm hdist
    exact not_lt_of_ge hρ_le_abs_y hdist_abs
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
    exact Real.sub_nonneg_le_self ((N + 1 : ℕ) : ℝ) ρ hρnonneg
  have hre_mem :
      (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)).re) ∈
        [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] := by
    have hre :
        (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)).re) =
          ((N + 1 : ℕ) : ℝ) - ρ := by
      ring_nf
    exact
      Real.endpoint_mem_uIcc_congr hre
        (Real.endpoint_mem_uIcc_of_bounds hleft_le_right
          (And.intro le_rfl hleft_le_right))
  have him_mem :
      (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)).im) ∈ [[-T, T]] :=
    let him :
        (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)).im) = y :=
      Eq.trans (Complex.add_im (((N + 1 : ℕ) : ℝ) - ρ : ℂ) (Complex.I * (y : ℂ)))
        (Eq.trans (congrArg (0 + ·) (Complex.mul_im Complex.I (y : ℂ))) (zero_add y))
    Real.endpoint_mem_uIcc_congr him hy
  have hnot_ball :
      (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ))) ∉
        Metric.ball ((N + 1 : ℕ) : ℂ) ρ := by
    intro hball
    have hdist :
        ‖(((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
            ((N + 1 : ℕ) : ℂ))‖ < ρ :=
      Complex.endpoint_norm_lt_of_mem_ball
        (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)))
        ((N + 1 : ℕ) : ℂ)
        hball
    have hre_norm :
        |(((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
            ((N + 1 : ℕ) : ℂ)).re| ≤
          ‖(((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
            ((N + 1 : ℕ) : ℂ))‖ :=
      Complex.endpoint_abs_re_le_norm
        (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
          ((N + 1 : ℕ) : ℂ))
    have hρ_le_norm :
        ρ ≤ ‖(((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
            ((N + 1 : ℕ) : ℂ))‖ :=
      let hre_abs :
          |(((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
              ((N + 1 : ℕ) : ℂ)).re| = ρ :=
        let hre :
            ((((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
                ((N + 1 : ℕ) : ℂ)).re) = -ρ :=
          Eq.trans (Complex.sub_re ((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) (↑(N + 1 : ℕ)))
            (Eq.trans (congrArg (· - ↑(N + 1 : ℕ)) (Complex.add_re (((N + 1 : ℕ) : ℝ) - ρ : ℂ) (Complex.I * (y : ℂ))))
              (Eq.trans (congrArg ((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + 0 - ·) (Complex.ofReal_re (N + 1 : ℕ)))
                (Eq.trans (congrArg (· - ↑(N + 1 : ℕ)) (add_zero (((N + 1 : ℕ) : ℝ) - ρ : ℝ)))
                  (sub_right_inj.mpr rfl))))
        hre ▸ abs_neg ρ ▸ abs_of_nonneg hρnonneg
      hre_abs ▸ hre_norm
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
      z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] :=
    (Complex.mem_reProdIm.mp hz).1
  have hzim_lower : z.im ∈ [[-T, -ρ]] :=
    (Complex.mem_reProdIm.mp hz).2
  have horder : -T ≤ -ρ :=
    Real.endpoint_neg_height_le_neg_radius hρT
  have hzimIcc : z.im ∈ Set.Icc (-T) (-ρ) :=
    Real.endpoint_bounds_of_mem_uIcc horder hzim_lower
  have hzim : z.im ∈ [[-T, T]] :=
    let hleT : z.im ≤ T :=
      hzimIcc.2.trans
        (Real.endpoint_neg_radius_le_height (hρ.trans hρT) hρ)
    Real.endpoint_mem_uIcc_of_bounds (neg_le_self (le_of_lt (hρ.trans hρT)))
      (And.intro hzimIcc.1 hleT)
  have hnot_ball : z ∉ Metric.ball ((N + 1 : ℕ) : ℂ) ρ := fun hball =>
    let hρ_le_abs_im : ρ ≤ |(z - ((N + 1 : ℕ) : ℂ)).im| :=
      let hraw : ρ ≤ |z.im| :=
        let hneg : ρ ≤ -z.im :=
          Real.endpoint_neg_le_neg_of_le hzimIcc.2
        hneg.trans (neg_le_abs z.im)
      Eq.mpr
        (congrArg (fun r : ℝ => ρ ≤ |r|)
          (Complex.endpoint_sub_natCast_im z (N + 1)).symm)
        hraw
    let hdist : ‖z - ((N + 1 : ℕ) : ℂ)‖ < ρ :=
      Complex.endpoint_norm_lt_of_mem_ball z ((N + 1 : ℕ) : ℂ) hball
    let him_norm : |(z - ((N + 1 : ℕ) : ℂ)).im| ≤
        ‖z - ((N + 1 : ℕ) : ℂ)‖ :=
      Complex.endpoint_abs_im_le_norm (z - ((N + 1 : ℕ) : ℂ))
    not_lt_of_ge (hρ_le_abs_im.trans him_norm) hdist
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
    exact (Complex.mem_reProdIm.mp hz).1
  have hzim_upper : z.im ∈ [[ρ, T]] := by
    exact (Complex.mem_reProdIm.mp hz).2
  have horder : ρ ≤ T := le_of_lt hρT
  have hzimIcc : z.im ∈ Set.Icc ρ T :=
    Real.endpoint_bounds_of_mem_uIcc horder hzim_upper
  have hzim : z.im ∈ [[-T, T]] := by
    have hge_negT : -T ≤ z.im :=
      (Real.endpoint_neg_height_le_radius (hρ.trans hρT) hρ).trans
        hzimIcc.1
    exact
      Real.endpoint_mem_uIcc_of_bounds (neg_le_self (le_of_lt (hρ.trans hρT)))
        (And.intro hge_negT hzimIcc.2)
  have hnot_ball : z ∉ Metric.ball ((N + 1 : ℕ) : ℂ) ρ := by
    have hρ_le_abs_im : ρ ≤ |(z - ((N + 1 : ℕ) : ℂ)).im| := by
      have hraw : ρ ≤ |z.im| :=
        hzimIcc.1.trans (le_abs_self z.im)
      exact
        Eq.mpr
          (congrArg (fun r : ℝ => ρ ≤ |r|)
            (Complex.endpoint_sub_natCast_im z (N + 1)).symm)
          hraw
    exact
      fun hball =>
        let hdist : ‖z - ((N + 1 : ℕ) : ℂ)‖ < ρ :=
          Complex.endpoint_norm_lt_of_mem_ball z ((N + 1 : ℕ) : ℂ) hball
        let him_norm : |(z - ((N + 1 : ℕ) : ℂ)).im| ≤
            ‖z - ((N + 1 : ℕ) : ℂ)‖ :=
          Complex.endpoint_abs_im_le_norm (z - ((N + 1 : ℕ) : ℂ))
        not_lt_of_ge (hρ_le_abs_im.trans him_norm) hdist
  exact
    Complex.mem_finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hzre, hzim, hnot_ball⟩

/-- Transport the generic rectangular Cauchy-Goursat boundary to the lower
right endpoint cap coordinates. -/
theorem Complex.rightEndpointLowerRectangleBoundaryIntegral_of_rectBoundary
    (f : ℂ → ℂ)
    (N M : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hM : M = N + 1)
    (z₀ z₁ : ℂ)
    (hz₀ : z₀ = (((M : ℝ) - ρ : ℝ) : ℂ) - Complex.I * (T : ℂ))
    (hz₁ : z₁ = (M : ℂ) - Complex.I * (ρ : ℂ))
    (hrect :
      (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
          (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) =
        0) :
    (let M : ℕ := N + 1
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (T : ℂ))) -
          (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
            Complex.I *
              (∫ y : ℝ in (-T)..(-ρ), f ((M : ℂ) + Complex.I * (y : ℂ))) -
              Complex.I *
                (∫ y : ℝ in (-T)..(-ρ),
                  f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))) =
      0 := by
  subst z₀
  subst z₁
  subst M
  ring_nf at hrect
  exact hrect

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
    unfold z₀; unfold z₁; unfold M
    exact
      Complex.finiteAbelPlanaLogRightEndpointLowerRectangle_subset_capCollar
        hT hρ hρT
  have hopen :
      (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
        Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
    intro z hz
    have hclosed_rect :
        z ∈ ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) :=
      let hzdata := Complex.mem_reProdIm.mp hz
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
  exact
    Complex.rightEndpointLowerRectangleBoundaryIntegral_of_rectBoundary
      f N M T rfl z₀ z₁ rfl rfl hcauchy

/-- Transport the generic rectangular Cauchy-Goursat boundary to the upper
right endpoint cap coordinates. -/
theorem Complex.rightEndpointUpperRectangleBoundaryIntegral_of_rectBoundary
    (f : ℂ → ℂ)
    (N M : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hM : M = N + 1)
    (z₀ z₁ : ℂ)
    (hz₀ : z₀ = (((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (ρ : ℂ))
    (hz₁ : z₁ = (M : ℂ) + Complex.I * (T : ℂ))
    (hrect :
      (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
          (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) =
        0) :
    (let M : ℕ := N + 1
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
          (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (T : ℂ))) +
            Complex.I *
              (∫ y : ℝ in ρ..T, f ((M : ℂ) + Complex.I * (y : ℂ))) -
              Complex.I *
                (∫ y : ℝ in ρ..T,
                  f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))) =
      0 := by
  subst z₀
  subst z₁
  subst M
  ring_nf at hrect
  exact hrect

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
    unfold z₀
    unfold z₁
    unfold M
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
  exact
    Complex.rightEndpointUpperRectangleBoundaryIntegral_of_rectBoundary
      f N M T rfl z₀ z₁ rfl rfl hcauchy

/-- Transport the left-half deleted-disk model boundary to the right endpoint
half-collar coordinates. -/
theorem Complex.rightEndpointHalfRectangleDeletedDiskBoundary_of_model
    (f : ℂ → ℂ)
    (N M : ℕ)
    {ρ : ℝ}
    (hM : M = N + 1)
    (c : ℂ)
    (hc : c = (M : ℂ))
    (hmodel :
      (∫ x : ℝ in (c.re - ρ)..c.re,
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
          -(∫ x : ℝ in (c.re - ρ)..c.re,
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
                f (((c.re - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        0) :
    (let M : ℕ := N + 1
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
          f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
        -(∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
          f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
          Complex.I *
            (∫ y : ℝ in (-ρ)..ρ,
              f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          f ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      0 := by
  subst c
  subst M
  ring_nf at hmodel
  exact hmodel

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
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
          f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
        -(∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
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
    unfold c; unfold M; unfold Complex.leftHalfRectangleDeletedDiskDomain
    unfold Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain at hcont
    exact hcont
  have hdiff_model :
      DifferentiableOn ℂ f (Complex.leftHalfRectangleDeletedDiskDomain c T ρ ρ) := by
    unfold c; unfold M; unfold Complex.leftHalfRectangleDeletedDiskDomain
    unfold Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain at hdiff
    exact hdiff
  have hmodel :
      (∫ x : ℝ in (c.re - ρ)..c.re,
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
          -(∫ x : ℝ in (c.re - ρ)..c.re,
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
                f (((c.re - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        0 :=
    Complex.leftHalfRectangleDeletedDiskBoundary_eq_zero
      f c T ρ le_rfl hρ
      (Real.endpoint_radius_lt_abs_height hT hρT)
      hcont_model hdiff_model
  unfold c at hmodel ⊢
  unfold M at hmodel ⊢
  exact
    Complex.rightEndpointHalfRectangleDeletedDiskBoundary_of_model
      f N (N + 1) rfl ((N + 1 : ℕ) : ℂ) rfl hmodel

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
              f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) :=
  let M : ℕ := N + 1
  let g : ℝ → ℂ := fun y : ℝ =>
    f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))
  let hleft := intervalIntegral.integral_add_adjacent_intervals hlower hmiddle
  let hleft_integrable := hlower.trans hmiddle
  let hright := intervalIntegral.integral_add_adjacent_intervals hleft_integrable hupper
  congrArg (fun left : ℂ => left + ∫ y : ℝ in ρ..T, g y) hleft.symm ▸
    hright.symm ▸ rfl

/-- Helper: sum of three equations equals zero. -/
private lemma rightEndpointCapCollarBoundary_algebra_sum
    (lowerT upperT lowerChord upperChord pvLower pvUpper safeLower
      safeMiddle safeUpper arc : ℂ)
    (hlower : lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower = 0)
    (hupper : upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper = 0)
    (hhalf : lowerChord - upperChord - Complex.I * safeMiddle - arc = 0) :
    (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
        (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
          (lowerChord - upperChord - Complex.I * safeMiddle - arc) =
      0 :=
  (congrArg₂ (· + ·)
    (congrArg₂ (· + ·) hlower hupper)
    hhalf).trans ((add_zero (0 + 0 : ℂ)).trans (zero_add 0))

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
      lowerChord - upperChord - Complex.I * safeMiddle - arc = 0) :
    lowerT - upperT + Complex.I * (pvLower + pvUpper) -
        Complex.I * safe - arc =
      0 :=
  let hsum := rightEndpointCapCollarBoundary_algebra_sum
    lowerT upperT lowerChord upperChord pvLower pvUpper safeLower safeMiddle safeUpper arc
    hlower hupper hhalf
  let hcollected :=
    (Complex.rightEndpointCapCollarBoundary_collect
      lowerT upperT lowerChord upperChord pvLower pvUpper safeLower
      safeMiddle safeUpper arc).symm
  (Eq.subst
    (motive := fun safeTotal : ℂ =>
      lowerT - upperT + Complex.I * (pvLower + pvUpper) -
          Complex.I * safeTotal - arc =
        (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
          (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
            (lowerChord - upperChord - Complex.I * safeMiddle - arc))
    hsafe.symm
    hcollected).trans hsum

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
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :=
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
        (∀ y ∈ Set.Icc a b, y ∈ Set.Icc (-T) T) →
          IntervalIntegrable g volume a b := by
    intro a b hinterval_subset
    have hpath_cont :
        ContinuousOn
          (fun y : ℝ =>
            ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
          (Set.Icc a b) := by
      exact (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn
    have hpath_mem :
        ∀ y ∈ Set.Icc a b,
          ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)) ∈
            Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
      intro y hy
      have hM : M = N + 1 := rfl
      rw [hM] at hinterval_subset ⊢
      exact
        Complex.finiteAbelPlanaLogRightEndpointSafeVerticalPoint_mem_capCollar
          hρ (hinterval_subset y hy)
    have hg_cont :
        ContinuousOn g (Set.Icc a b) :=
      hcont.comp hpath_cont hpath_mem
    exact hg_cont.intervalIntegrable
  have hlower_interval :
      ∀ y ∈ Set.Icc (-T) (-ρ), y ∈ Set.Icc (-T) T :=
    Real.endpoint_lower_interval_subset_height hT hρ hρT
  have hmiddle_interval :
      ∀ y ∈ Set.Icc (-ρ) ρ, y ∈ Set.Icc (-T) T :=
    Real.endpoint_middle_interval_subset_height hρ hρT
  have hupper_interval :
      ∀ y ∈ Set.Icc ρ T, y ∈ Set.Icc (-T) T :=
    Real.endpoint_upper_interval_subset_height hT hρ hρT
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
                f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) :=
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
        (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
            f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
          -(∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
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
  unfold Complex.rightEndpointCapCollarOrientedBoundaryIntegral
  unfold M at hsafe_split
  unfold M at hlower_zero
  unfold M at hupper_zero
  unfold M at hhalf_zero
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
      hsafe_split
      hlower_zero
      hupper_zero
      hhalf_zero

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
    Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 :=
  let hρnonneg := le_of_lt hρ
  let hcont_right :=
    Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_rightEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hcont
  let hdiff_right :=
    Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_rightEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hdiff
  let hρT_valid :=
    Real.endpoint_radius_lt_height_of_lt_abs_height_half hT hdeleted_geometry.2.1
  (Complex.finiteAbelPlana_log_rightEndpointCapCollarOrientedBoundary_eq_generic
    N w T ρ) ▸
  Complex.rightEndpointCapCollarOrientedBoundaryIntegral_eq_zero
    (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
    N T hT hρ hρT_valid hcont_right hdiff_right

/-- Owner Cauchy-Goursat statement for the two endpoint semicollars, in
oriented-boundary form.

Both endpoints use their named oriented-boundary objects. -/

end

end LFunctions
end Boundary
