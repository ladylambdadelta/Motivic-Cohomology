import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircasePrevSafeGraph

/-!
# Cell-domain containment for right semicircle staircase rectangles

This file owns the deleted-collar membership proofs for staircase side pieces
and the closed/open Cauchy rectangles attached to one staircase cell.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators Topology Interval
open Filter MeasureTheory

/-- Graph-side criterion for membership in the deleted right half-collar. -/
theorem Complex.rightSemicircleGraphPoint_mem_core
    (c : ℂ)
    {ρ x y : ℝ}
    (hρ : 0 < ρ)
    (hx : x ∈ [[(0 : ℝ), ρ]])
    (hy : y ∈ [[-ρ, ρ]])
    (hgraph : Complex.rightSemicircleGraphRe ρ y ≤ x) :
    (((c.re + x : ℝ) : ℂ) + Complex.I * (((c.im + y : ℝ) : ℂ))) ∈
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  let z : ℂ :=
    (((c.re + x : ℝ) : ℂ) + Complex.I * (((c.im + y : ℝ) : ℂ)))
  have hx_bounds : 0 ≤ x ∧ x ≤ ρ := by
    exact Real.bounds_of_mem_uIcc hρ.le hx
  have hy_bounds : -ρ ≤ y ∧ y ≤ ρ := by
    exact
      Real.bounds_of_mem_uIcc
        (Complex.neg_radius_le_radius hρ.le)
        hy
  have hz_re : z.re = c.re + x := by
    exact Complex.ofReal_add_I_mul_ofReal_re (c.re + x) (c.im + y)
  have hz_im : z.im = c.im + y := by
    exact Complex.ofReal_add_I_mul_ofReal_im (c.re + x) (c.im + y)
  have hre_mem : z.re ∈ [[c.re, c.re + ρ]] := by
    have hleft : c.re ≤ c.re + x := by
      exact le_add_of_nonneg_right hx_bounds.1
    have hright : c.re + x ≤ c.re + ρ := by
      exact add_le_add_left hx_bounds.2 c.re
    have hz_left : c.re ≤ z.re := by
      calc
        c.re ≤ c.re + x := hleft
        _ = z.re := Eq.symm hz_re
    have hz_right : z.re ≤ c.re + ρ := by
      calc
        z.re = c.re + x := hz_re
        _ ≤ c.re + ρ := hright
    exact
      Real.mem_uIcc_of_bounds
        (le_add_of_nonneg_right hρ.le)
        (And.intro hz_left hz_right)
  have him_mem : z.im ∈ [[c.im - ρ, c.im + ρ]] := by
    have hleft : c.im - ρ ≤ c.im + y := by
      exact add_le_add_left hy_bounds.1 c.im
    have hright : c.im + y ≤ c.im + ρ := by
      exact add_le_add_left hy_bounds.2 c.im
    have hcenter_bounds : c.im - ρ ≤ c.im + ρ := by
      calc
        c.im - ρ = c.im + (-ρ) := rfl
        _ ≤ c.im + ρ :=
          add_le_add_left (Complex.neg_radius_le_radius hρ.le) c.im
    have hz_left : c.im - ρ ≤ z.im := by
      calc
        c.im - ρ ≤ c.im + y := hleft
        _ = z.im := Eq.symm hz_im
    have hz_right : z.im ≤ c.im + ρ := by
      calc
        z.im = c.im + y := hz_im
        _ ≤ c.im + ρ := hright
    exact
      Real.mem_uIcc_of_bounds hcenter_bounds
        (And.intro hz_left hz_right)
  have hx_shift : z.re - c.re ∈ [[(0 : ℝ), ρ]] := by
    have hshift : z.re - c.re = x := by
      calc
        z.re - c.re = (c.re + x) - c.re :=
          congrArg (fun r : ℝ => r - c.re) hz_re
        _ = x :=
          add_sub_cancel_left c.re x
    exact hshift.symm ▸ hx
  have hy_shift : z.im - c.im ∈ [[-ρ, ρ]] := by
    have hshift : z.im - c.im = y := by
      calc
        z.im - c.im = (c.im + y) - c.im :=
          congrArg (fun r : ℝ => r - c.im) hz_im
        _ = y :=
          add_sub_cancel_left c.im y
    exact hshift.symm ▸ hy
  have hgraph_shift :
      Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) ≤ z.re - c.re := by
    have hx_shift_eq : z.re - c.re = x := by
      calc
        z.re - c.re = (c.re + x) - c.re :=
          congrArg (fun r : ℝ => r - c.re) hz_re
        _ = x :=
          add_sub_cancel_left c.re x
    have hy_shift_eq : z.im - c.im = y := by
      calc
        z.im - c.im = (c.im + y) - c.im :=
          congrArg (fun r : ℝ => r - c.im) hz_im
        _ = y :=
          add_sub_cancel_left c.im y
    have hgraph_sqrt :
        Real.sqrt (ρ ^ 2 - y ^ 2) ≤ x :=
      Eq.mp
        (congrArg (fun r : ℝ => r ≤ x)
          (Complex.rightSemicircleGraphRe_eq_sqrt ρ y))
        hgraph
    exact
      Eq.mpr
        (congrArg₂
          (fun lhs rhs : ℝ => lhs ≤ rhs)
          (congrArg
            (fun t : ℝ => Real.sqrt (ρ ^ 2 - t ^ 2))
            hy_shift_eq)
          hx_shift_eq)
        hgraph_sqrt
  have hcircle :
      ρ ≤ Real.sqrt ((z.re - c.re) ^ 2 + (z.im - c.im) ^ 2) :=
    (Real.tangentBox_outside_circle_iff_graph_right
      hρ hx_shift hy_shift).mpr hgraph_shift
  have hnot_ball : z ∉ Metric.ball c ρ := by
    intro hball
    have hdist_lt : dist z c < ρ := by
      exact Metric.mem_ball.mp hball
    have hdist_ge : ρ ≤ dist z c := by
      exact
        (Complex.dist_eq_re_im z c).symm ▸ hcircle
    exact not_lt_of_ge hdist_ge hdist_lt
  exact ⟨⟨hre_mem, him_mem⟩, hnot_ball⟩

/-- Exterior staircase approximation to the inner right semicircle, oriented
from the bottom tangent point to the top tangent point. -/
noncomputable def Complex.rightSemicirclePolygonalArcIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  (∑ k in Finset.range (m + 1),
      (Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k +
        Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k)) +
    Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m

/-- A horizontal staircase connector lies in the deleted right-half-collar. -/
theorem Complex.rightSemicircleStaircaseHorizontal_subset_core
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    {x : ℝ}
    (hx :
      x ∈
        [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
          Complex.rightSemicircleStaircaseSafeRe ρ m k]]) :
    (((c.re + x : ℝ) : ℂ) +
      Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))) ∈
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  have hxprev :
      Complex.rightSemicircleStaircasePrevSafeRe ρ m k ∈ [[(0 : ℝ), ρ]] :=
    Complex.rightSemicircleStaircasePrevSafeRe_mem_Icc hρ.le m k hk
  have hxsafe :
      Complex.rightSemicircleStaircaseSafeRe ρ m k ∈ [[(0 : ℝ), ρ]] :=
    Complex.rightSemicircleStaircaseSafeRe_mem_Icc hρ.le m k hk
  have hx_bounds : x ∈ [[(0 : ℝ), ρ]] := by
    exact
      mem_uIcc_of_mem_uIcc_endpoints
        hρ.le hxprev hxsafe hx
  have hy_bounds :
      Complex.rightSemicircleStaircaseY ρ m k ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k
      (Complex.staircase_lower_sample_mem_range hk)
  have hgraph :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) ≤ x :=
    Complex.rightSemicircleStaircaseHorizontal_re_ge_graph hρ.le m k hk hx
  exact
    Complex.rightSemicircleGraphPoint_mem_core
      c hρ hx_bounds hy_bounds hgraph

/-- A vertical staircase side lies in the deleted right-half-collar. -/
theorem Complex.rightSemicircleStaircaseVertical_subset_core
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    {y : ℝ}
    (hy :
      y ∈
        [[Complex.rightSemicircleStaircaseY ρ m k,
          Complex.rightSemicircleStaircaseY ρ m (k + 1)]]) :
    (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
      Complex.I * (((c.im + y : ℝ) : ℂ))) ∈
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  have hx_bounds :
      Complex.rightSemicircleStaircaseSafeRe ρ m k ∈ [[(0 : ℝ), ρ]] :=
    Complex.rightSemicircleStaircaseSafeRe_mem_Icc hρ.le m k hk
  have hy0 :
      Complex.rightSemicircleStaircaseY ρ m k ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k
      (Complex.staircase_lower_sample_mem_range hk)
  have hy1 :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m (k + 1)
      (Complex.staircase_upper_sample_mem_range hk)
  have hy_bounds : y ∈ [[-ρ, ρ]] := by
    exact
      mem_uIcc_of_mem_uIcc_endpoints
        (Complex.neg_radius_le_radius hρ.le) hy0 hy1 hy
  have hgraph :
      Complex.rightSemicircleGraphRe ρ y ≤
        Complex.rightSemicircleStaircaseSafeRe ρ m k :=
    Complex.rightSemicircleStaircaseSafeRe_ge_graph_on_cell hρ.le m k hk hy
  exact
    Complex.rightSemicircleGraphPoint_mem_core
      c hρ hx_bounds hy_bounds hgraph

/-- The top staircase connector lies in the deleted right-half-collar. -/
theorem Complex.rightSemicircleStaircaseTopConnector_subset_core
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    {x : ℝ}
    (hx : x ∈ [[Complex.rightSemicircleStaircaseSafeRe ρ m m, 0]]) :
    (((c.re + x : ℝ) : ℂ) +
      Complex.I * (((c.im + ρ : ℝ) : ℂ))) ∈
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  have hx_safe :
      Complex.rightSemicircleStaircaseSafeRe ρ m m ∈ [[(0 : ℝ), ρ]] :=
    Complex.rightSemicircleStaircaseSafeRe_last_mem_Icc hρ.le m
  have hx_bounds : x ∈ [[(0 : ℝ), ρ]] := by
    have hzero : (0 : ℝ) ∈ [[(0 : ℝ), ρ]] :=
      Complex.zero_mem_radius_uIcc hρ.le
    exact
      mem_uIcc_of_mem_uIcc_endpoints
        hρ.le hx_safe hzero hx
  have hy_bounds : ρ ∈ [[-ρ, ρ]] := by
    exact Complex.radius_mem_semicircle_height_uIcc hρ.le
  have hgraph : Complex.rightSemicircleGraphRe ρ ρ ≤ x := by
    have hgraph_zero : Complex.rightSemicircleGraphRe ρ ρ = 0 := by
      exact Complex.rightSemicircleGraphRe_top
    have hx_nonneg : 0 ≤ x := by
      have hxbounds : 0 ≤ x ∧ x ≤ ρ := by
        exact Real.bounds_of_mem_uIcc hρ.le hx_bounds
      exact hxbounds.1
    calc
      Complex.rightSemicircleGraphRe ρ ρ = 0 := hgraph_zero
      _ ≤ x := hx_nonneg
  exact
    Complex.rightSemicircleGraphPoint_mem_core
      c hρ hx_bounds hy_bounds hgraph

/-- Polygonal half-collar boundary with the fixed outer sides and a safe
exterior staircase approximation to the circular side. -/
noncomputable def Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  (∫ x : ℝ in c.re..(c.re + ρ),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
    (∫ x : ℝ in c.re..(c.re + ρ),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
      Complex.I *
        (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
              f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        Complex.rightSemicirclePolygonalArcIntegral f c ρ m

/-- The explicit lower-left Cauchy corner for one staircase cell. -/
noncomputable def Complex.rightSemicircleStaircaseCellLowerCorner
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) : ℂ :=
  (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
    Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))

/-- The explicit upper-right Cauchy corner for one staircase cell. -/
noncomputable def Complex.rightSemicircleStaircaseCellUpperCorner
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) : ℂ :=
  (((c.re + ρ : ℝ) : ℂ) +
    Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))

/-- Real coordinate of the lower-left Cauchy corner. -/
theorem Complex.rightSemicircleStaircaseCellLowerCorner_re
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re =
      c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  exact
    Complex.ofReal_add_I_mul_ofReal_re
      (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)
      (c.im + Complex.rightSemicircleStaircaseY ρ m k)

/-- Imaginary coordinate of the lower-left Cauchy corner. -/
theorem Complex.rightSemicircleStaircaseCellLowerCorner_im
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im =
      c.im + Complex.rightSemicircleStaircaseY ρ m k := by
  exact
    Complex.ofReal_add_I_mul_ofReal_im
      (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)
      (c.im + Complex.rightSemicircleStaircaseY ρ m k)

/-- Real coordinate of the upper-right Cauchy corner. -/
theorem Complex.rightSemicircleStaircaseCellUpperCorner_re
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re =
      c.re + ρ := by
  exact
    Complex.ofReal_add_I_mul_ofReal_re
      (c.re + ρ)
      (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1))

/-- Imaginary coordinate of the upper-right Cauchy corner. -/
theorem Complex.rightSemicircleStaircaseCellUpperCorner_im
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im =
      c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) := by
  exact
    Complex.ofReal_add_I_mul_ofReal_im
      (c.re + ρ)
      (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1))

/-- Boundary integral of one rectangular strip in the staircase exhaustion. -/
noncomputable def Complex.rightSemicircleStaircaseCellBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) : ℂ :=
  let z₀ : ℂ := Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k
  let z₁ : ℂ := Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k
  (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
      (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
        Complex.I •
          (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
          Complex.I •
            (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I))

/-- A coordinate in the translated safe-radius interval has shifted coordinate
in `[0, ρ]`. -/
theorem Complex.sub_re_mem_radius_uIcc_of_mem_safe_radius_box
    {c s ρ z : ℝ}
    (hρ : 0 ≤ ρ)
    (hs : 0 ≤ s ∧ s ≤ ρ)
    (hz : z ∈ [[c + s, c + ρ]]) :
    z - c ∈ [[(0 : ℝ), ρ]] :=
  match Set.mem_uIcc.mp hz with
  | Or.inl hz_pair =>
      let hleft : 0 ≤ z - c :=
        sub_nonneg.mpr
          (le_trans (le_add_of_nonneg_right hs.1) hz_pair.1)
      let hright : z - c ≤ ρ :=
        calc
          z - c ≤ (c + ρ) - c :=
            sub_le_sub_right hz_pair.2 c
          _ = ρ :=
            add_sub_cancel_left c ρ
      Real.mem_uIcc_of_bounds hρ (And.intro hleft hright)
  | Or.inr hz_pair =>
      let hleft : 0 ≤ z - c :=
        sub_nonneg.mpr
          (le_trans (le_add_of_nonneg_right hρ) hz_pair.1)
      let hright : z - c ≤ ρ :=
        calc
          z - c ≤ (c + s) - c :=
            sub_le_sub_right hz_pair.2 c
          _ = s :=
            add_sub_cancel_left c s
          _ ≤ ρ :=
            hs.2
      Real.mem_uIcc_of_bounds hρ (And.intro hleft hright)

/-- A coordinate in the translated safe-radius interval is at least the safe
coordinate after shifting by the center. -/
theorem Complex.safe_le_sub_re_of_mem_safe_radius_box
    {c s ρ z : ℝ}
    (_hρ : 0 ≤ ρ)
    (hs : 0 ≤ s ∧ s ≤ ρ)
    (hz : z ∈ [[c + s, c + ρ]]) :
    s ≤ z - c :=
  match Set.mem_uIcc.mp hz with
  | Or.inl hz_pair =>
      calc
        s = (c + s) - c :=
          Eq.symm (add_sub_cancel_left c s)
        _ ≤ z - c :=
          sub_le_sub_right hz_pair.1 c
  | Or.inr hz_pair =>
      calc
        s ≤ ρ :=
          hs.2
        _ = (c + ρ) - c :=
          Eq.symm (add_sub_cancel_left c ρ)
        _ ≤ z - c :=
          sub_le_sub_right hz_pair.1 c

/-- A point in a translated unordered interval remains in the original
unordered interval after subtracting the translation. -/
theorem Complex.sub_im_mem_uIcc_of_mem_translated_uIcc
    {c a b z : ℝ}
    (hz : z ∈ [[c + a, c + b]]) :
    z - c ∈ [[a, b]] :=
  match Set.mem_uIcc.mp hz with
  | Or.inl hz_pair =>
      let hleft : a ≤ z - c :=
        calc
          a = (c + a) - c :=
            Eq.symm (add_sub_cancel_left c a)
          _ ≤ z - c :=
            sub_le_sub_right hz_pair.1 c
      let hright : z - c ≤ b :=
        calc
          z - c ≤ (c + b) - c :=
            sub_le_sub_right hz_pair.2 c
          _ = b :=
            add_sub_cancel_left c b
      Set.mem_uIcc.mpr (Or.inl (And.intro hleft hright))
  | Or.inr hz_pair =>
      let hleft : b ≤ z - c :=
        calc
          b = (c + b) - c :=
            Eq.symm (add_sub_cancel_left c b)
          _ ≤ z - c :=
            sub_le_sub_right hz_pair.1 c
      let hright : z - c ≤ a :=
        calc
          z - c ≤ (c + a) - c :=
            sub_le_sub_right hz_pair.2 c
          _ = a :=
            add_sub_cancel_left c a
      Set.mem_uIcc.mpr (Or.inr (And.intro hleft hright))

/-- The closed rectangle of one staircase strip lies in the deleted
right-half-collar. -/
theorem Complex.rightSemicircleStaircaseCellRectangle_subset_core
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1)) :
    ([[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]] ×ℂ
        [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
          c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]]) ⊆
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  intro z hz
  have hzdata := Complex.mem_reProdIm.mp hz
  let x : ℝ := z.re - c.re
  let y : ℝ := z.im - c.im
  have hx_def : x = z.re - c.re := rfl
  have hy_def : y = z.im - c.im := rfl
  have hz_eq :
      z = (((c.re + x : ℝ) : ℂ) + Complex.I * (((c.im + y : ℝ) : ℂ))) := by
    exact
      Complex.ext
        (calc
        z.re =
            (((c.re + x : ℝ) : ℂ) +
              Complex.I * (((c.im + y : ℝ) : ℂ))).re := by
          exact
            Eq.symm
              (calc
                (((c.re + x : ℝ) : ℂ) +
                  Complex.I * (((c.im + y : ℝ) : ℂ))).re =
                    c.re + x :=
                  Complex.ofReal_add_I_mul_ofReal_re
                    (c.re + x) (c.im + y)
                _ = c.re + (z.re - c.re) := by
                  exact congrArg (fun u : ℝ => c.re + u) hx_def
                _ = (z.re - c.re) + c.re := add_comm c.re (z.re - c.re)
                _ = z.re := sub_add_cancel z.re c.re)
        )
        (calc
        z.im =
            (((c.re + x : ℝ) : ℂ) +
              Complex.I * (((c.im + y : ℝ) : ℂ))).im := by
          exact
            Eq.symm
              (calc
                (((c.re + x : ℝ) : ℂ) +
                  Complex.I * (((c.im + y : ℝ) : ℂ))).im =
                    c.im + y :=
                  Complex.ofReal_add_I_mul_ofReal_im
                    (c.re + x) (c.im + y)
                _ = c.im + (z.im - c.im) := by
                  exact congrArg (fun u : ℝ => c.im + u) hy_def
                _ = (z.im - c.im) + c.im := add_comm c.im (z.im - c.im)
                _ = z.im := sub_add_cancel z.im c.im)
        )
  have hsafe_bounds :
      Complex.rightSemicircleStaircaseSafeRe ρ m k ∈ [[(0 : ℝ), ρ]] :=
    Complex.rightSemicircleStaircaseSafeRe_mem_Icc hρ.le m k hk
  have hsafe_pair : 0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m k ∧
      Complex.rightSemicircleStaircaseSafeRe ρ m k ≤ ρ := by
    exact Real.bounds_of_mem_uIcc hρ.le hsafe_bounds
  have hx_bounds : x ∈ [[(0 : ℝ), ρ]] :=
    Complex.sub_re_mem_radius_uIcc_of_mem_safe_radius_box
      hρ.le hsafe_pair hzdata.1
  have hy_cell :
      y ∈ [[Complex.rightSemicircleStaircaseY ρ m k,
        Complex.rightSemicircleStaircaseY ρ m (k + 1)]] :=
    Complex.sub_im_mem_uIcc_of_mem_translated_uIcc hzdata.2
  have hy_bounds : y ∈ [[-ρ, ρ]] := by
    have hk0 : k ∈ Finset.range (m + 2) := by
      exact Complex.staircase_lower_sample_mem_range hk
    have hk1 : k + 1 ∈ Finset.range (m + 2) := by
      exact Complex.staircase_upper_sample_mem_range hk
    have hy0 :=
      Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k hk0
    have hy1 :=
      Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m (k + 1) hk1
    exact
      mem_uIcc_of_mem_uIcc_endpoints
        (Complex.neg_radius_le_radius hρ.le) hy0 hy1 hy_cell
  have hgraph_safe :
      Complex.rightSemicircleGraphRe ρ y ≤
        Complex.rightSemicircleStaircaseSafeRe ρ m k :=
    Complex.rightSemicircleStaircaseSafeRe_ge_graph_on_cell
      hρ.le m k hk hy_cell
  have hx_safe : Complex.rightSemicircleStaircaseSafeRe ρ m k ≤ x :=
    Complex.safe_le_sub_re_of_mem_safe_radius_box
      hρ.le hsafe_pair hzdata.1
  have hgraph : Complex.rightSemicircleGraphRe ρ y ≤ x :=
    le_trans hgraph_safe hx_safe
  exact
    hz_eq.symm ▸
      (Complex.rightSemicircleGraphPoint_mem_core
        c hρ hx_bounds hy_bounds hgraph)

end

end LFunctions
end Boundary
