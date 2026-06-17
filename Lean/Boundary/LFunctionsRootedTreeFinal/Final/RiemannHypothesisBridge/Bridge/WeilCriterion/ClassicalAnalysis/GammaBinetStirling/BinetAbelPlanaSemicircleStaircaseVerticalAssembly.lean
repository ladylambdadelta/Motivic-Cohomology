import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseHorizontalAssembly

/-!
# Vertical assembly for semicircle staircase cells

This file owns the finite vertical-side concatenation identities used by the
staircase geometry assembly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- Endpoint-transport wrapper for summing adjacent interval integrals along a
finite chain. -/
theorem Complex.integral_eq_sum_adjacent_intervals_of_endpoint_chain
    (F : ℝ → ℂ)
    (a : ℕ → ℝ)
    (n : ℕ)
    (A B : ℝ)
    (hA : a 0 = A)
    (hB : a n = B)
    (hint : ∀ k < n, IntervalIntegrable F volume (a k) (a (k + 1))) :
    (∫ y : ℝ in A..B, F y) =
      ∑ k in Finset.range n, ∫ y : ℝ in a k..a (k + 1), F y := by
  have hsum :
      (∑ k in Finset.range n, ∫ y : ℝ in a k..a (k + 1), F y) =
        ∫ y : ℝ in (a 0)..(a n), F y := by
    exact
      intervalIntegral.sum_integral_adjacent_intervals
        (μ := volume)
        (f := F)
        (a := a)
        (n := n)
        hint
  have htarget :
      (∫ y : ℝ in (a 0)..(a n), F y) =
        ∫ y : ℝ in A..B, F y := by
    exact
      congrArg₂
        (fun s t : ℝ => ∫ y : ℝ in s..t, F y)
        hA
        hB
  exact Eq.symm (Eq.trans hsum htarget)

/-- Outer vertical sides of the staircase-cell rectangles concatenate to the
outer vertical side of the half-collar. -/
theorem Complex.sum_rightSemicircleStaircaseCellOuterVertical_eq_outerVertical
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    (∑ k in Finset.range (m + 1),
        ∫ y : ℝ in
          (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
            (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
          f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
      ∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)) := by
  let F : ℝ → ℂ := fun y =>
    f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))
  let a : ℕ → ℝ := fun k =>
    c.im + Complex.rightSemicircleStaircaseY ρ m k
  have hF_def :
      F =
        fun y : ℝ =>
          f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)) := rfl
  have ha_def :
      a =
        fun k : ℕ =>
          c.im + Complex.rightSemicircleStaircaseY ρ m k := rfl
  have hA : a 0 = c.im - ρ := by
    exact congrFun ha_def 0 ▸
      Complex.rightSemicircleStaircaseY_zero_add_im c ρ m
  have hB : a (m + 1) = c.im + ρ := by
    exact congrFun ha_def (m + 1) ▸
      Complex.rightSemicircleStaircaseY_last_add_im c ρ m
  have hint :
      ∀ k < m + 1, IntervalIntegrable F volume (a k) (a (k + 1)) := by
    intro k hk
    have hkrange : k ∈ Finset.range (m + 1) := by
      exact Finset.mem_range.mpr hk
    have hraw :
        IntervalIntegrable
          (fun y : ℝ =>
            f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
          volume
          (c.im + Complex.rightSemicircleStaircaseY ρ m k)
          (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)) :=
      Complex.intervalIntegrable_rightSemicircleStaircaseCellOuterVertical
        f c hρ m k hkrange hcont
    exact hF_def.symm ▸ ha_def.symm ▸ hraw
  exact
    (Complex.integral_eq_sum_adjacent_intervals_of_endpoint_chain
      F a (m + 1) (c.im - ρ) (c.im + ρ) hA hB hint).symm

/-- Inner vertical sides of the staircase-cell rectangles are exactly the
vertical part of the staircase arc integral. -/
theorem Complex.sum_rightSemicircleStaircaseCellInnerVertical_eq_verticalArc
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    (∑ k in Finset.range (m + 1),
        Complex.I *
          (∫ y : ℝ in
            (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
              (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
            f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
              Complex.I * (y : ℂ)))) =
      ∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k := by
  apply Finset.sum_congr rfl
  intro k _hk
  let G : ℝ → ℂ := fun y =>
    f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
      Complex.I * (y : ℂ))
  have hcomm_integrand :
      (∫ y : ℝ in
          Complex.rightSemicircleStaircaseY ρ m k..
            Complex.rightSemicircleStaircaseY ρ m (k + 1),
          G (c.im + y)) =
        ∫ y : ℝ in
          Complex.rightSemicircleStaircaseY ρ m k..
            Complex.rightSemicircleStaircaseY ρ m (k + 1),
          G (y + c.im) := by
    exact
      intervalIntegral.integral_congr
        (fun y _hy =>
          congrArg G (add_comm c.im y))
  have htranslate :
      (∫ y : ℝ in
          Complex.rightSemicircleStaircaseY ρ m k..
            Complex.rightSemicircleStaircaseY ρ m (k + 1),
          G (y + c.im)) =
        ∫ y : ℝ in
          (Complex.rightSemicircleStaircaseY ρ m k + c.im)..
            (Complex.rightSemicircleStaircaseY ρ m (k + 1) + c.im),
          G y := by
    exact
      intervalIntegral.integral_comp_add_right
        (f := G)
        (a := Complex.rightSemicircleStaircaseY ρ m k)
        (b := Complex.rightSemicircleStaircaseY ρ m (k + 1))
        c.im
  have hbounds :
      (∫ y : ℝ in
        (Complex.rightSemicircleStaircaseY ρ m k + c.im)..
          (Complex.rightSemicircleStaircaseY ρ m (k + 1) + c.im),
        G y) =
      ∫ y : ℝ in
        (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
          (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
        G y := by
    exact
      congrArg₂
        (fun a b : ℝ => ∫ y : ℝ in a..b, G y)
        (add_comm (Complex.rightSemicircleStaircaseY ρ m k) c.im)
        (add_comm (Complex.rightSemicircleStaircaseY ρ m (k + 1)) c.im)
  have hrelative_to_absolute :
      (∫ y : ℝ in
          Complex.rightSemicircleStaircaseY ρ m k..
            Complex.rightSemicircleStaircaseY ρ m (k + 1),
          G (c.im + y)) =
        ∫ y : ℝ in
          (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
            (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
          G y :=
    Eq.trans hcomm_integrand (Eq.trans htranslate hbounds)
  show
    Complex.I *
      (∫ y : ℝ in
        (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
          (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
        G y) =
      Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k
  exact
    Eq.symm
      (congrArg (fun z : ℂ => Complex.I * z)
        hrelative_to_absolute)

end

end LFunctions
end Boundary
