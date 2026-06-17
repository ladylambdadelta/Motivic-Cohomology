import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseIntegrability

/-!
# Cauchy cancellation on right semicircle staircase cells

This file owns the rectangular Cauchy-Goursat cancellation for one cell in the
finite right-semicircle staircase decomposition.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- Coordinate transport from the Cauchy-corner rectangle to the explicit
staircase cell rectangle. -/
theorem Complex.mem_explicitCellRectangle_of_mem_cauchyCellRectangle
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ)
    {z : ℂ}
    (hz :
      z ∈
        ([[((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re),
          ((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re)]] ×ℂ
          [[((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im),
            ((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im)]])) :
    z ∈
      ([[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]] ×ℂ
        [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
          c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]]) := by
  have hzdata := Complex.mem_reProdIm.mp hz
  have hre_set :
      [[((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re),
        ((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re)]] =
        [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]] := by
    exact
      congrArg₂
        (fun a b : ℝ => [[a, b]])
        (Complex.rightSemicircleStaircaseCellLowerCorner_re c ρ m k)
        (Complex.rightSemicircleStaircaseCellUpperCorner_re c ρ m k)
  have him_set :
      [[((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im),
        ((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im)]] =
        [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
          c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]] := by
    exact
      congrArg₂
        (fun a b : ℝ => [[a, b]])
        (Complex.rightSemicircleStaircaseCellLowerCorner_im c ρ m k)
        (Complex.rightSemicircleStaircaseCellUpperCorner_im c ρ m k)
  have hre_mem :
      z.re ∈
        [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]] :=
    Eq.mp (congrArg (fun s : Set ℝ => z.re ∈ s) hre_set) hzdata.1
  have him_mem :
      z.im ∈
        [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
          c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]] :=
    Eq.mp (congrArg (fun s : Set ℝ => z.im ∈ s) him_set) hzdata.2
  exact Complex.mem_reProdIm.mpr ⟨hre_mem, him_mem⟩

/-- The Cauchy rectangle attached to one staircase cell lies in the deleted
right-half-collar. -/
theorem Complex.rightSemicircleStaircaseCellCauchyRectangle_subset_core
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1)) :
    let z₀ : ℂ := Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k
    let z₁ : ℂ := Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k
    ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  show
    ([[((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re),
      ((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re)]] ×ℂ
      [[((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im),
        ((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im)]]) ⊆
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ
  intro z hz
  have hexplicit :
      z ∈
        ([[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]] ×ℂ
          [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
            c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]]) :=
    Complex.mem_explicitCellRectangle_of_mem_cauchyCellRectangle c ρ m k hz
  exact
    Complex.rightSemicircleStaircaseCellRectangle_subset_core
      c hρ m k hk hexplicit

/-- A point in the open Cauchy rectangle is in the corresponding closed
Cauchy rectangle. -/
theorem Complex.mem_cauchyCellRectangle_of_mem_openCauchyCellRectangle
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ)
    {z : ℂ}
    (hz :
      z ∈
        (Set.Ioo
            (min (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re
              (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re)
            (max (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re
              (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re) ×ℂ
          Set.Ioo
            (min (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im
              (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im)
            (max (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im
              (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im))) :
    z ∈
      ([[((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re),
        ((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re)]] ×ℂ
        [[((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im),
          ((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im)]]) := by
  have hzdata := Complex.mem_reProdIm.mp hz
  exact
    Complex.mem_reProdIm.mpr
      ⟨Set.Ioo_subset_Icc_self hzdata.1,
        Set.Ioo_subset_Icc_self hzdata.2⟩

/-- The open Cauchy rectangle attached to one staircase cell lies in the
deleted right-half-collar. -/
theorem Complex.rightSemicircleStaircaseCellCauchyOpenRectangle_subset_core
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1)) :
    let z₀ : ℂ := Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k
    let z₁ : ℂ := Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k
    (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
        Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  show
    (Set.Ioo
        (min (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re
          (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re)
        (max (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re
          (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re) ×ℂ
      Set.Ioo
        (min (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im
          (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im)
        (max (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im
          (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im)) ⊆
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ
  intro z hz
  have hclosed :
      z ∈
        ([[((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re),
          ((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re)]] ×ℂ
          [[((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im),
            ((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im)]]) :=
    Complex.mem_cauchyCellRectangle_of_mem_openCauchyCellRectangle c ρ m k hz
  exact
    Complex.rightSemicircleStaircaseCellCauchyRectangle_subset_core
      c hρ m k hk hclosed

end

end LFunctions
end Boundary
