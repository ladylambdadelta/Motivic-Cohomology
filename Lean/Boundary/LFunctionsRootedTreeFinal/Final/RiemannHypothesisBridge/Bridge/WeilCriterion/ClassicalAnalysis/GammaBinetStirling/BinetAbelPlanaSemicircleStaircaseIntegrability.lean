import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseEndpoints

/-!
# Interval-integrability for right semicircle staircase sides

This file owns the continuity-to-interval-integrability transport for the
straight sides of the finite staircase cell decomposition.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- The closed rectangle of a staircase cell, written with the explicit lower
left and upper right corners used by the integrability lemmas, lies in the
deleted right-half-collar. -/
theorem Complex.rightSemicircleStaircaseCellExplicitRectangle_subset_core
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1)) :
    ([[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]] ×ℂ
        [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
          c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]]) ⊆
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  exact
    Complex.rightSemicircleStaircaseCellRectangle_subset_core
      c hρ m k hk

/-- Horizontal staircase connectors are interval-integrable under continuity on
the deleted collar. -/
theorem Complex.intervalIntegrable_rightSemicircleStaircaseHorizontal
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun x : ℝ =>
        f (((c.re + x : ℝ) : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
      volume
      (Complex.rightSemicircleStaircasePrevSafeRe ρ m k)
      (Complex.rightSemicircleStaircaseSafeRe ρ m k) := by
  have hmaps :
      Set.MapsTo
        (fun x : ℝ =>
          (((c.re + x : ℝ) : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
        [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
          Complex.rightSemicircleStaircaseSafeRe ρ m k]]
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro x hx
    exact
      Complex.rightSemicircleStaircaseHorizontal_subset_core
        c hρ m k hk hx
  have hparam :
      ContinuousOn
        (fun x : ℝ =>
          (((c.re + x : ℝ) : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
        [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
          Complex.rightSemicircleStaircaseSafeRe ρ m k]] := by
    exact
      ((Complex.continuous_ofReal.comp
          (continuous_const.add continuous_id)).add
        (continuous_const.mul continuous_const)).continuousOn
  exact (ContinuousOn.comp hcont hparam hmaps).intervalIntegrable

/-- Vertical staircase sides are interval-integrable under continuity on the
deleted collar. -/
theorem Complex.intervalIntegrable_rightSemicircleStaircaseVertical
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun y : ℝ =>
        f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
          Complex.I * (((c.im + y : ℝ) : ℂ))))
      volume
      (Complex.rightSemicircleStaircaseY ρ m k)
      (Complex.rightSemicircleStaircaseY ρ m (k + 1)) := by
  have hmaps :
      Set.MapsTo
        (fun y : ℝ =>
          (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
            Complex.I * (((c.im + y : ℝ) : ℂ))))
        [[Complex.rightSemicircleStaircaseY ρ m k,
          Complex.rightSemicircleStaircaseY ρ m (k + 1)]]
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro y hy
    exact
      Complex.rightSemicircleStaircaseVertical_subset_core
        c hρ m k hk hy
  have hparam :
      ContinuousOn
        (fun y : ℝ =>
          (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
            Complex.I * (((c.im + y : ℝ) : ℂ))))
        [[Complex.rightSemicircleStaircaseY ρ m k,
          Complex.rightSemicircleStaircaseY ρ m (k + 1)]] := by
    exact
      (continuous_const.add
        (continuous_const.mul
          (Complex.continuous_ofReal.comp
            (continuous_const.add continuous_id)))).continuousOn
  exact (ContinuousOn.comp hcont hparam hmaps).intervalIntegrable

/-- The final top connector is interval-integrable under continuity on the
deleted collar. -/
theorem Complex.intervalIntegrable_rightSemicircleStaircaseTopConnector
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun x : ℝ =>
        f (((c.re + x : ℝ) : ℂ) +
          Complex.I * (((c.im + ρ : ℝ) : ℂ))))
      volume
      (Complex.rightSemicircleStaircaseSafeRe ρ m m)
      0 := by
  have hmaps :
      Set.MapsTo
        (fun x : ℝ =>
          (((c.re + x : ℝ) : ℂ) +
            Complex.I * (((c.im + ρ : ℝ) : ℂ))))
        [[Complex.rightSemicircleStaircaseSafeRe ρ m m, 0]]
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro x hx
    exact
      Complex.rightSemicircleStaircaseTopConnector_subset_core
        c hρ m hx
  have hparam :
      ContinuousOn
        (fun x : ℝ =>
          (((c.re + x : ℝ) : ℂ) +
            Complex.I * (((c.im + ρ : ℝ) : ℂ))))
        [[Complex.rightSemicircleStaircaseSafeRe ρ m m, 0]] := by
    exact
      ((Complex.continuous_ofReal.comp
          (continuous_const.add continuous_id)).add
        (continuous_const.mul continuous_const)).continuousOn
  exact (ContinuousOn.comp hcont hparam hmaps).intervalIntegrable

/-- Bottom right-tail side of a staircase cell is interval-integrable. -/
theorem Complex.intervalIntegrable_rightSemicircleStaircaseCellBottomTail
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun x : ℝ =>
        f ((x : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
      volume
      (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)
      (c.re + ρ) := by
  have hrect :
      ([[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]] ×ℂ
        [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
          c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]]) ⊆
        Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
    exact
      Complex.rightSemicircleStaircaseCellExplicitRectangle_subset_core
        c hρ m k hk
  have hmaps :
      Set.MapsTo
        (fun x : ℝ =>
          ((x : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
        [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]]
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro x hx
    let z : ℂ :=
      ((x : ℂ) +
        Complex.I *
          (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))
    have hzre : z.re = x := by
      exact
        Complex.ofReal_add_I_mul_ofReal_re
          x (c.im + Complex.rightSemicircleStaircaseY ρ m k)
    have hzim :
        z.im = c.im + Complex.rightSemicircleStaircaseY ρ m k := by
      exact
        Complex.ofReal_add_I_mul_ofReal_im
          x (c.im + Complex.rightSemicircleStaircaseY ρ m k)
    have hre_mem :
        z.re ∈
          [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k,
            c.re + ρ]] :=
      Eq.mp
        (congrArg
          (fun r : ℝ =>
            r ∈
              [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k,
                c.re + ρ]])
          (Eq.symm hzre))
        hx
    have him_mem :
        z.im ∈
          [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
            c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]] :=
      Eq.mp
        (congrArg
          (fun r : ℝ =>
            r ∈
              [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
                c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]])
          (Eq.symm hzim))
        Set.left_mem_uIcc
    show z ∈ Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ
    exact hrect (Complex.mem_reProdIm.mpr ⟨hre_mem, him_mem⟩)
  have hparam :
      ContinuousOn
        (fun x : ℝ =>
          ((x : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
        [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]] := by
    exact (Complex.continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
  exact (ContinuousOn.comp hcont hparam hmaps).intervalIntegrable

/-- Top right-tail side of a staircase cell is interval-integrable. -/
theorem Complex.intervalIntegrable_rightSemicircleStaircaseCellTopTail
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun x : ℝ =>
        f ((x : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ))))
      volume
      (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)
      (c.re + ρ) := by
  have hrect :
      ([[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]] ×ℂ
        [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
          c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]]) ⊆
        Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
    exact
      Complex.rightSemicircleStaircaseCellExplicitRectangle_subset_core
        c hρ m k hk
  have hmaps :
      Set.MapsTo
        (fun x : ℝ =>
          ((x : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ))))
        [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]]
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro x hx
    let z : ℂ :=
      ((x : ℂ) +
        Complex.I *
          (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))
    have hzre : z.re = x := by
      exact
        Complex.ofReal_add_I_mul_ofReal_re
          x (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1))
    have hzim :
        z.im = c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) := by
      exact
        Complex.ofReal_add_I_mul_ofReal_im
          x (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1))
    have hre_mem :
        z.re ∈
          [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k,
            c.re + ρ]] :=
      Eq.mp
        (congrArg
          (fun r : ℝ =>
            r ∈
              [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k,
                c.re + ρ]])
          (Eq.symm hzre))
        hx
    have him_mem :
        z.im ∈
          [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
            c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]] :=
      Eq.mp
        (congrArg
          (fun r : ℝ =>
            r ∈
              [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
                c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]])
          (Eq.symm hzim))
        Set.right_mem_uIcc
    show z ∈ Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ
    exact hrect (Complex.mem_reProdIm.mpr ⟨hre_mem, him_mem⟩)
  have hparam :
      ContinuousOn
        (fun x : ℝ =>
          ((x : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ))))
        [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]] := by
    exact (Complex.continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
  exact (ContinuousOn.comp hcont hparam hmaps).intervalIntegrable

/-- Outer vertical side of a staircase cell is interval-integrable. -/
theorem Complex.intervalIntegrable_rightSemicircleStaircaseCellOuterVertical
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun y : ℝ =>
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
      volume
      (c.im + Complex.rightSemicircleStaircaseY ρ m k)
      (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)) := by
  have hrect :
      ([[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]] ×ℂ
        [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
          c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]]) ⊆
        Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
    exact
      Complex.rightSemicircleStaircaseCellExplicitRectangle_subset_core
        c hρ m k hk
  have hmaps :
      Set.MapsTo
        (fun y : ℝ =>
          (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
          c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]]
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro y hy
    let z : ℂ :=
      (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))
    have hzre : z.re = c.re + ρ := by
      exact Complex.ofReal_add_I_mul_ofReal_re (c.re + ρ) y
    have hzim : z.im = y := by
      exact Complex.ofReal_add_I_mul_ofReal_im (c.re + ρ) y
    have hre_mem :
        z.re ∈
          [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k,
            c.re + ρ]] :=
      Eq.mp
        (congrArg
          (fun r : ℝ =>
            r ∈
              [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k,
                c.re + ρ]])
          (Eq.symm hzre))
        Set.right_mem_uIcc
    have him_mem :
        z.im ∈
          [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
            c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]] :=
      Eq.mp
        (congrArg
          (fun r : ℝ =>
            r ∈
              [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
                c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]])
          (Eq.symm hzim))
        hy
    show z ∈ Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ
    exact hrect (Complex.mem_reProdIm.mpr ⟨hre_mem, him_mem⟩)
  have hparam :
      ContinuousOn
        (fun y : ℝ =>
          (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
          c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]] := by
    exact (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn
  exact (ContinuousOn.comp hcont hparam hmaps).intervalIntegrable

end

end LFunctions
end Boundary
