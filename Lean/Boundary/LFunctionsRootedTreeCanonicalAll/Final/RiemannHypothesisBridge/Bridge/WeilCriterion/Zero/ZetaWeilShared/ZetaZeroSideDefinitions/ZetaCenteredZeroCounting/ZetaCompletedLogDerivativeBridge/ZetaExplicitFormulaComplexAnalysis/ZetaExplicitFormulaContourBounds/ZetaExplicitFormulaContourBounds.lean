import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaGeometry.ZetaExplicitFormulaGeometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Boundary explicit-formula contour bounds

This file owns the generic interval-integral estimate and the contour-path
shift/strip lemmas. The analytic complex-analysis file consumes these results
as reusable geometry/analysis infrastructure.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The complex number `1 / 2` is the coercion of the real number `1 / 2`. -/
theorem complex_half_eq_ofReal_half :
    (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) :=
  (Complex.ofReal_div (1 : ℝ) (2 : ℝ)).symm

/-- The real part of the complex number `1 / 2` is `1 / 2`. -/
theorem complex_half_re :
    ((1 / 2 : ℂ).re) = (1 / 2 : ℝ) :=
  Eq.trans
    (congrArg Complex.re complex_half_eq_ofReal_half)
    (Complex.ofReal_re (1 / 2 : ℝ))

/-- Membership in `Ι a b` is membership in `Ioc a b` when `a ≤ b`. -/
theorem mem_Ioc_of_mem_uIoc_of_le {a b x : ℝ} (hab : a ≤ b)
    (hx : x ∈ Ι a b) :
    x ∈ Set.Ioc a b :=
  Eq.mp (congrArg (fun s : Set ℝ => x ∈ s) (Set.uIoc_of_le hab)) hx

/-- When `a ≤ b`, the unordered interval `Ι a b` lies in the closed interval `Icc a b`. -/
theorem uIoc_subset_Icc_of_le {a b : ℝ} (hab : a ≤ b) :
    Ι a b ⊆ Set.Icc a b := by
  intro x hx
  exact Set.Ioc_subset_Icc_self (mem_Ioc_of_mem_uIoc_of_le hab hx)

/-- A pointwise bound on `Icc a b` gives the same bound on `Ι a b` when `a ≤ b`. -/
theorem pointwise_bound_on_uIoc_of_bound_on_Icc
    {g : ℝ → ℂ} {a b C : ℝ} (hab : a ≤ b)
    (hg : ∀ x ∈ Set.Icc a b, ‖g x‖ ≤ C) :
    ∀ x ∈ Ι a b, ‖g x‖ ≤ C :=
  fun x hx => hg x (uIoc_subset_Icc_of_le hab hx)

/-- Mathlib's unordered-interval norm bound in the notation used by the contour estimates. -/
theorem intervalIntegral_norm_le_constant_abs
    (g : ℝ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hg : ∀ x ∈ Set.Icc a b, ‖g x‖ ≤ C) :
    ‖∫ x in a..b, g x‖ ≤ C * |b - a| :=
  intervalIntegral.norm_integral_le_of_norm_le_const
    (pointwise_bound_on_uIoc_of_bound_on_Icc (g := g) (a := a) (b := b) (C := C) hab hg)

/-- The absolute interval length is the oriented length when `a ≤ b`. -/
theorem abs_intervalLength_eq_of_le {a b : ℝ} (hab : a ≤ b) :
    |b - a| = b - a :=
  abs_of_nonneg (sub_nonneg.mpr hab)

/-- A constant pointwise bound integrates to a constant bound on the interval. -/
theorem intervalIntegral_norm_le_constant
    (g : ℝ → ℂ) (a b C : ℝ)
    (hab : a ≤ b)
    (hg : ∀ x ∈ Set.Icc a b, ‖g x‖ ≤ C) :
    ‖∫ x in a..b, g x‖ ≤ C * |b - a| :=
  intervalIntegral_norm_le_constant_abs g a b C hab hg

/-- A constant pointwise bound integrates to an oriented-length bound when `a ≤ b`. -/
theorem intervalIntegral_norm_le_oriented_constant
    (g : ℝ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hg : ∀ x ∈ Set.Icc a b, ‖g x‖ ≤ C) :
    ‖∫ x in a..b, g x‖ ≤ (b - a) * C := by
  have hnorm :
      ‖∫ x in a..b, g x‖ ≤ C * |b - a| :=
    intervalIntegral_norm_le_constant g a b C hab hg
  have hlength : C * |b - a| = (b - a) * C :=
    Eq.trans
      (congrArg (fun t : ℝ => C * t) (abs_intervalLength_eq_of_le hab))
      (mul_comm C (b - a))
  exact hnorm.trans_eq hlength

/-- The positive horizontal length of the contour edge between `c` and `1 - c`. -/
def horizontalEdgeLength (c : ℝ) : ℝ :=
  |(1 - c) - c|

/-- The positive horizontal length unfolds to the absolute oriented length. -/
theorem horizontalEdgeLength_eq_abs (c : ℝ) :
    horizontalEdgeLength c = |(1 - c) - c| :=
  rfl

/-- The volume of the unordered horizontal edge is the positive horizontal length. -/
theorem volume_uIcc_toReal_eq_horizontalEdgeLength (c : ℝ) :
    (volume (Set.uIcc c (1 - c))).toReal = horizontalEdgeLength c :=
  Eq.trans
    (congrArg ENNReal.toReal (Real.volume_interval (a := c) (b := 1 - c)))
    (ENNReal.toReal_ofReal (abs_nonneg ((1 - c) - c)))

/-- The unordered horizontal edge has finite measure. -/
theorem volume_uIcc_lt_top (c : ℝ) :
    volume (Set.uIcc c (1 - c)) < ⊤ :=
  Eq.subst
    (motive := fun q : ENNReal => q < ⊤)
    (Real.volume_interval (a := c) (b := 1 - c)).symm
    ENNReal.ofReal_lt_top

/-- A pointwise constant bound on an unordered horizontal edge bounds the set integral. -/
theorem norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
    (g : ℝ → ℂ) (c C : ℝ)
    (hg : ∀ x ∈ Set.uIcc c (1 - c), ‖g x‖ ≤ C) :
    ‖∫ x in Set.uIcc c (1 - c), g x‖ ≤ C * horizontalEdgeLength c :=
  (MeasureTheory.norm_setIntegral_le_of_norm_le_const'
    (μ := volume) (s := Set.uIcc c (1 - c)) (f := g)
    (C := C) (volume_uIcc_lt_top c) measurableSet_uIcc hg).trans_eq
      (congrArg (fun q : ℝ => C * q) (volume_uIcc_toReal_eq_horizontalEdgeLength c))

/-- The upper endpoint of the centered horizontal strip normalizes after subtracting `1 / 2`. -/
theorem one_sub_sub_half_eq_half_sub (c : ℝ) :
    (1 - c) - 1 / 2 = 1 / 2 - c :=
  Eq.trans
    (sub_right_comm (1 : ℝ) c (1 / 2))
    (congrArg (fun t : ℝ => t - c) (sub_half (1 : ℝ)))

/-- The interval length appearing in the horizontal contour estimate simplifies to `1 - 2*c`. -/
theorem horizontalIntervalLength_eq_one_sub_two_mul (c : ℝ) :
    (1 - c) - c = 1 - 2 * c :=
  Eq.trans
    (sub_sub (1 : ℝ) c c)
    (congrArg (fun t : ℝ => 1 - t) (two_mul c).symm)

/-- The real part of the shifted top path is exactly `x - 1/2`. -/
theorem zetaCompletedExplicitFormulaTopPath_shift_re
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaTopPath r x - 1 / 2 : ℂ).re = x - 1 / 2 := by
  calc
    (zetaCompletedExplicitFormulaTopPath r x - 1 / 2 : ℂ).re
        = (zetaCompletedExplicitFormulaTopPath r x).re - (1 / 2 : ℂ).re := by
            exact Complex.sub_re _ _
    _ = (zetaCompletedExplicitFormulaTopPath r x).re - (1 / 2 : ℝ) := by
          exact congrArg
            (fun t : ℝ => (zetaCompletedExplicitFormulaTopPath r x).re - t)
            complex_half_re
    _ = x - 1 / 2 := by
          exact congrArg (fun z : ℝ => z - (1 / 2 : ℝ))
            (zetaCompletedExplicitFormulaTopPath_re_eq r x)

/-- The real part of the shifted bottom path is exactly `x - 1/2`. -/
theorem zetaCompletedExplicitFormulaBottomPath_shift_re
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2 : ℂ).re = x - 1 / 2 := by
  calc
    (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2 : ℂ).re
        = (zetaCompletedExplicitFormulaBottomPath r x).re - (1 / 2 : ℂ).re := by
            exact Complex.sub_re _ _
    _ = (zetaCompletedExplicitFormulaBottomPath r x).re - (1 / 2 : ℝ) := by
          exact congrArg
            (fun t : ℝ => (zetaCompletedExplicitFormulaBottomPath r x).re - t)
            complex_half_re
    _ = x - 1 / 2 := by
          exact congrArg (fun z : ℝ => z - (1 / 2 : ℝ))
            (zetaCompletedExplicitFormulaBottomPath_re_eq r x)

/-- The top path shifted by `1/2` stays in the vertical strip. -/
theorem zetaCompletedExplicitFormulaTopPath_shift_strip'
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    (r.c - 1 / 2) ≤ (zetaCompletedExplicitFormulaTopPath r x - 1 / 2 : ℂ).re ∧
      (zetaCompletedExplicitFormulaTopPath r x - 1 / 2 : ℂ).re ≤ (1 / 2 - r.c) := by
  constructor
  · exact (zetaCompletedExplicitFormulaTopPath_shift_re r x) ▸ sub_le_sub_right hx1 (1 / 2 : ℝ)
  · exact (zetaCompletedExplicitFormulaTopPath_shift_re r x) ▸
      (one_sub_sub_half_eq_half_sub r.c) ▸ sub_le_sub_right hx2 (1 / 2 : ℝ)

/-- The bottom path shifted by `1/2` stays in the vertical strip. -/
theorem zetaCompletedExplicitFormulaBottomPath_shift_strip'
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    (r.c - 1 / 2) ≤ (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2 : ℂ).re ∧
      (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2 : ℂ).re ≤ (1 / 2 - r.c) := by
  constructor
  · exact (zetaCompletedExplicitFormulaBottomPath_shift_re r x) ▸ sub_le_sub_right hx1 (1 / 2 : ℝ)
  · exact (zetaCompletedExplicitFormulaBottomPath_shift_re r x) ▸
      (one_sub_sub_half_eq_half_sub r.c) ▸ sub_le_sub_right hx2 (1 / 2 : ℝ)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
