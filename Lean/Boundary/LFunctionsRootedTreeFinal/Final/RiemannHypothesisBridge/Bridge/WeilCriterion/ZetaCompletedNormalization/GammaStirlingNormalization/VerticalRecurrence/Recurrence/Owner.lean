import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.Owner

/-!
# Vertical recurrence: fundamentals

This file owns the foundational recurrence product definitions and the
multiplicative Gamma recurrence transport equations.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi


/-- The recurrence product is nonzero when all its factors are nonzero. -/
theorem Complex.gammaRecurrenceProduct_ne_zero
    {z : ℂ}
    {N : ℕ}
    (hfactor_ne :
      ∀ j : ℕ,
        j < N →
          z + (j : ℂ) ≠ 0) :
    Complex.gammaRecurrenceProduct z N ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr
    (fun j hj =>
      hfactor_ne j (Finset.mem_range.mp hj))

/-- Multiplicative form of the finite Gamma recurrence. -/
theorem Complex.Gamma_shifted_eq_gammaRecurrenceProduct_mul
    {z : ℂ}
    (N : ℕ)
    (hfactor_ne :
      ∀ j : ℕ,
        j < N →
          z + (j : ℂ) ≠ 0) :
    Complex.Gamma (z + (N : ℂ)) =
      Complex.gammaRecurrenceProduct z N * Complex.Gamma z := by
  induction N with
  | zero =>
      calc
        Complex.Gamma (z + ((0 : ℕ) : ℂ)) =
            Complex.Gamma z :=
          congrArg Complex.Gamma (add_zero z)
        _ = 1 * Complex.Gamma z :=
          (one_mul (Complex.Gamma z)).symm
        _ = Complex.gammaRecurrenceProduct z 0 * Complex.Gamma z := by
          exact congrArg (fun t : ℂ => t * Complex.Gamma z)
            (Finset.prod_range_zero (fun j : ℕ => z + (j : ℂ))).symm
  | succ N ih =>
      have hfactor_prev :
          ∀ j : ℕ, j < N → z + (j : ℂ) ≠ 0 := by
        exact
          fun j hj =>
            hfactor_ne j (Nat.lt_trans hj (Nat.lt_succ_self N))
      have hN_factor : z + (N : ℂ) ≠ 0 :=
        hfactor_ne N (Nat.lt_succ_self N)
      have hsucc_arg :
          z + ((Nat.succ N : ℕ) : ℂ) =
            (z + (N : ℂ)) + 1 := by
        calc
          z + ((Nat.succ N : ℕ) : ℂ) =
              z + ((N : ℂ) + 1) := by
            exact congrArg (fun t : ℂ => z + t) (Nat.cast_succ N)
          _ = (z + (N : ℂ)) + 1 :=
            (add_assoc z (N : ℂ) 1).symm
      have hgamma_step :
          Complex.Gamma (z + ((Nat.succ N : ℕ) : ℂ)) =
            (z + (N : ℂ)) * Complex.Gamma (z + (N : ℂ)) := by
        exact Eq.trans
          (congrArg Complex.Gamma hsucc_arg)
          (Complex.Gamma_add_one (z + (N : ℂ)) hN_factor)
      have hprod_step :
          Complex.gammaRecurrenceProduct z (Nat.succ N) =
            Complex.gammaRecurrenceProduct z N * (z + (N : ℂ)) := by
        exact Finset.prod_range_succ (fun j : ℕ => z + (j : ℂ)) N
      calc
        Complex.Gamma (z + ((Nat.succ N : ℕ) : ℂ)) =
            (z + (N : ℂ)) * Complex.Gamma (z + (N : ℂ)) :=
          hgamma_step
        _ = (z + (N : ℂ)) *
              (Complex.gammaRecurrenceProduct z N * Complex.Gamma z) := by
          exact congrArg (fun t : ℂ => (z + (N : ℂ)) * t)
            (ih hfactor_prev)
        _ =
            (Complex.gammaRecurrenceProduct z N * (z + (N : ℂ))) *
              Complex.Gamma z := by
          exact (mul_left_comm (z + (N : ℂ))
            (Complex.gammaRecurrenceProduct z N) (Complex.Gamma z)).symm
        _ =
            Complex.gammaRecurrenceProduct z (Nat.succ N) *
              Complex.Gamma z := by
          exact congrArg (fun t : ℂ => t * Complex.Gamma z) hprod_step.symm

/-- The deterministic shift as a complex horizontal translation. -/
theorem Complex.fixedRealPartVerticalPoint_add_verticalStripRightShift
    (A x y : ℝ) :
    Complex.fixedRealPartVerticalPoint (x + Complex.verticalStripRightShift A) y =
      Complex.fixedRealPartVerticalPoint x y +
        (Complex.verticalStripRightShift A : ℂ) := by
  exact Complex.ext
    (by
      calc
        (Complex.fixedRealPartVerticalPoint (x + Complex.verticalStripRightShift A) y).re =
            x + (Complex.verticalStripRightShift A : ℝ) :=
          Complex.fixedRealPartVerticalPoint_re
            (x + Complex.verticalStripRightShift A) y
        _ =
            (Complex.fixedRealPartVerticalPoint x y +
              (Complex.verticalStripRightShift A : ℂ)).re := by
          have hleft :
              (Complex.fixedRealPartVerticalPoint x y).re = x :=
            Complex.fixedRealPartVerticalPoint_re x y
          have hright :
              ((Complex.verticalStripRightShift A : ℂ)).re =
                (Complex.verticalStripRightShift A : ℝ) :=
            Complex.ofReal_re (Complex.verticalStripRightShift A : ℝ)
          exact
            (Eq.trans
              (Complex.add_re
                (Complex.fixedRealPartVerticalPoint x y)
                (Complex.verticalStripRightShift A : ℂ))
              (congrArg₂ HAdd.hAdd hleft hright)).symm)
    (by
      calc
        (Complex.fixedRealPartVerticalPoint (x + Complex.verticalStripRightShift A) y).im =
            y :=
          Complex.fixedRealPartVerticalPoint_im
            (x + Complex.verticalStripRightShift A) y
        _ =
            (Complex.fixedRealPartVerticalPoint x y +
              (Complex.verticalStripRightShift A : ℂ)).im := by
          have hleft :
              (Complex.fixedRealPartVerticalPoint x y).im = y :=
            Complex.fixedRealPartVerticalPoint_im x y
          have hright :
              ((Complex.verticalStripRightShift A : ℂ)).im = 0 :=
            Complex.ofReal_im (Complex.verticalStripRightShift A : ℝ)
          exact
            (Eq.trans
              (Complex.add_im
                (Complex.fixedRealPartVerticalPoint x y)
                (Complex.verticalStripRightShift A : ℂ))
              (Eq.trans (congrArg₂ HAdd.hAdd hleft hright) (add_zero y))).symm)

/-- A natural real-part shift is the corresponding complex horizontal
translation of a fixed vertical point. -/
theorem Complex.fixedRealPartVerticalPoint_add_natCast
    (x y : ℝ)
    (N : ℕ) :
    Complex.fixedRealPartVerticalPoint (x + N) y =
      Complex.fixedRealPartVerticalPoint x y + (N : ℂ) := by
  exact Complex.ext
    (by
      calc
        (Complex.fixedRealPartVerticalPoint (x + N) y).re =
            x + (N : ℝ) :=
          Complex.fixedRealPartVerticalPoint_re (x + N) y
        _ =
            (Complex.fixedRealPartVerticalPoint x y + (N : ℂ)).re := by
          have hleft :
              (Complex.fixedRealPartVerticalPoint x y).re = x :=
            Complex.fixedRealPartVerticalPoint_re x y
          have hright : ((N : ℂ)).re = (N : ℝ) :=
            Complex.natCast_re N
          exact
            (Eq.trans
              (Complex.add_re (Complex.fixedRealPartVerticalPoint x y) (N : ℂ))
              (congrArg₂ HAdd.hAdd hleft hright)).symm)
    (by
      calc
        (Complex.fixedRealPartVerticalPoint (x + N) y).im = y :=
          Complex.fixedRealPartVerticalPoint_im (x + N) y
        _ =
            (Complex.fixedRealPartVerticalPoint x y + (N : ℂ)).im := by
          have hleft :
              (Complex.fixedRealPartVerticalPoint x y).im = y :=
            Complex.fixedRealPartVerticalPoint_im x y
          have hright : ((N : ℂ)).im = 0 :=
            Complex.natCast_im N
          exact
            (Eq.trans
              (Complex.add_im (Complex.fixedRealPartVerticalPoint x y) (N : ℂ))
              (Eq.trans (congrArg₂ HAdd.hAdd hleft hright) (add_zero y))).symm)

/-- Gamma recurrence over a deterministic finite product.

For large vertical height the factors `z + j` avoid zero, so iterating
`Γ(s + 1) = s Γ(s)` gives the exact transport from `Γ z` to
`Γ(z + N)`. -/
theorem Complex.Gamma_eq_shifted_div_gammaRecurrenceProduct
    {z : ℂ}
    (N : ℕ)
    (hfactor_ne :
      ∀ j : ℕ,
        j < N →
          z + (j : ℂ) ≠ 0) :
    Complex.Gamma z =
      Complex.Gamma (z + (N : ℂ)) /
        Complex.gammaRecurrenceProduct z N := by
  have hprod_ne :
      Complex.gammaRecurrenceProduct z N ≠ 0 :=
    Complex.gammaRecurrenceProduct_ne_zero hfactor_ne
  have hshift :
      Complex.Gamma (z + (N : ℂ)) =
        Complex.gammaRecurrenceProduct z N * Complex.Gamma z :=
    Complex.Gamma_shifted_eq_gammaRecurrenceProduct_mul N hfactor_ne
  exact
    (calc
      Complex.Gamma (z + (N : ℂ)) /
          Complex.gammaRecurrenceProduct z N =
          (Complex.gammaRecurrenceProduct z N * Complex.Gamma z) /
            Complex.gammaRecurrenceProduct z N := by
        exact congrArg
          (fun t : ℂ => t / Complex.gammaRecurrenceProduct z N)
          hshift
      _ = Complex.Gamma z :=
        mul_div_cancel_left₀ (Complex.Gamma z) hprod_ne).symm

/- The norm form of recurrence transport is owned by `VerticalRecurrence.Factors`. -/

end

end LFunctions
end Boundary
