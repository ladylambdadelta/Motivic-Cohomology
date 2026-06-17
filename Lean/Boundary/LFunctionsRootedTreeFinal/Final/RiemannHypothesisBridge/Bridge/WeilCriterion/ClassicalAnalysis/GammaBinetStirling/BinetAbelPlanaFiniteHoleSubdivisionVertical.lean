import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteHoleSubdivisionHorizontal

/-!
# Finite-hole subdivision vertical assembly

This file owns the vertical-side telescoping algebra for the Abel-Plana
punctured rectangle.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Topology Interval


/-- Base-case additive rearrangement in the vertical-side telescoping identity. -/
theorem Complex.finiteAbelPlana_verticalPVSide_zero_step_algebra
    (LPV RPV Sright Sleft : ℂ) :
    (RPV - LPV) - (Sright - Sleft) =
      (Sleft - LPV) + (RPV - Sright) + 0 := by
  calc
    (RPV - LPV) - (Sright - Sleft) =
        (RPV + -LPV) + -(Sright + -Sleft) := by
      exact congrArg₂
        HAdd.hAdd
        (sub_eq_add_neg RPV LPV)
        (congrArg Neg.neg (sub_eq_add_neg Sright Sleft))
    _ = (RPV + -LPV) + (-(-Sleft) + -Sright) := by
      exact congrArg
        (fun z : ℂ => (RPV + -LPV) + z)
        (neg_add_rev Sright (-Sleft))
    _ = (RPV + -LPV) + (-Sright + -(-Sleft)) := by
      exact congrArg
        (fun z : ℂ => (RPV + -LPV) + z)
        (add_comm (-(-Sleft)) (-Sright))
    _ = (RPV + -LPV) + (-Sright + Sleft) := by
      exact congrArg
        (fun z : ℂ => (RPV + -LPV) + (-Sright + z))
        (neg_neg Sleft)
    _ = RPV + (-LPV + (-Sright + Sleft)) :=
      add_assoc RPV (-LPV) (-Sright + Sleft)
    _ = RPV + ((-Sright + Sleft) + -LPV) := by
      exact congrArg (fun z : ℂ => RPV + z)
        (add_comm (-LPV) (-Sright + Sleft))
    _ = RPV + (-Sright + (Sleft + -LPV)) := by
      exact congrArg (fun z : ℂ => RPV + z)
        (add_assoc (-Sright) Sleft (-LPV))
    _ = (RPV + -Sright) + (Sleft + -LPV) := by
      exact Eq.symm (add_assoc RPV (-Sright) (Sleft + -LPV))
    _ = (Sleft + -LPV) + (RPV + -Sright) :=
      add_comm (RPV + -Sright) (Sleft + -LPV)
    _ = (Sleft - LPV) + (RPV + -Sright) := by
      exact congrArg
        (fun z : ℂ => z + (RPV + -Sright))
        (Eq.symm (sub_eq_add_neg Sleft LPV))
    _ = (Sleft - LPV) + (RPV - Sright) := by
      exact congrArg
        (fun z : ℂ => (Sleft - LPV) + z)
        (Eq.symm (sub_eq_add_neg RPV Sright))
    _ = (Sleft - LPV) + (RPV - Sright) + 0 := by
      exact Eq.symm (add_zero ((Sleft - LPV) + (RPV - Sright)))

/-- The induction hypothesis in the vertical-side telescoping identity can be
cancelled by the common right principal-value side. -/
theorem Complex.finiteAbelPlana_verticalPVSide_succ_cancel_induction
    (LPV RPV Sright stripSum interiorSum leftCap : ℂ)
    (ih :
      (RPV - LPV) - stripSum =
        leftCap + (RPV - Sright) + interiorSum) :
    -LPV - stripSum = leftCap - Sright + interiorSum := by
  have hleft :
      (RPV - LPV) - stripSum =
        RPV + (-LPV - stripSum) := by
    calc
      (RPV - LPV) - stripSum =
          (RPV + -LPV) - stripSum := by
        exact congrArg
          (fun z : ℂ => z - stripSum)
          (sub_eq_add_neg RPV LPV)
      _ = (RPV + -LPV) + -stripSum :=
        sub_eq_add_neg (RPV + -LPV) stripSum
      _ = RPV + (-LPV + -stripSum) :=
        add_assoc RPV (-LPV) (-stripSum)
      _ = RPV + (-LPV - stripSum) := by
        exact congrArg
          (fun z : ℂ => RPV + z)
          (Eq.symm (sub_eq_add_neg (-LPV) stripSum))
  have hright :
      leftCap + (RPV - Sright) + interiorSum =
        RPV + (leftCap - Sright + interiorSum) := by
    calc
      leftCap + (RPV - Sright) + interiorSum =
          leftCap + (RPV + -Sright) + interiorSum := by
        exact congrArg
          (fun z : ℂ => leftCap + z + interiorSum)
          (sub_eq_add_neg RPV Sright)
      _ = (leftCap + (RPV + -Sright)) + interiorSum := rfl
      _ = ((leftCap + RPV) + -Sright) + interiorSum := by
        exact congrArg
          (fun z : ℂ => z + interiorSum)
          (Eq.symm (add_assoc leftCap RPV (-Sright)))
      _ = ((RPV + leftCap) + -Sright) + interiorSum := by
        exact congrArg
          (fun z : ℂ => (z + -Sright) + interiorSum)
          (add_comm leftCap RPV)
      _ = (RPV + (leftCap + -Sright)) + interiorSum := by
        exact congrArg
          (fun z : ℂ => z + interiorSum)
          (add_assoc RPV leftCap (-Sright))
      _ = RPV + ((leftCap + -Sright) + interiorSum) :=
        add_assoc RPV (leftCap + -Sright) interiorSum
      _ = RPV + (leftCap + -Sright + interiorSum) := rfl
      _ = RPV + (leftCap - Sright + interiorSum) := by
        exact congrArg
          (fun z : ℂ => RPV + (z + interiorSum))
          (Eq.symm (sub_eq_add_neg leftCap Sright))
  have hcommon :
      RPV + (-LPV - stripSum) =
        RPV + (leftCap - Sright + interiorSum) :=
    hleft.symm.trans (ih.trans hright)
  exact add_left_cancel hcommon

/-- Left-hand decomposition in the successor step of the vertical telescoping
identity. -/
theorem Complex.finiteAbelPlana_verticalPVSide_succ_left_decomp
    (LPV RPVnext SrightNext SleftNext stripSum : ℂ) :
    (RPVnext - LPV) - (stripSum + (SrightNext - SleftNext)) =
      (-LPV - stripSum) + (RPVnext - SrightNext + SleftNext) := by
  calc
    (RPVnext - LPV) - (stripSum + (SrightNext - SleftNext)) =
        (RPVnext - LPV) + -(stripSum + (SrightNext - SleftNext)) := by
      exact sub_eq_add_neg
        (RPVnext - LPV)
        (stripSum + (SrightNext - SleftNext))
    _ = (RPVnext + -LPV) + -(stripSum + (SrightNext - SleftNext)) := by
      exact congrArg
        (fun z : ℂ => z + -(stripSum + (SrightNext - SleftNext)))
        (sub_eq_add_neg RPVnext LPV)
    _ = (RPVnext + -LPV) + (-(SrightNext - SleftNext) + -stripSum) := by
      exact congrArg
        (fun z : ℂ => (RPVnext + -LPV) + z)
        (neg_add_rev stripSum (SrightNext - SleftNext))
    _ = (RPVnext + -LPV) + (-stripSum + -(SrightNext - SleftNext)) := by
      exact congrArg
        (fun z : ℂ => (RPVnext + -LPV) + z)
        (add_comm (-(SrightNext - SleftNext)) (-stripSum))
    _ = (RPVnext + -LPV) + (-stripSum + -(SrightNext + -SleftNext)) := by
      exact congrArg
        (fun z : ℂ => (RPVnext + -LPV) + (-stripSum + z))
        (congrArg Neg.neg (sub_eq_add_neg SrightNext SleftNext))
    _ = (RPVnext + -LPV) + (-stripSum + (-(-SleftNext) + -SrightNext)) := by
      exact congrArg
        (fun z : ℂ => (RPVnext + -LPV) + (-stripSum + z))
        (neg_add_rev SrightNext (-SleftNext))
    _ = (RPVnext + -LPV) + (-stripSum + (-SrightNext + -(-SleftNext))) := by
      exact congrArg
        (fun z : ℂ => (RPVnext + -LPV) + (-stripSum + z))
        (add_comm (-(-SleftNext)) (-SrightNext))
    _ = (RPVnext + -LPV) + (-stripSum + (-SrightNext + SleftNext)) := by
      exact congrArg
        (fun z : ℂ => (RPVnext + -LPV) + (-stripSum + (-SrightNext + z)))
        (neg_neg SleftNext)
    _ = RPVnext + (-LPV + (-stripSum + (-SrightNext + SleftNext))) :=
      add_assoc RPVnext (-LPV) (-stripSum + (-SrightNext + SleftNext))
    _ = RPVnext + ((-LPV + -stripSum) + (-SrightNext + SleftNext)) := by
      exact congrArg
        (fun z : ℂ => RPVnext + z)
        (Eq.symm (add_assoc (-LPV) (-stripSum) (-SrightNext + SleftNext)))
    _ = ((-LPV + -stripSum) + (-SrightNext + SleftNext)) + RPVnext :=
      add_comm RPVnext ((-LPV + -stripSum) + (-SrightNext + SleftNext))
    _ = (-LPV + -stripSum) + ((-SrightNext + SleftNext) + RPVnext) :=
      add_assoc (-LPV + -stripSum) (-SrightNext + SleftNext) RPVnext
    _ = (-LPV + -stripSum) + (RPVnext + (-SrightNext + SleftNext)) := by
      exact congrArg
        (fun z : ℂ => (-LPV + -stripSum) + z)
        (add_comm (-SrightNext + SleftNext) RPVnext)
    _ = (-LPV + -stripSum) + ((RPVnext + -SrightNext) + SleftNext) := by
      exact congrArg
        (fun z : ℂ => (-LPV + -stripSum) + z)
        (Eq.symm (add_assoc RPVnext (-SrightNext) SleftNext))
    _ = (-LPV - stripSum) + ((RPVnext + -SrightNext) + SleftNext) := by
      exact congrArg
        (fun z : ℂ => z + ((RPVnext + -SrightNext) + SleftNext))
        (Eq.symm (sub_eq_add_neg (-LPV) stripSum))
    _ = (-LPV - stripSum) + (RPVnext - SrightNext + SleftNext) := by
      exact congrArg
        (fun z : ℂ => (-LPV - stripSum) + (z + SleftNext))
        (Eq.symm (sub_eq_add_neg RPVnext SrightNext))

/-- Right-hand reassociation in the successor step of the vertical telescoping
identity. -/
theorem Complex.finiteAbelPlana_verticalPVSide_succ_right_reassoc
    (leftCap Sright interiorSum RPVnext SrightNext SleftNext : ℂ) :
    (leftCap - Sright + interiorSum) +
        (RPVnext - SrightNext + SleftNext) =
      leftCap + (RPVnext - SrightNext) +
        (interiorSum + (SleftNext - Sright)) := by
  calc
    (leftCap - Sright + interiorSum) +
        (RPVnext - SrightNext + SleftNext) =
      ((leftCap + -Sright) + interiorSum) +
        (RPVnext - SrightNext + SleftNext) := by
        exact congrArg
          (fun z : ℂ => (z + interiorSum) +
            (RPVnext - SrightNext + SleftNext))
          (sub_eq_add_neg leftCap Sright)
    _ =
      ((leftCap + -Sright) + interiorSum) +
        ((RPVnext + -SrightNext) + SleftNext) := by
        exact congrArg
          (fun z : ℂ => ((leftCap + -Sright) + interiorSum) + (z + SleftNext))
          (sub_eq_add_neg RPVnext SrightNext)
    _ = (leftCap + -Sright) +
        (interiorSum + ((RPVnext + -SrightNext) + SleftNext)) :=
      add_assoc (leftCap + -Sright) interiorSum
        ((RPVnext + -SrightNext) + SleftNext)
    _ = leftCap + (-Sright +
        (interiorSum + ((RPVnext + -SrightNext) + SleftNext))) :=
      add_assoc leftCap (-Sright)
        (interiorSum + ((RPVnext + -SrightNext) + SleftNext))
    _ = leftCap + (interiorSum +
        ((RPVnext + -SrightNext) + SleftNext) + -Sright) := by
      exact congrArg
        (fun z : ℂ => leftCap + z)
        (add_comm (-Sright)
          (interiorSum + ((RPVnext + -SrightNext) + SleftNext)))
    _ = leftCap + (interiorSum +
        (((RPVnext + -SrightNext) + SleftNext) + -Sright)) := by
      exact congrArg
        (fun z : ℂ => leftCap + z)
        (add_assoc interiorSum ((RPVnext + -SrightNext) + SleftNext) (-Sright))
    _ = leftCap + (interiorSum +
        ((RPVnext + -SrightNext) + (SleftNext + -Sright))) := by
      exact congrArg
        (fun z : ℂ => leftCap + (interiorSum + z))
        (add_assoc (RPVnext + -SrightNext) SleftNext (-Sright))
    _ = leftCap + ((RPVnext + -SrightNext) +
        (interiorSum + (SleftNext + -Sright))) := by
      exact congrArg
        (fun z : ℂ => leftCap + z)
        (add_left_comm interiorSum (RPVnext + -SrightNext) (SleftNext + -Sright))
    _ = leftCap + (RPVnext + -SrightNext) +
        (interiorSum + (SleftNext + -Sright)) :=
      Eq.symm
        (add_assoc leftCap (RPVnext + -SrightNext)
          (interiorSum + (SleftNext + -Sright)))
    _ = leftCap + (RPVnext - SrightNext) +
        (interiorSum + (SleftNext + -Sright)) := by
      exact congrArg
        (fun z : ℂ => leftCap + z + (interiorSum + (SleftNext + -Sright)))
        (Eq.symm (sub_eq_add_neg RPVnext SrightNext))
    _ = leftCap + (RPVnext - SrightNext) +
        (interiorSum + (SleftNext - Sright)) := by
      exact congrArg
        (fun z : ℂ =>
          leftCap + (RPVnext - SrightNext) + (interiorSum + z))
        (Eq.symm (sub_eq_add_neg SleftNext Sright))

/-- The additive successor step in the vertical-side telescoping identity. -/
theorem Complex.finiteAbelPlana_verticalPVSide_succ_step_algebra
    (LPV RPV RPVnext Sright SrightNext SleftNext stripSum interiorSum leftCap : ℂ)
    (ih :
      (RPV - LPV) - stripSum =
        leftCap + (RPV - Sright) + interiorSum) :
    (RPVnext - LPV) - (stripSum + (SrightNext - SleftNext)) =
      leftCap + (RPVnext - SrightNext) +
        (interiorSum + (SleftNext - Sright)) := by
  have hbase :
      -LPV - stripSum = leftCap - Sright + interiorSum :=
    Complex.finiteAbelPlana_verticalPVSide_succ_cancel_induction
      LPV RPV Sright stripSum interiorSum leftCap ih
  calc
    (RPVnext - LPV) - (stripSum + (SrightNext - SleftNext)) =
        (-LPV - stripSum) + (RPVnext - SrightNext + SleftNext) :=
      Complex.finiteAbelPlana_verticalPVSide_succ_left_decomp
        LPV RPVnext SrightNext SleftNext stripSum
    _ =
        (leftCap - Sright + interiorSum) +
          (RPVnext - SrightNext + SleftNext) := by
      exact
        congrArg
          (fun z : ℂ => z + (RPVnext - SrightNext + SleftNext))
          hbase
    _ =
        leftCap + (RPVnext - SrightNext) +
          (interiorSum + (SleftNext - Sright)) :=
      Complex.finiteAbelPlana_verticalPVSide_succ_right_reassoc
        leftCap Sright interiorSum RPVnext SrightNext SleftNext

/-- Vertical-side telescoping for the finite-hole subdivision.

Subtracting the safe-strip vertical sides from the principal-value endpoint
vertical sides leaves exactly the endpoint collars and the interior collar
vertical sides. -/
theorem Complex.finiteAbelPlana_log_verticalPVSide_sub_verticalStrips_eq_capCollars
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) -
      (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)) =
      (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) +
        (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ) +
          ∑ n in Finset.range N,
            (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ) := by
  induction N with
  | zero =>
      have hstrip_sum :
          (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet 0,
            (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)) =
            (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ) :=
        Eq.trans
          (congrArg
            (fun s : Finset ℕ =>
              ∑ k in s,
                (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
                  Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ))
            (Complex.finiteAbelPlana_verticalStripIndexSet_unfold 0))
          (Finset.sum_range_one
            (fun k =>
              (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)))
      have hinterior_sum :
          (∑ n in Finset.range 0,
            (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ)) =
            0 :=
        Finset.sum_range_zero
          (fun n =>
            (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ))
      exact hstrip_sum ▸ hinterior_sum ▸ by
        exact
          Complex.finiteAbelPlana_verticalPVSide_zero_step_algebra
            (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ)
            (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV 0 w T ρ)
            (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide 0 w T ρ)
            (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ)
  | succ N ih =>
      have hstrip_sum :
          (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet (N + 1),
            (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)) =
            (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)) +
              (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide (N + 1) w T ρ -
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (N + 1) w T ρ) :=
        Eq.trans
          (congrArg
            (fun s : Finset ℕ =>
              ∑ k in s,
                (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
                  Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ))
            (Complex.finiteAbelPlana_verticalStripIndexSet_unfold (N + 1)))
          (Eq.trans
            (Finset.sum_range_succ
              (f := fun k =>
                (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
                  Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ))
              (n := N + 1))
            (congrArg
              (fun z : ℂ =>
                z +
                  (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide (N + 1) w T ρ -
                    Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (N + 1) w T ρ))
              (congrArg
                (fun s : Finset ℕ =>
                  ∑ k in s,
                    (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
                      Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ))
                (Complex.finiteAbelPlana_verticalStripIndexSet_unfold N).symm)))
      have hinterior_sum :
          (∑ n in Finset.range (N + 1),
            (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ)) =
            (∑ n in Finset.range N,
              (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ)) +
              (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (N + 1) w T ρ -
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ) :=
        Finset.sum_range_succ
          (f := fun n =>
            (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ))
          (n := N)
      exact hstrip_sum ▸ hinterior_sum ▸
        Complex.finiteAbelPlana_verticalPVSide_succ_step_algebra
          (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ)
          (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ)
          (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV (N + 1) w T ρ)
          (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ)
          (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide (N + 1) w T ρ)
          (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (N + 1) w T ρ)
          (∑ k in Finset.range (N + 1),
            (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ))
          (∑ n in Finset.range N,
            (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ))
          (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ)
          ih

end

end LFunctions
end Boundary
