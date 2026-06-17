import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteHoleSubdivisionVertical

/-!
# Finite-hole subdivision assembly

This file owns the vertical telescoping and final finite-hole boundary assembly
for the Abel-Plana punctured rectangle.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Topology Interval


/-- Separating the lower and upper horizontal decompositions into the common
strip part and the three collar parts. -/
theorem Complex.finiteAbelPlana_horizontal_three_collar_separation
    (LL LU RL RU IL IU SL SU : ℂ) :
    SL + (LL + RL + IL) - (SU + (LU + RU + IU)) =
      (SL - SU) + ((LL - LU) + (RL - RU) + (IL - IU)) := by
  have hinner :
      (LL + RL + IL) - (LU + RU + IU) =
        ((LL - LU) + (RL - RU)) + (IL - IU) := by
    calc
      (LL + RL + IL) - (LU + RU + IU) =
          (LL + RL) - (LU + RU) + (IL - IU) :=
        (sub_add_sub_comm (LL + RL) (LU + RU) IL IU).symm
      _ = ((LL - LU) + (RL - RU)) + (IL - IU) := by
        exact congrArg
          (fun z : ℂ => z + (IL - IU))
          (sub_add_sub_comm LL LU RL RU).symm
  calc
    SL + (LL + RL + IL) - (SU + (LU + RU + IU)) =
        (SL - SU) + ((LL + RL + IL) - (LU + RU + IU)) :=
      (sub_add_sub_comm SL SU (LL + RL + IL) (LU + RU + IU)).symm
    _ = (SL - SU) + (((LL - LU) + (RL - RU)) + (IL - IU)) := by
      exact congrArg (fun z : ℂ => (SL - SU) + z) hinner
    _ = (SL - SU) + ((LL - LU) + (RL - RU) + (IL - IU)) := rfl

/-- Cancelling the common safe-strip horizontal part in the aggregate
rectangle-minus-strip expression. -/
theorem Complex.finiteAbelPlana_common_strip_aggregate_cancel
    (S C R D : ℂ) :
    ((S + C) + R) - (S + D) = C + (R - D) := by
  calc
    ((S + C) + R) - (S + D) = (S + (C + R)) - (S + D) := by
      exact congrArg (fun z : ℂ => z - (S + D)) (add_assoc S C R)
    _ = (C + R) - D :=
      add_sub_add_left_eq_sub (C + R) D S
    _ = C + (R - D) :=
      add_sub_assoc C R D

/-- Collecting the three collar contributions separately from the three
vertical contributions. -/
theorem Complex.finiteAbelPlana_three_collar_vertical_collect
    (A B C X Y Z : ℂ) :
    (A + X) + (B + Y) + (C + Z) =
      (A + B + C) + (X + Y + Z) := by
  calc
    (A + X) + (B + Y) + (C + Z) =
        ((A + X) + (B + Y)) + (C + Z) := rfl
    _ = (A + (X + (B + Y))) + (C + Z) := by
      exact congrArg (fun z : ℂ => z + (C + Z)) (add_assoc A X (B + Y))
    _ = (A + (B + (X + Y))) + (C + Z) := by
      exact congrArg (fun z : ℂ => (A + z) + (C + Z)) (add_left_comm X B Y)
    _ = ((A + B) + (X + Y)) + (C + Z) := by
      exact congrArg (fun z : ℂ => z + (C + Z)) (Eq.symm (add_assoc A B (X + Y)))
    _ = (A + B) + ((X + Y) + (C + Z)) :=
      add_assoc (A + B) (X + Y) (C + Z)
    _ = (A + B) + (C + ((X + Y) + Z)) := by
      exact congrArg (fun z : ℂ => (A + B) + z) (add_left_comm (X + Y) C Z)
    _ = ((A + B) + C) + ((X + Y) + Z) := by
      exact Eq.symm (add_assoc (A + B) C ((X + Y) + Z))
    _ = (A + B + C) + (X + Y + Z) := rfl

/-- Transporting a vertical telescoping identity through the common residue
normalization scalar. -/
theorem Complex.finiteAbelPlana_vertical_telescope_scale
    (q A B SR SV X Y U V : ℂ)
    (h :
      q * ((A - B) - (SR - SV)) =
        q * ((X - B) + (A - Y) + (U - V))) :
    (q * A - q * B) - (q * SR - q * SV) =
      (q * X - q * B) + (q * A - q * Y) + (q * U - q * V) := by
  have hleft :
      q * ((A - B) - (SR - SV)) =
        (q * A - q * B) - (q * SR - q * SV) := by
    calc
      q * ((A - B) - (SR - SV)) = q * (A - B) - q * (SR - SV) :=
        mul_sub q (A - B) (SR - SV)
      _ = (q * A - q * B) - q * (SR - SV) := by
        exact congrArg (fun z : ℂ => z - q * (SR - SV)) (mul_sub q A B)
      _ = (q * A - q * B) - (q * SR - q * SV) := by
        exact congrArg (fun z : ℂ => (q * A - q * B) - z) (mul_sub q SR SV)
  have hright :
      q * ((X - B) + (A - Y) + (U - V)) =
        (q * X - q * B) + (q * A - q * Y) + (q * U - q * V) := by
    calc
      q * ((X - B) + (A - Y) + (U - V)) =
          q * ((X - B) + (A - Y)) + q * (U - V) :=
        mul_add q ((X - B) + (A - Y)) (U - V)
      _ = (q * (X - B) + q * (A - Y)) + q * (U - V) := by
        exact congrArg (fun z : ℂ => z + q * (U - V)) (mul_add q (X - B) (A - Y))
      _ = ((q * X - q * B) + q * (A - Y)) + q * (U - V) := by
        exact congrArg (fun z : ℂ => (z + q * (A - Y)) + q * (U - V)) (mul_sub q X B)
      _ = ((q * X - q * B) + (q * A - q * Y)) + q * (U - V) := by
        exact congrArg (fun z : ℂ => ((q * X - q * B) + z) + q * (U - V)) (mul_sub q A Y)
      _ = ((q * X - q * B) + (q * A - q * Y)) + (q * U - q * V) := by
        exact congrArg
          (fun z : ℂ => ((q * X - q * B) + (q * A - q * Y)) + z)
          (mul_sub q U V)
      _ = (q * X - q * B) + (q * A - q * Y) + (q * U - q * V) := rfl
  exact hleft.symm.trans (h.trans hright)

/-- Distributing the common normalization scalar across one oriented
four-side boundary expression. -/
theorem Complex.finiteAbelPlana_normalized_four_term_expand
    (q A B C D : ℂ) :
    q * (A - B + C - D) = q * A - q * B + q * C - q * D := by
  calc
    q * (A - B + C - D) =
        q * (A - B + C) - q * D :=
      mul_sub q (A - B + C) D
    _ = (q * (A - B) + q * C) - q * D := by
      exact congrArg
        (fun z : ℂ => z - q * D)
        (mul_add q (A - B) C)
    _ = ((q * A - q * B) + q * C) - q * D := by
      exact congrArg
        (fun z : ℂ => (z + q * C) - q * D)
        (mul_sub q A B)
    _ = q * A - q * B + q * C - q * D := rfl

/-- Distributing the common normalization scalar across three added
contributions. -/
theorem Complex.finiteAbelPlana_normalized_three_term_expand
    (q A B C : ℂ) :
    q * (A + B + C) = q * A + q * B + q * C := by
  calc
    q * (A + B + C) =
        q * (A + B) + q * C :=
      mul_add q (A + B) C
    _ = (q * A + q * B) + q * C := by
      exact congrArg
        (fun z : ℂ => z + q * C)
        (mul_add q A B)
    _ = q * A + q * B + q * C := rfl

/-- Distributing the common normalization scalar across the finite-height
horizontal and vertical side pair. -/
theorem Complex.finiteAbelPlana_normalized_rectangle_pair_expand
    (q L U R S : ℂ) :
    q * ((L - U) + (R - S)) = (q * L - q * U) + (q * R - q * S) := by
  calc
    q * ((L - U) + (R - S)) =
        q * (L - U) + q * (R - S) :=
      mul_add q (L - U) (R - S)
    _ = (q * L - q * U) + q * (R - S) := by
      exact congrArg
        (fun z : ℂ => z + q * (R - S))
        (mul_sub q L U)
    _ = (q * L - q * U) + (q * R - q * S) := by
      exact congrArg
        (fun z : ℂ => (q * L - q * U) + z)
        (mul_sub q R S)

/-- Distributing the common normalization scalar and a finite sum across
oriented four-side boundary expressions. -/
theorem Complex.finiteAbelPlana_normalized_four_term_sum_expand
    {ι : Type}
    (s : Finset ι)
    (q : ℂ)
    (A B C D : ι → ℂ) :
    (∑ i in s, q * (A i - B i + C i - D i)) =
        (∑ i in s, q * A i) -
            (∑ i in s, q * B i) +
          (∑ i in s, q * C i) -
        ∑ i in s, q * D i := by
  have hterm :
      (∑ i in s, q * (A i - B i + C i - D i)) =
          ∑ i in s, (q * A i - q * B i + q * C i - q * D i) :=
    Finset.sum_congr rfl
      (fun i _hi =>
        Complex.finiteAbelPlana_normalized_four_term_expand
          q (A i) (B i) (C i) (D i))
  have hsubD :
      (∑ i in s, (q * A i - q * B i + q * C i - q * D i)) =
          (∑ i in s, (q * A i - q * B i + q * C i)) -
            ∑ i in s, q * D i :=
    Finset.sum_sub_distrib
  have haddC :
      (∑ i in s, (q * A i - q * B i + q * C i)) =
          (∑ i in s, (q * A i - q * B i)) +
            ∑ i in s, q * C i :=
    Finset.sum_add_distrib
  have hsubB :
      (∑ i in s, (q * A i - q * B i)) =
          (∑ i in s, q * A i) - ∑ i in s, q * B i :=
    Finset.sum_sub_distrib
  calc
    (∑ i in s, q * (A i - B i + C i - D i)) =
        ∑ i in s, (q * A i - q * B i + q * C i - q * D i) :=
      hterm
    _ =
        (∑ i in s, (q * A i - q * B i + q * C i)) -
          ∑ i in s, q * D i :=
      hsubD
    _ =
        ((∑ i in s, (q * A i - q * B i)) +
            ∑ i in s, q * C i) -
          ∑ i in s, q * D i := by
      exact congrArg
        (fun z : ℂ => z - ∑ i in s, q * D i)
        haddC
    _ =
        (((∑ i in s, q * A i) - ∑ i in s, q * B i) +
            ∑ i in s, q * C i) -
          ∑ i in s, q * D i := by
      exact congrArg
        (fun z : ℂ => (z + ∑ i in s, q * C i) - ∑ i in s, q * D i)
        hsubB
    _ =
        (∑ i in s, q * A i) -
            (∑ i in s, q * B i) +
          (∑ i in s, q * C i) -
        ∑ i in s, q * D i := rfl

/-- Normalized cap/collar assembly after the lower, upper, and vertical
side decompositions have been named.

The variables are ordered by geometry: endpoint collars, interior collars,
outer horizontal strip sums, and vertical strip sums. -/
theorem Complex.finiteAbelPlana_normalized_capCollar_assembly_algebra
    (LL LU VL0 LPV RL RU RPV VRN IL IU IVL IVR SL SU SR SV : ℂ)
    (hvertical :
      (RPV - LPV) - (SR - SV) =
        (VL0 - LPV) + (RPV - VRN) + (IVL - IVR)) :
    (LL - LU + VL0 - LPV) +
          (RL - RU + RPV - VRN) +
        (IL - IU + IVL - IVR) =
      (SL + (LL + RL + IL) -
          (SU + (LU + RU + IU)) +
            (RPV - LPV)) -
        (SL - SU + SR - SV) := by
  let C : ℂ := (LL - LU) + (RL - RU) + (IL - IU)
  let R : ℂ := RPV - LPV
  let D : ℂ := SR - SV
  have hthird :
      IL - IU + IVL - IVR = (IL - IU) + (IVL - IVR) :=
    add_sub_assoc (IL - IU) IVL IVR
  have hleft_collect :
      (LL - LU + VL0 - LPV) + (RL - RU + RPV - VRN) + (IL - IU + IVL - IVR) =
        C + ((VL0 - LPV) + (RPV - VRN) + (IVL - IVR)) := by
    calc
      (LL - LU + VL0 - LPV) + (RL - RU + RPV - VRN) + (IL - IU + IVL - IVR) =
          ((LL - LU) + (VL0 - LPV)) + (RL - RU + RPV - VRN) +
            (IL - IU + IVL - IVR) := by
        exact congrArg
          (fun z : ℂ => z + (RL - RU + RPV - VRN) + (IL - IU + IVL - IVR))
          (add_sub_assoc (LL - LU) VL0 LPV)
      _ = ((LL - LU) + (VL0 - LPV)) + ((RL - RU) + (RPV - VRN)) +
            (IL - IU + IVL - IVR) := by
        exact congrArg
          (fun z : ℂ =>
            ((LL - LU) + (VL0 - LPV)) + z + (IL - IU + IVL - IVR))
          (add_sub_assoc (RL - RU) RPV VRN)
      _ = ((LL - LU) + (VL0 - LPV)) + ((RL - RU) + (RPV - VRN)) +
            ((IL - IU) + (IVL - IVR)) := by
        exact congrArg
          (fun z : ℂ =>
            ((LL - LU) + (VL0 - LPV)) + ((RL - RU) + (RPV - VRN)) + z)
          hthird
      _ = ((LL - LU) + (RL - RU) + (IL - IU)) +
            ((VL0 - LPV) + (RPV - VRN) + (IVL - IVR)) :=
        Complex.finiteAbelPlana_three_collar_vertical_collect
          (LL - LU) (RL - RU) (IL - IU) (VL0 - LPV) (RPV - VRN) (IVL - IVR)
      _ = C + ((VL0 - LPV) + (RPV - VRN) + (IVL - IVR)) := rfl
  have hright_horizontal :
      SL + (LL + RL + IL) - (SU + (LU + RU + IU)) =
        (SL - SU) + C := by
    calc
      SL + (LL + RL + IL) - (SU + (LU + RU + IU)) =
          (SL - SU) + ((LL - LU) + (RL - RU) + (IL - IU)) :=
        Complex.finiteAbelPlana_horizontal_three_collar_separation
          LL LU RL RU IL IU SL SU
      _ = (SL - SU) + C := rfl
  have hstrip :
      SL - SU + SR - SV = (SL - SU) + D := by
    calc
      SL - SU + SR - SV = (SL - SU) + (SR - SV) :=
        add_sub_assoc (SL - SU) SR SV
      _ = (SL - SU) + D := rfl
  have hright_reduce :
      (SL + (LL + RL + IL) - (SU + (LU + RU + IU)) + (RPV - LPV)) -
          (SL - SU + SR - SV) =
        C + (R - D) := by
    calc
      (SL + (LL + RL + IL) - (SU + (LU + RU + IU)) + (RPV - LPV)) -
          (SL - SU + SR - SV) =
          (((SL - SU) + C) + (RPV - LPV)) - (SL - SU + SR - SV) := by
        exact congrArg
          (fun z : ℂ => (z + (RPV - LPV)) - (SL - SU + SR - SV))
          hright_horizontal
      _ = (((SL - SU) + C) + R) - (SL - SU + SR - SV) := rfl
      _ = (((SL - SU) + C) + R) - ((SL - SU) + D) := by
        exact congrArg (fun z : ℂ => (((SL - SU) + C) + R) - z) hstrip
      _ = C + (R - D) :=
        Complex.finiteAbelPlana_common_strip_aggregate_cancel (SL - SU) C R D
  calc
    (LL - LU + VL0 - LPV) + (RL - RU + RPV - VRN) + (IL - IU + IVL - IVR) =
        C + ((VL0 - LPV) + (RPV - VRN) + (IVL - IVR)) :=
      hleft_collect
    _ = C + (R - D) := by
      exact congrArg (fun z : ℂ => C + z) hvertical.symm
    _ =
      (SL + (LL + RL + IL) - (SU + (LU + RU + IU)) + (RPV - LPV)) -
        (SL - SU + SR - SV) :=
      hright_reduce.symm

/-- Additive assembly of the concrete cap/collar boundary after the three
owner decompositions have been supplied. -/
theorem Complex.finiteAbelPlana_concreteCapCollarBoundaryContribution_eq_pvNormalized_sub_verticalStripBoundarySum_of_sides
    {w : ℂ}
    (N : ℕ)
    (T ρ : ℝ)
    (hlower :
      Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ))
    (hupper :
      Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ))
    (hvertical :
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
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ)) :
    Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ =
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ := by
  let q : ℂ := ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹
  have hstrip_vertical_sum :
      (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)) =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ) -
          ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ :=
    Finset.sum_sub_distrib
  have hinterior_vertical_sum :
      (∑ n in Finset.range N,
        (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ)) =
        (∑ n in Finset.range N,
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ) -
          ∑ n in Finset.range N,
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ :=
    Finset.sum_sub_distrib
  have hvertical_summed :
      (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) -
        ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ) -
          ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ) =
        (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) +
          (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ) +
            ((∑ n in Finset.range N,
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ) -
              ∑ n in Finset.range N,
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ) := by
    exact
      Eq.trans
        (congrArg
          (fun z : ℂ =>
            (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
                Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) - z)
          hstrip_vertical_sum.symm)
        (Eq.trans hvertical
          (congrArg
            (fun z : ℂ =>
              (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
                  Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) +
                (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
                  Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ) + z)
            hinterior_vertical_sum))
  have hvertical_normalized :
      q *
          ((Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) -
            ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ) -
              ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)) =
        q *
          ((Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) +
            (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ) +
              ((∑ n in Finset.range N,
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ) -
                ∑ n in Finset.range N,
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ)) :=
    congrArg (fun z : ℂ => q * z) hvertical_summed
  have hvertical_scaled :
      q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
            q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) -
          ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ)) -
            ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)) =
        q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ) -
              q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) +
            (q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ)) +
          ((∑ n in Finset.range N,
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ)) -
            ∑ n in Finset.range N,
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ)) := by
    have hraw :
        q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
              q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) -
            (q * (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ) -
              q * (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)) =
          q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ) -
                q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) +
              (q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
                q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ)) +
            (q * (∑ n in Finset.range N,
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ) -
              q * (∑ n in Finset.range N,
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ)) :=
      Complex.finiteAbelPlana_vertical_telescope_scale
        q
        (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ)
        (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ)
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ)
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)
        (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ)
        (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ)
        (∑ n in Finset.range N,
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ)
        (∑ n in Finset.range N,
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ)
        hvertical_normalized
    have hstrip_right :
        q * (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ) =
            ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ) :=
      Finset.mul_sum
        (s := Complex.finiteAbelPlanaVerticalStripIndexSet N)
        (f := fun k =>
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ)
        q
    have hstrip_left :
        q * (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ) =
            ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ) :=
      Finset.mul_sum
        (s := Complex.finiteAbelPlanaVerticalStripIndexSet N)
        (f := fun k =>
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)
        q
    have hinterior_left :
        q * (∑ n in Finset.range N,
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ) =
            ∑ n in Finset.range N,
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ) :=
      Finset.mul_sum
        (s := Finset.range N)
        (f := fun n =>
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ)
        q
    have hinterior_right :
        q * (∑ n in Finset.range N,
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ) =
            ∑ n in Finset.range N,
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ) :=
      Finset.mul_sum
        (s := Finset.range N)
        (f := fun n =>
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ)
        q
    exact hstrip_right ▸ hstrip_left ▸ hinterior_left ▸ hinterior_right ▸ hraw
  have halgebra :
      (q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
              q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ) -
          q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ)) +
            (q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
                q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
            q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ)) +
          ((∑ n in Finset.range N,
              q * Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) -
                (∑ n in Finset.range N,
                  q * Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) +
              (∑ n in Finset.range N,
                q * (Complex.I *
                  Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ)) -
            ∑ n in Finset.range N,
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ)) =
        ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
            (q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
                q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
              ∑ n in Finset.range N,
                q * Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) -
          ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                q * Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
              (q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                  q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                ∑ n in Finset.range N,
                  q * Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ)) +
          (q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
            q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ))) -
        ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) -
          (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
          (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ)) -
          ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
            q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)) :=
    Complex.finiteAbelPlana_normalized_capCollar_assembly_algebra
      (q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ)
      (q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ)
      (q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ))
      (q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ))
      (q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ)
      (q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ)
      (q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ))
      (q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ))
      (∑ n in Finset.range N,
        q * Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ)
      (∑ n in Finset.range N,
        q * Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ)
      (∑ n in Finset.range N,
        q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ))
      (∑ n in Finset.range N,
        q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ))
      (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        q * Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ)
      (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        q * Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ)
      (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ))
      (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ))
      hvertical_scaled
  have hleft_endpoint :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarBoundary w T ρ =
        q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
              q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ) -
          q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) := by
    calc
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarBoundary w T ρ =
          q *
            (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
              Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) := rfl
      _ =
          q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
                q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ) -
            q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) :=
        Complex.finiteAbelPlana_normalized_four_term_expand
          q
          (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ)
          (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ)
          (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ)
          (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ)
  have hright_endpoint :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary N w T ρ =
        q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
              q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
          q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ) := by
    calc
      Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary N w T ρ =
          q *
            (Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
              Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ) := rfl
      _ =
          q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
                q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
            q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ) :=
        Complex.finiteAbelPlana_normalized_four_term_expand
          q
          (Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ)
          (Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ)
          (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ)
          (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ)
  have hinterior :
      Complex.finiteAbelPlanaLogInteriorCapCollarBoundaryContribution N w T ρ =
          (∑ n in Finset.range N,
              q * Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) -
                (∑ n in Finset.range N,
                  q * Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) +
              (∑ n in Finset.range N,
                q * (Complex.I *
                  Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ)) -
            ∑ n in Finset.range N,
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ) := by
    calc
      Complex.finiteAbelPlanaLogInteriorCapCollarBoundaryContribution N w T ρ =
          ∑ n in Finset.range N,
            q *
              (Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ -
                Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ +
                  Complex.I *
                    Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
                Complex.I *
                  Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ) := rfl
      _ =
          (∑ n in Finset.range N,
              q * Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) -
                (∑ n in Finset.range N,
                  q * Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) +
              (∑ n in Finset.range N,
                q * (Complex.I *
                  Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ)) -
            ∑ n in Finset.range N,
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ) :=
        Complex.finiteAbelPlana_normalized_four_term_sum_expand
          (Finset.range N)
          q
          (fun n => Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ)
          (fun n => Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ)
          (fun n =>
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ)
          (fun n =>
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ)
  have hleft :
      Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ =
        (q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
                q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ) -
            q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ)) +
              (q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
                  q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ)) +
            ((∑ n in Finset.range N,
                q * Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) -
                  (∑ n in Finset.range N,
                    q * Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) +
                (∑ n in Finset.range N,
                  q * (Complex.I *
                    Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ)) -
              ∑ n in Finset.range N,
                q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ)) := by
    calc
      Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ =
          (Complex.finiteAbelPlanaLogLeftEndpointCapCollarBoundary w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary N w T ρ) +
            Complex.finiteAbelPlanaLogInteriorCapCollarBoundaryContribution N w T ρ := rfl
      _ =
          (q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
                  q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ) -
              q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) +
            Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary N w T ρ) +
            Complex.finiteAbelPlanaLogInteriorCapCollarBoundaryContribution N w T ρ := by
        exact congrArg
          (fun z : ℂ =>
            (z + Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary N w T ρ) +
              Complex.finiteAbelPlanaLogInteriorCapCollarBoundaryContribution N w T ρ)
          hleft_endpoint
      _ =
          (q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
                  q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ) -
              q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) +
            (q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
                    q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                  q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
                q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ))) +
            Complex.finiteAbelPlanaLogInteriorCapCollarBoundaryContribution N w T ρ := by
        exact congrArg
          (fun z : ℂ =>
            (q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
                    q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                  q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ) -
                q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) + z) +
              Complex.finiteAbelPlanaLogInteriorCapCollarBoundaryContribution N w T ρ)
          hright_endpoint
      _ =
          (q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
                  q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ) -
              q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) +
            (q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
                    q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                  q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
                q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ))) +
            ((∑ n in Finset.range N,
                q * Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) -
                  (∑ n in Finset.range N,
                    q * Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) +
                (∑ n in Finset.range N,
                  q * (Complex.I *
                    Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ)) -
              ∑ n in Finset.range N,
                q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ)) := by
        exact congrArg
          (fun z : ℂ =>
            (q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
                    q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                  q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ) -
                q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) +
              (q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
                      q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                    q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
                  q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ))) + z)
          hinterior
  have hright :
      ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
            (q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
                q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
              ∑ n in Finset.range N,
                q * Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) -
          ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                q * Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
              (q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                  q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                ∑ n in Finset.range N,
                  q * Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ)) +
          (q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
            q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ))) -
        ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) -
          (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
          (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ)) -
          ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
            q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)) =
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ := by
    have hlower_collar :
        q *
            (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
              Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
                ∑ n in Finset.range N,
                  Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) =
          q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
              q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
            ∑ n in Finset.range N,
              q * Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ := by
      have hsum :
          q * (∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) =
              ∑ n in Finset.range N,
                q * Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ :=
        Finset.mul_sum
          (s := Finset.range N)
          (f := fun n => Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ)
          q
      calc
        q *
            (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
              Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
                ∑ n in Finset.range N,
                  Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) =
            q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
                q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
              q * (∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) :=
          Complex.finiteAbelPlana_normalized_three_term_expand
            q
            (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ)
            (Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ)
            (∑ n in Finset.range N,
              Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ)
        _ =
            q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
                q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
              ∑ n in Finset.range N,
                q * Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ := by
          exact congrArg
            (fun z : ℂ =>
              q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
                  q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ + z)
            hsum
    have hupper_collar :
        q *
            (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
              Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                ∑ n in Finset.range N,
                  Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) =
          q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
              q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            ∑ n in Finset.range N,
              q * Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ := by
      have hsum :
          q * (∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) =
              ∑ n in Finset.range N,
                q * Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ :=
        Finset.mul_sum
          (s := Finset.range N)
          (f := fun n => Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ)
          q
      calc
        q *
            (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
              Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                ∑ n in Finset.range N,
                  Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) =
            q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              q * (∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) :=
          Complex.finiteAbelPlana_normalized_three_term_expand
            q
            (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ)
            (Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ)
            (∑ n in Finset.range N,
              Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ)
        _ =
            q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              ∑ n in Finset.range N,
                q * Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ := by
          exact congrArg
            (fun z : ℂ =>
              q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                  q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ + z)
            hsum
    have hlower_scaled :
        q * Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
          (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
            (q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
                q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
              ∑ n in Finset.range N,
                q * Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) := by
      have hstrip :
          q * (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
            Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) =
              ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                q * Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ :=
        Finset.mul_sum
          (s := Complex.finiteAbelPlanaVerticalStripIndexSet N)
          (f := fun k => Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ)
          q
      calc
        q * Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
            q *
              ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
                (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
                  Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
                    ∑ n in Finset.range N,
                      Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ)) := by
          exact congrArg (fun z : ℂ => q * z) hlower
        _ =
            q * (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
              q *
                (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
                  Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
                    ∑ n in Finset.range N,
                      Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) :=
          mul_add q
            (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ)
            (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
              Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
                ∑ n in Finset.range N,
                  Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ)
        _ =
            (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                q * Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
              q *
                (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
                  Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
                    ∑ n in Finset.range N,
                      Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) := by
          exact congrArg
            (fun z : ℂ =>
              z +
                q *
                  (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
                    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
                      ∑ n in Finset.range N,
                        Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ))
            hstrip
        _ =
            (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                q * Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
              (q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
                  q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
                ∑ n in Finset.range N,
                  q * Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) := by
          exact congrArg
            (fun z : ℂ =>
              (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                q * Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) + z)
            hlower_collar
    have hupper_scaled :
        q * Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
          (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
            (q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              ∑ n in Finset.range N,
                q * Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) := by
      have hstrip :
          q * (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
            Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) =
              ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                q * Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ :=
        Finset.mul_sum
          (s := Complex.finiteAbelPlanaVerticalStripIndexSet N)
          (f := fun k => Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ)
          q
      calc
        q * Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
            q *
              ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
                (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                  Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                    ∑ n in Finset.range N,
                      Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ)) := by
          exact congrArg (fun z : ℂ => q * z) hupper
        _ =
            q * (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
              q *
                (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                  Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                    ∑ n in Finset.range N,
                      Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) :=
          mul_add q
            (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ)
            (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
              Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                ∑ n in Finset.range N,
                  Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ)
        _ =
            (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                q * Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
              q *
                (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                  Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                    ∑ n in Finset.range N,
                      Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) := by
          exact congrArg
            (fun z : ℂ =>
              z +
                q *
                  (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                    Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                      ∑ n in Finset.range N,
                        Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ))
            hstrip
        _ =
            (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                q * Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
              (q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                  q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                ∑ n in Finset.range N,
                  q * Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) := by
          exact congrArg
            (fun z : ℂ =>
              (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                q * Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) + z)
            hupper_collar
    have hrect :
        ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                q * Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
              (q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
                  q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
                ∑ n in Finset.range N,
                  q * Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) -
            ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                  q * Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
                (q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                    q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                  ∑ n in Finset.range N,
                    q * Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ)) +
            (q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
              q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ))) =
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ := by
      calc
        ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                q * Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
              (q * Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
                  q * Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
                ∑ n in Finset.range N,
                  q * Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) -
            ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
                  q * Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
                (q * Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
                    q * Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
                  ∑ n in Finset.range N,
                    q * Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ)) +
            (q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
              q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ))) =
            (q * Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T -
              q * Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T) +
            (q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
              q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ)) := by
          exact congrArg₂
            (fun a b : ℂ =>
              (a - b) +
                (q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ) -
                  q * (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ)))
            hlower_scaled.symm
            hupper_scaled.symm
        _ =
            q *
              ((Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T -
                  Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T) +
                (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
                  Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ)) := by
          exact
            (Complex.finiteAbelPlana_normalized_rectangle_pair_expand
              q
              (Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T)
              (Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T)
              (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ)
              (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ)).symm
        _ =
            Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ := rfl
    have hstrip :
        ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) -
          (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
          (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ)) -
          ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
            q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)) =
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ := by
      calc
        ((∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) -
          (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
          (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ)) -
          ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
            q * (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)) =
            ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
              q *
                (Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ -
                  Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ +
                    Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
                  Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ) := by
          exact
            (Complex.finiteAbelPlana_normalized_four_term_sum_expand
              (Complex.finiteAbelPlanaVerticalStripIndexSet N)
              q
              (fun k => Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ)
              (fun k => Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ)
              (fun k => Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ)
              (fun k => Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)).symm
        _ =
            Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ := rfl
    exact congrArg₂ HSub.hSub hrect hstrip
  exact hleft.trans (halgebra.trans hright)

/-- Raw cap/collar accounting before applying the residue normalization.

This is the assembly of the lower-horizontal partition, upper-horizontal
partition, and vertical-side telescoping theorem. -/
theorem Complex.finiteAbelPlana_log_concreteCapCollarBoundaryContribution_eq_pvNormalized_sub_verticalStripBoundarySum
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
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ =
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ := by
  have hlower :
      Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) :=
    Complex.finiteAbelPlana_log_lowerHorizontalSide_eq_verticalStrips_add_capCollars
      N T hT hρ hdeleted_geometry hcont
  have hupper :
      Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) :=
    Complex.finiteAbelPlana_log_upperHorizontalSide_eq_verticalStrips_add_capCollars
      N T hT hρ hdeleted_geometry hcont
  have hvertical :
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
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ) :=
    Complex.finiteAbelPlana_log_verticalPVSide_sub_verticalStrips_eq_capCollars
      N w T ρ
  exact
    Complex.finiteAbelPlana_concreteCapCollarBoundaryContribution_eq_pvNormalized_sub_verticalStripBoundarySum_of_sides
      N T ρ hlower hupper hvertical

/-- Boundary contribution of the cap/collar subdomains omitted by the vertical
gap strips.

The vertical safe strips alone do not cover the finite punctured rectangle.
This term records the ordinary cap/collar subdomain boundaries around the
deleted disks.  With this term included, the subdivision has the same outer
boundary as the named principal-value punctured rectangle. -/
noncomputable def Complex.finiteAbelPlanaLogCapCollarBoundaryContribution
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
    Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ

/-- The concrete endpoint and interior cap/collar rectangles assemble to the
abstract cap/collar correction.

This is the remaining collar-accounting theorem: split the lower and upper
outer horizontal sides into safe-strip intervals and deleted-disk collar
intervals, telescope the adjacent vertical strip sides, and identify the
surviving endpoint principal-value vertical pieces. -/
theorem Complex.finiteAbelPlana_log_concreteCapCollarBoundaryContribution_eq_capCollarBoundaryContribution
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
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ =
      Complex.finiteAbelPlanaLogCapCollarBoundaryContribution N w T ρ := by
  calc
    Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ =
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
          Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ := by
      exact
        Complex.finiteAbelPlana_log_concreteCapCollarBoundaryContribution_eq_pvNormalized_sub_verticalStripBoundarySum
          N T hT hρ hdeleted_geometry hcont
    _ =
        Complex.finiteAbelPlanaLogCapCollarBoundaryContribution N w T ρ := by
      rfl

/-- Full finite-hole subdivision boundary: vertical gap strips, cap/collar
subdomains, and deleted arcs with punctured-domain orientation. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
      Complex.finiteAbelPlanaLogCapCollarBoundaryContribution N w T ρ -
    Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ

/-- Concrete finite-hole subdivision boundary, before the concrete cap/collar
sum is identified with the abstract cap/collar correction. -/
noncomputable def Complex.finiteAbelPlanaLogConcreteFiniteHoleSubdivisionBoundary
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
      Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ -
    Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ

/-- Unfolding of the full finite-hole subdivision boundary. -/
theorem Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_unfold
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ =
      Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
          Complex.finiteAbelPlanaLogCapCollarBoundaryContribution N w T ρ -
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
  rfl

/-- Unfolding of the concrete finite-hole subdivision boundary. -/
theorem Complex.finiteAbelPlana_log_concreteFiniteHoleSubdivisionBoundary_unfold
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogConcreteFiniteHoleSubdivisionBoundary N w T ρ =
      Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
          Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ -
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
  rfl

/-- Replacing the concrete cap/collar sum by the abstract cap/collar
correction transports the concrete finite-hole boundary to the public
finite-hole subdivision boundary. -/
theorem Complex.finiteAbelPlana_log_concreteFiniteHoleSubdivisionBoundary_eq_finiteHoleSubdivisionBoundary
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
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogConcreteFiniteHoleSubdivisionBoundary N w T ρ =
      Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ := by
  calc
    Complex.finiteAbelPlanaLogConcreteFiniteHoleSubdivisionBoundary N w T ρ =
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
            Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ -
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      exact
        Complex.finiteAbelPlana_log_concreteFiniteHoleSubdivisionBoundary_unfold
          N w T ρ
    _ =
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
            Complex.finiteAbelPlanaLogCapCollarBoundaryContribution N w T ρ -
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      exact
        congrArg
          (fun z : ℂ =>
            Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ + z -
              Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ)
          (Complex.finiteAbelPlana_log_concreteCapCollarBoundaryContribution_eq_capCollarBoundaryContribution
            N T hT hρ hdeleted_geometry hcont)
    _ =
        Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ := by
      exact
        (Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_unfold
          N w T ρ).symm

/-- The full finite-hole subdivision boundary is the named finite-radius
punctured boundary. -/
theorem Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_eq_finiteRadiusPuncturedBoundary
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ =
      Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ := by
  calc
    Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ =
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
            (Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
              Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ) -
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      rfl
    _ =
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      exact Complex.finiteAbelPlana_boundary_sum_cancel_then_sub
        (Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ)
        (Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
        (Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ)
    _ =
        Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ := by
      exact
        (Complex.finiteAbelPlana_log_finiteRadiusPuncturedBoundaryIntegral_eq_pvNormalized_sub_deleted
          N w T ρ).symm

/-- The remaining outer-boundary accounting defect after the deleted-boundary
terms have been put on both sides.

This is the precise geometric object that must vanish after the cap/collar
subdomains near the deleted disks are included in the finite-hole strip
decomposition.  The vertical safe strips alone do not definitionally contain
those cap pieces. -/
noncomputable def Complex.finiteAbelPlanaLogStripOuterBoundaryDefect
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ -
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ

/-- Unfolding of the finite-hole outer-boundary accounting defect. -/
theorem Complex.finiteAbelPlana_log_stripOuterBoundaryDefect_unfold
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogStripOuterBoundaryDefect N w T ρ =
      Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ -
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ :=
  rfl

/-- Cancellation of a common right subtraction term. -/
theorem Complex.finiteAbelPlana_sub_right_cancel
    {a b c : ℂ}
    (h : a - c = b - c) :
    a = b := by
  have h_add :
      (a - c) + c = (b - c) + c :=
    congrArg (fun z : ℂ => z + c) h
  calc
    a = (a - c) + c :=
      (sub_add_cancel a c).symm
    _ = (b - c) + c :=
      h_add
    _ = b :=
      sub_add_cancel b c

/-- The strip-boundary/deleted-arc equality is exactly the vanishing of the
outer-boundary defect. -/
theorem Complex.finiteAbelPlana_log_stripBoundaryWithDeletedArcs_eq_finiteRadiusPuncturedBoundary_iff_outerBoundaryDefect_zero
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogStripBoundaryWithDeletedArcs N w T ρ =
       Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ ↔
      Complex.finiteAbelPlanaLogStripOuterBoundaryDefect N w T ρ = 0 := by
  constructor
  · intro hboundary
    have hstrip :
        Complex.finiteAbelPlanaLogStripBoundaryWithDeletedArcs N w T ρ =
          Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      exact
        Complex.finiteAbelPlana_log_stripBoundaryWithDeletedArcs_unfold
          N w T ρ
    have hpunctured :
        Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ =
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      exact
        Complex.finiteAbelPlana_log_finiteRadiusPuncturedBoundaryIntegral_eq_pvNormalized_sub_deleted
          N w T ρ
    have houter :
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ =
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      exact hstrip.symm.trans (hboundary.trans hpunctured)
    have houter_eq :
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ =
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ :=
      Complex.finiteAbelPlana_sub_right_cancel houter
    calc
      Complex.finiteAbelPlanaLogStripOuterBoundaryDefect N w T ρ =
          Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ -
            Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ :=
        Complex.finiteAbelPlana_log_stripOuterBoundaryDefect_unfold N w T ρ
      _ = 0 :=
        sub_eq_zero.mpr houter_eq
  · intro hdefect
    have houter :
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ =
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ := by
      have hdefect_unfolded :
          Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ -
              Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ =
            0 :=
        Eq.mp
          (congrArg
            (fun z : ℂ => z = 0)
            (Complex.finiteAbelPlana_log_stripOuterBoundaryDefect_unfold N w T ρ))
          hdefect
      exact sub_eq_zero.mp hdefect_unfolded
    calc
      Complex.finiteAbelPlanaLogStripBoundaryWithDeletedArcs N w T ρ =
          Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
        exact
          Complex.finiteAbelPlana_log_stripBoundaryWithDeletedArcs_unfold
            N w T ρ
      _ =
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
        exact
          congrArg
            (fun z : ℂ =>
              z - Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ)
            houter
      _ =
          Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ := by
        exact
          (Complex.finiteAbelPlana_log_finiteRadiusPuncturedBoundaryIntegral_eq_pvNormalized_sub_deleted
            N w T ρ).symm

/-- Vanishing of the outer-boundary defect gives the boundary-identification
half of the finite-hole decomposition. -/
theorem Complex.finiteAbelPlana_log_stripBoundaryWithDeletedArcs_eq_finiteRadiusPuncturedBoundary_of_outerBoundaryDefect_zero
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ)
    (hdefect :
      Complex.finiteAbelPlanaLogStripOuterBoundaryDefect N w T ρ = 0) :
    Complex.finiteAbelPlanaLogStripBoundaryWithDeletedArcs N w T ρ =
      Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ :=
  (Complex.finiteAbelPlana_log_stripBoundaryWithDeletedArcs_eq_finiteRadiusPuncturedBoundary_iff_outerBoundaryDefect_zero
    N w T ρ).2 hdefect

/-- The full finite-hole subdivision boundary is the named finite-radius
punctured boundary. -/
theorem Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_eq_finiteRadiusPuncturedBoundary_owner
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
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
    Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ =
      Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ := by
  exact
    Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_eq_finiteRadiusPuncturedBoundary
      N w T ρ


end

end LFunctions
end Boundary
