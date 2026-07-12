import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.DyadicBlocks
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCurvatureLower

/-!
# Two-sided logarithmic curvature on canonical dyadic blocks

This file specializes the general endpoint lower and upper curvature theorems
to the actual finite dyadic blocks used by the prefix decomposition.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The left endpoint of every canonical dyadic block is positive. -/
theorem Nat.one_le_dyadicBlockLeft (j : ℕ) :
    1 ≤ Nat.dyadicBlockLeft j := by
  exact Nat.one_le_pow j 2 (Nat.zero_lt_succ 1)

/-- A nonempty dyadic block has ordered inclusive endpoints. -/
theorem Nat.dyadicBlockLeft_le_upper
    {N j : ℕ}
    (hnonempty :
      Nat.dyadicBlockLeft j <
        min (N + 1) (Nat.dyadicBlockRightExclusive j)) :
    Nat.dyadicBlockLeft j ≤ Nat.dyadicBlockUpper N j := by
  have hsuccessor :
      Nat.dyadicBlockLeft j + 1 ≤
        min (N + 1) (Nat.dyadicBlockRightExclusive j) :=
    Nat.succ_le_of_lt hnonempty
  exact Nat.le_sub_of_add_le hsuccessor

/-- A nonempty dyadic block has its exclusive endpoint at most twice its left
endpoint. -/
theorem Nat.dyadicBlockUpper_add_one_le_two_mul_left
    {N j : ℕ}
    (hnonempty :
      Nat.dyadicBlockLeft j <
        min (N + 1) (Nat.dyadicBlockRightExclusive j)) :
    Nat.dyadicBlockUpper N j + 1 ≤
      2 * Nat.dyadicBlockLeft j := by
  have hendpoint :
      Nat.dyadicBlockUpper N j + 1 =
        min (N + 1) (Nat.dyadicBlockRightExclusive j) :=
    Nat.dyadicBlockUpper_add_one_eq_truncatedRight hnonempty
  exact
    Eq.subst
      (motive := fun left : ℕ =>
        left ≤ 2 * Nat.dyadicBlockLeft j)
      hendpoint.symm
      (Nat.dyadicBlock_truncatedRight_le_two_mul_left N j)

/-- Explicit square identity behind the factor-four curvature comparison. -/
theorem Real.two_mul_sq_eq_four_mul_sq
    (A : ℝ) :
    (2 * A) * (2 * A) = 4 * (A * A) := by
  have hrearrange :
      (2 * A) * (2 * A) = (2 * 2) * (A * A) :=
    mul_mul_mul_comm 2 A 2 A
  have htwo_mul_two : (2 : ℝ) * 2 = 4 := by
    have hnat : (2 * 2 : ℕ) = 4 :=
      rfl
    exact Eq.trans
      (Nat.cast_mul 2 2).symm
      (Eq.trans
        (congrArg (fun n : ℕ => (n : ℝ)) hnat)
        Nat.cast_ofNat)
  exact Eq.trans hrearrange
    (congrArg (fun coefficient : ℝ => coefficient * (A * A)) htwo_mul_two)

/-- Reciprocal-square comparison for endpoints satisfying `B ≤ 2A`. -/
theorem Real.inv_sq_le_four_mul_inv_sq_of_le_two_mul
    {A B : ℝ}
    (hA : 0 < A)
    (hB : 0 < B)
    (hBA : B ≤ 2 * A) :
    (A * A)⁻¹ ≤ 4 * (B * B)⁻¹ := by
  have hA_nonneg : 0 ≤ A :=
    le_of_lt hA
  have hB_nonneg : 0 ≤ B :=
    le_of_lt hB
  have htwoA_nonneg : 0 ≤ 2 * A :=
    mul_nonneg zero_le_two hA_nonneg
  have hBB_le_twoA_sq :
      B * B ≤ (2 * A) * (2 * A) :=
    mul_le_mul hBA hBA hB_nonneg htwoA_nonneg
  have hBB_le_fourAA :
      B * B ≤ 4 * (A * A) :=
    Eq.subst
      (motive := fun right : ℝ => B * B ≤ right)
      (Real.two_mul_sq_eq_four_mul_sq A)
      hBB_le_twoA_sq
  have hAA_pos : 0 < A * A :=
    mul_pos hA hA
  have hBB_pos : 0 < B * B :=
    mul_pos hB hB
  have hcross :
      (1 : ℝ) * (B * B) ≤ 4 * (A * A) :=
    Eq.subst
      (motive := fun left : ℝ => left ≤ 4 * (A * A))
      (one_mul (B * B)).symm
      hBB_le_fourAA
  have hdivision :
      (1 : ℝ) / (A * A) ≤ 4 / (B * B) :=
    (div_le_div_iff₀ hAA_pos hBB_pos).mpr hcross
  have hleft :
      (A * A)⁻¹ = (1 : ℝ) / (A * A) :=
    (one_div (A * A)).symm
  have hright :
      4 * (B * B)⁻¹ = 4 / (B * B) :=
    (div_eq_mul_inv 4 (B * B)).symm
  exact
    Eq.subst
      (motive := fun left : ℝ => left ≤ 4 * (B * B)⁻¹)
      hleft.symm
      (Eq.subst
        (motive := fun right : ℝ => (1 : ℝ) / (A * A) ≤ right)
        hright.symm
        hdivision)

/-- The upper logarithmic curvature scale is at most four times the lower
scale whenever the block endpoints satisfy `b+1 ≤ 2a`. -/
theorem Real.logarithmicCurvature_upperScale_le_four_mul_lowerScale
    (T : ℝ)
    (hT : 0 ≤ T)
    {A B : ℝ}
    (hA : 0 < A)
    (hB : 0 < B)
    (hBA : B ≤ 2 * A) :
    T * (A * A)⁻¹ ≤ 4 * (T * (B * B)⁻¹) := by
  have hinverse :
      (A * A)⁻¹ ≤ 4 * (B * B)⁻¹ :=
    Real.inv_sq_le_four_mul_inv_sq_of_le_two_mul hA hB hBA
  have hscaled :
      T * (A * A)⁻¹ ≤ T * (4 * (B * B)⁻¹) :=
    mul_le_mul_of_nonneg_left hinverse hT
  have hreassociate :
      T * (4 * (B * B)⁻¹) = 4 * (T * (B * B)⁻¹) := by
    calc
      T * (4 * (B * B)⁻¹) = (T * 4) * (B * B)⁻¹ :=
        (mul_assoc T 4 (B * B)⁻¹).symm
      _ = (4 * T) * (B * B)⁻¹ := by
        exact congrArg (fun coefficient : ℝ => coefficient * (B * B)⁻¹)
          (mul_comm T 4)
      _ = 4 * (T * (B * B)⁻¹) :=
        mul_assoc 4 T (B * B)⁻¹
  exact le_trans hscaled (le_of_eq hreassociate)

/-- Canonical factor-four comparison between the two endpoint curvature
scales of a nonempty dyadic block. -/
theorem Real.logarithmicCurvature_dyadic_upperScale_le_four_mul_lowerScale
    (T : ℝ)
    (hT : 0 ≤ T)
    {N j : ℕ}
    (hnonempty :
      Nat.dyadicBlockLeft j <
        min (N + 1) (Nat.dyadicBlockRightExclusive j)) :
    T *
        (((((Nat.dyadicBlockLeft j : ℕ) : ℝ) *
          ((Nat.dyadicBlockLeft j : ℕ) : ℝ)))⁻¹) ≤
      4 *
        (T *
          (((((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ) *
            ((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ)))⁻¹)) := by
  let A : ℝ := ((Nat.dyadicBlockLeft j : ℕ) : ℝ)
  let B : ℝ := ((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ)
  have hA_nat : 0 < Nat.dyadicBlockLeft j :=
    Nat.lt_of_succ_le (Nat.one_le_dyadicBlockLeft j)
  have hA : 0 < A :=
    Nat.cast_pos.mpr hA_nat
  have hB_nat : 0 < Nat.dyadicBlockUpper N j + 1 :=
    Nat.succ_pos (Nat.dyadicBlockUpper N j)
  have hB : 0 < B :=
    Nat.cast_pos.mpr hB_nat
  have hBA_nat :
      Nat.dyadicBlockUpper N j + 1 ≤
        2 * Nat.dyadicBlockLeft j :=
    Nat.dyadicBlockUpper_add_one_le_two_mul_left hnonempty
  have hBA_cast :
      (((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ)) ≤
        (((2 * Nat.dyadicBlockLeft j : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hBA_nat
  have hcast_mul :
      (((2 * Nat.dyadicBlockLeft j : ℕ) : ℝ)) =
        2 * ((Nat.dyadicBlockLeft j : ℕ) : ℝ) :=
    Nat.cast_mul 2 (Nat.dyadicBlockLeft j)
  have hBA : B ≤ 2 * A :=
    Eq.subst
      (motive := fun right : ℝ => B ≤ right)
      hcast_mul
      hBA_cast
  exact
    Real.logarithmicCurvature_upperScale_le_four_mul_lowerScale
      T hT hA hB hBA

/-- Exact two-sided second-derivative curvature data on one nonempty canonical
dyadic block.  The lower scale uses the truncated right endpoint and the upper
scale uses the power-of-two left endpoint. -/
theorem Complex.logarithmicPhaseRealPhase_dyadicBlock_twoSidedCurvature
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {N j : ℕ}
    (hnonempty :
      Nat.dyadicBlockLeft j <
        min (N + 1) (Nat.dyadicBlockRightExclusive j)) :
    (∀ x : ℝ,
      x ∈ Set.Icc
          ((Nat.dyadicBlockLeft j : ℕ) : ℝ)
          (((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ)) →
        ‖t‖ *
            (((((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ) *
              ((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ)))⁻¹) ≤
          ‖deriv
            (deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
            x‖) ∧
      (∀ x : ℝ,
        x ∈ Set.Icc
            ((Nat.dyadicBlockLeft j : ℕ) : ℝ)
            (((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ)) →
          ‖deriv
              (deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
              x‖ ≤
            ‖t‖ *
              (((((Nat.dyadicBlockLeft j : ℕ) : ℝ) *
                ((Nat.dyadicBlockLeft j : ℕ) : ℝ)))⁻¹)) := by
  let a : ℕ := Nat.dyadicBlockLeft j
  let b : ℕ := Nat.dyadicBlockUpper N j
  have ha : 1 ≤ a :=
    Nat.one_le_dyadicBlockLeft j
  have hab : a ≤ b :=
    Nat.dyadicBlockLeft_le_upper hnonempty
  have hlower :=
    Complex.logarithmicPhaseRealPhase_secondDerivative_curvature_lower
      t ht ha hab
  have hupper :=
    Complex.logarithmicPhaseRealPhase_secondDerivative_curvature_upper
      t (b := b) ha
  exact And.intro hlower hupper

end

end LFunctions
end Boundary
