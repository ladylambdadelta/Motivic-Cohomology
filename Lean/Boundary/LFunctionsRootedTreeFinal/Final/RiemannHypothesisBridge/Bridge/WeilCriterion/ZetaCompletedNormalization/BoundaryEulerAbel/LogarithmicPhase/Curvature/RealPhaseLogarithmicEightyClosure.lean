import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicExclusiveFiniteLedger
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicExactPositiveTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicSharpFarNegativeSeries
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicSharpBProcessBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicExactActiveClosure

/-!
# Exact closure of the logarithmic B-process at eighty

The complete active coefficient is `55`.  The far-negative series is charged
honestly, including its first lattice packet: its square and two residual-cubic
parts cost `5 / 2`, `1 / 4`, and `1 / 4`, while its quartic part costs
one square-root unit.  Thus the full negative tail costs four refined-scale
units, leaving a strict margin below `80` after the exact positive tail.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseEightySquareRootCoefficient : ℝ :=
  55 + 121 / 18 + 2 / 3 +
    (4 + Complex.logarithmicPhaseExactPositiveTailConstant)

def Complex.logarithmicPhaseEightyTwoComponentLedger
    (t : ℝ) (b : ℕ) : ℝ :=
  3 * Real.logarithmicPhaseEndpointComponent t b +
    Complex.logarithmicPhaseEightySquareRootCoefficient *
      Real.logarithmicPhaseSquareRootComponent t

theorem Complex.logarithmicPhaseBProcessClosedInteriorMajorant_le_one_hundred_one_thirds_scale_of_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessClosedInteriorMajorant
        t (a : ℤ) (b : ℤ) ≤
      (101 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  let S := Complex.logarithmicPhaseBProcessScale t
  have hexpand :=
    Complex.logarithmicPhaseBProcessClosedInteriorMajorant_eq_eight_products
      t (a : ℤ) (b : ℤ)
  have hxC := Complex.two_mul_crossingScalar_le_three_mul_scale t
  have hxL := Complex.two_mul_tailScalar_le_eight_mul_scale_of_nonempty
    ht hgeometry hnonempty
  have hxM := Complex.two_mul_centralScalar_le_eight_mul_scale_of_nonempty
    ht hgeometry hnonempty
  have hyC :=
    Complex.sharpFrequencyScalar_mul_crossingScalar_le_two_thirds_scale
      hgeometry
  have hyL :=
    Complex.sharpFrequencyScalar_mul_tailScalar_le_two_scale ht hgeometry
  have hyM :=
    Complex.sharpFrequencyScalar_mul_centralScalar_le_two_scale hgeometry
  have hcomponents := Real.add_two_four_term_bounds
    hxC hxL hxM hxL hyC hyL hyM hyL
  have hweighted :
      (3 * S + 8 * S + 8 * S + 8 * S) +
          ((2 / 3) * S + 2 * S + 2 * S + 2 * S) =
        (101 / 3) * S := by
    exact Eq.trans
      (Real.two_four_weighted_terms_eq_sum_coeff_mul
        3 8 8 8 (2 / 3) 2 2 2 S)
      (congrArg (fun coefficient : ℝ => coefficient * S)
        Real.sharp_frequency_active_coefficient_sum_eq_one_hundred_one_thirds)
  exact Eq.subst (motive := fun value : ℝ => value ≤ (101 / 3) * S)
    hexpand.symm (le_trans hcomponents (le_of_eq hweighted))

theorem Complex.logarithmicPhaseBProcessCompleteActiveBudget_le_fifty_five_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessCompleteActiveBudget
        t (a : ℤ) (b : ℤ) ≤
      55 * Complex.logarithmicPhaseBProcessScale t := by
  match Complex.logarithmicPhasePoissonBProcessInteriorModes_empty_or_nonempty
    t (a : ℤ) (b : ℤ) with
  | Or.inl hinteriorEmpty =>
      have hinteriorZero :=
        Complex.logarithmicPhaseBProcessInteriorBudget_eq_zero_of_empty
          t (a : ℤ) (b : ℤ) hinteriorEmpty
      have hendpoint :
          Complex.logarithmicPhaseBProcessUniversalEndpointBudget
              t (a : ℤ) (b : ℤ) ≤
            (112 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
        match
          (Complex.logarithmicPhasePoissonBProcessEndpointModes
            t (a : ℤ) (b : ℤ)).eq_empty_or_nonempty with
        | Or.inl hendpointEmpty =>
            have hzero :=
              Complex.logarithmicPhaseBProcessEndpointBudget_eq_zero_of_empty
                t (a : ℤ) (b : ℤ) hendpointEmpty
            exact Eq.subst (motive := fun value : ℝ => value ≤ _)
              hzero.symm
              (mul_nonneg
                (div_nonneg (Nat.cast_nonneg 112) (Nat.cast_nonneg 3))
                (Complex.logarithmicPhaseBProcessScale_nonneg t))
        | Or.inr hendpointNonempty =>
            exact
              Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_one_hundred_twelve_thirds_scale_of_endpoint_nonempty
                ht hgeometry hendpointNonempty
      have hfiftyFiveTimesThree : (55 : ℝ) * 3 = 165 := by
        have hnat : (55 * 3 : ℕ) = 165 := rfl
        exact Eq.trans (Nat.cast_mul 55 3).symm
          (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
            Nat.cast_ofNat)
      have honeHundredTwelvePlusFiftyThree :
          (112 : ℝ) + 53 = 165 := by
        have hnat : (112 + 53 : ℕ) = 165 := rfl
        exact Eq.trans (Nat.cast_add 112 53).symm
          (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
            Nat.cast_ofNat)
      have honeHundredTwelveLeOneHundredSixtyFive :
          (112 : ℝ) ≤ 165 :=
        (le_add_of_nonneg_right (Nat.cast_nonneg 53)).trans_eq
          honeHundredTwelvePlusFiftyThree
      have hcoefficient : (112 / 3 : ℝ) ≤ 55 :=
        (div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos 2))).mpr
          (honeHundredTwelveLeOneHundredSixtyFive.trans_eq
            hfiftyFiveTimesThree.symm)
      have henlarge := mul_le_mul_of_nonneg_right hcoefficient
        (Complex.logarithmicPhaseBProcessScale_nonneg t)
      unfold Complex.logarithmicPhaseBProcessCompleteActiveBudget
      have hzeroEndpoint :
          0 + Complex.logarithmicPhaseBProcessUniversalEndpointBudget
              t (a : ℤ) (b : ℤ) ≤
            55 * Complex.logarithmicPhaseBProcessScale t :=
        Eq.subst (motive := fun value : ℝ =>
            value ≤ 55 * Complex.logarithmicPhaseBProcessScale t)
          (zero_add
            (Complex.logarithmicPhaseBProcessUniversalEndpointBudget
              t (a : ℤ) (b : ℤ))).symm
          (le_trans hendpoint henlarge)
      exact Eq.subst (motive := fun value : ℝ => value + _ ≤ _)
        hinteriorZero.symm hzeroEndpoint
  | Or.inr hinteriorNonempty =>
      have hinteriorClosed :=
        Complex.logarithmicPhaseBProcessInteriorBudget_le_closedMajorant
          t ht (a : ℤ) (b : ℤ)
          (Int.ofNat_le.mpr
            (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
          (Int.ofNat_zero_le b)
      have hinterior := le_trans hinteriorClosed
        (Complex.logarithmicPhaseBProcessClosedInteriorMajorant_le_one_hundred_one_thirds_scale_of_nonempty
          ht hgeometry hinteriorNonempty)
      have hendpoint :=
        Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_sixty_four_thirds_scale_of_interior_nonempty
          ht hgeometry hinteriorNonempty
      unfold Complex.logarithmicPhaseBProcessCompleteActiveBudget
      have hsum := add_le_add hinterior hendpoint
      have hnumeratorSum : (101 : ℝ) + 64 = 165 := by
        have hnat : (101 + 64 : ℕ) = 165 := rfl
        exact Eq.trans (Nat.cast_add 101 64).symm
          (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
            Nat.cast_ofNat)
      have hfiftyFiveTimesThree : (55 : ℝ) * 3 = 165 := by
        have hnat : (55 * 3 : ℕ) = 165 := rfl
        exact Eq.trans (Nat.cast_mul 55 3).symm
          (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
            Nat.cast_ofNat)
      have honeHundredSixtyFiveThirds : (165 / 3 : ℝ) = 55 :=
        (div_eq_iff
          (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2)))).mpr
          hfiftyFiveTimesThree.symm
      have hcoefficient : (101 / 3 : ℝ) + 64 / 3 = 55 := by
        exact Eq.trans (div_add_div_same 101 64 3)
          (Eq.trans
            (congrArg (fun value : ℝ => value / 3) hnumeratorSum)
            honeHundredSixtyFiveThirds)
      exact le_trans hsum
        (le_of_eq
          (Eq.trans
            (add_mul (101 / 3 : ℝ) (64 / 3)
              (Complex.logarithmicPhaseBProcessScale t)).symm
            (congrArg
              (fun coefficient : ℝ => coefficient *
                Complex.logarithmicPhaseBProcessScale t)
              hcoefficient)))

theorem Complex.logarithmicPhaseExactPositiveTailConstant_le_twenty_seven_halves :
    Complex.logarithmicPhaseExactPositiveTailConstant ≤ 27 / 2 := by
  unfold Complex.logarithmicPhaseExactPositiveTailConstant
  have h4608Pos : (0 : ℝ) < 4608 :=
    Nat.cast_pos.mpr (Nat.succ_pos 4607)
  have htwoPos : (0 : ℝ) < 2 := zero_lt_two
  have hleft : (61683 : ℝ) * 2 = 123366 := by
    have hnat : (61683 * 2 : ℕ) = 123366 := rfl
    exact Eq.trans (Nat.cast_mul 61683 2).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hright : (27 : ℝ) * 4608 = 124416 := by
    have hnat : (27 * 4608 : ℕ) = 124416 := rfl
    exact Eq.trans (Nat.cast_mul 27 4608).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hnatLe : (123366 : ℕ) ≤ 124416 := by
    exact Eq.subst (motive := fun value : ℕ => 123366 ≤ value)
      (show 123366 + 1050 = 124416 from rfl)
      (Nat.le_add_right 123366 1050)
  have hrealLe : (123366 : ℝ) ≤ 124416 := Nat.cast_le.mpr hnatLe
  exact (div_le_div_iff₀ h4608Pos htwoPos).mpr
    (le_trans (le_of_eq hleft)
      (le_trans hrealLe (le_of_eq hright.symm)))

theorem Real.eighty_square_root_rational_ledger_le_eighty :
    (55 : ℝ) + 121 / 18 + 2 / 3 + (4 + 27 / 2) ≤ 80 := by
  have h18Ne : (18 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 17))
  have h9Ne : (9 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 8))
  have h55Product : (55 : ℝ) * 18 = 990 := by
    have hnat : (55 * 18 : ℕ) = 990 := rfl
    exact Eq.trans (Nat.cast_mul 55 18).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have h55 : (55 : ℝ) = 990 / 18 :=
    (eq_div_iff h18Ne).mpr h55Product
  have htwoThirds : (2 / 3 : ℝ) = 12 / 18 := by
    have h3Ne : (3 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
    have hleft : (2 : ℝ) * 18 = 36 := by
      have hnat : (2 * 18 : ℕ) = 36 := rfl
      exact Eq.trans (Nat.cast_mul 2 18).symm
        (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
          Nat.cast_ofNat)
    have hright : (12 : ℝ) * 3 = 36 := by
      have hnat : (12 * 3 : ℕ) = 36 := rfl
      exact Eq.trans (Nat.cast_mul 12 3).symm
        (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
          Nat.cast_ofNat)
    exact (div_eq_div_iff h3Ne h18Ne).mpr (Eq.trans hleft hright.symm)
  have h4Product : (4 : ℝ) * 18 = 72 := by
    have hnat : (4 * 18 : ℕ) = 72 := rfl
    exact Eq.trans (Nat.cast_mul 4 18).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have h4 : (4 : ℝ) = 72 / 18 := (eq_div_iff h18Ne).mpr h4Product
  have htwentySevenHalves : (27 / 2 : ℝ) = 243 / 18 := by
    have h2Ne : (2 : ℝ) ≠ 0 := ne_of_gt zero_lt_two
    have hleft : (27 : ℝ) * 18 = 486 := by
      have hnat : (27 * 18 : ℕ) = 486 := rfl
      exact Eq.trans (Nat.cast_mul 27 18).symm
        (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
          Nat.cast_ofNat)
    have hright : (243 : ℝ) * 2 = 486 := by
      have hnat : (243 * 2 : ℕ) = 486 := rfl
      exact Eq.trans (Nat.cast_mul 243 2).symm
        (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
          Nat.cast_ofNat)
    exact (div_eq_div_iff h2Ne h18Ne).mpr (Eq.trans hleft hright.symm)
  have hreplace :
      (55 : ℝ) + 121 / 18 + 2 / 3 + (4 + 27 / 2) =
        990 / 18 + 121 / 18 + 12 / 18 + (72 / 18 + 243 / 18) :=
    congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg₂ (fun left right : ℝ => left + right) h55 rfl)
        htwoThirds)
      (congrArg₂ (fun left right : ℝ => left + right)
        h4 htwentySevenHalves)
  have hfirst : (990 / 18 : ℝ) + 121 / 18 = (990 + 121) / 18 :=
    div_add_div_same (990 : ℝ) 121 18
  have hsecond : ((990 + 121 : ℝ) / 18) + 12 / 18 =
      ((990 + 121) + 12) / 18 :=
    div_add_div_same (990 + 121 : ℝ) 12 18
  have hthird : (72 / 18 : ℝ) + 243 / 18 = (72 + 243) / 18 :=
    div_add_div_same (72 : ℝ) 243 18
  have hfourth : (((990 + 121 : ℝ) + 12) / 18) +
      ((72 + 243 : ℝ) / 18) =
      (((990 + 121) + 12) + (72 + 243)) / 18 :=
    div_add_div_same ((990 + 121 : ℝ) + 12) (72 + 243) 18
  have hnumerator :
      (((990 + 121 : ℝ) + 12) + (72 + 243)) = 1438 := by
    have h990Add121 : (990 : ℝ) + 121 = 1111 :=
      Real.transition_nat_cast_add 990 121 1111 rfl
    have h1111Add12 : (1111 : ℝ) + 12 = 1123 :=
      Real.transition_nat_cast_add 1111 12 1123 rfl
    have h72Add243 : (72 : ℝ) + 243 = 315 :=
      Real.transition_nat_cast_add 72 243 315 rfl
    have h1123Add315 : (1123 : ℝ) + 315 = 1438 :=
      Real.transition_nat_cast_add 1123 315 1438 rfl
    exact Eq.trans
      (congrArg₂ (fun left right : ℝ => left + right)
        (Eq.trans
          (congrArg (fun value : ℝ => value + 12) h990Add121)
          h1111Add12)
        h72Add243)
      h1123Add315
  have hnormalized :
      (990 : ℝ) / 18 + 121 / 18 + 12 / 18 + (72 / 18 + 243 / 18) =
        (1438 : ℝ) / 18 :=
    Eq.trans
      (congrArg
        (fun value : ℝ => value + 12 / 18 + (72 / 18 + 243 / 18))
        hfirst)
      (Eq.trans
        (congrArg (fun value : ℝ => value + (72 / 18 + 243 / 18)) hsecond)
        (Eq.trans
          (congrArg
            (fun value : ℝ => ((990 + 121 : ℝ) + 12) / 18 + value)
            hthird)
          (Eq.trans hfourth
            (congrArg (fun value : ℝ => value / 18) hnumerator))))
  have hreduce : (1438 / 18 : ℝ) = 719 / 9 := by
    have hleft : (1438 : ℝ) * 9 = 12942 := by
      have hnat : (1438 * 9 : ℕ) = 12942 := rfl
      exact Eq.trans (Nat.cast_mul 1438 9).symm
        (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
          Nat.cast_ofNat)
    have hright : (719 : ℝ) * 18 = 12942 := by
      have hnat : (719 * 18 : ℕ) = 12942 := rfl
      exact Eq.trans (Nat.cast_mul 719 18).symm
        (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
          Nat.cast_ofNat)
    exact (div_eq_div_iff h18Ne h9Ne).mpr (Eq.trans hleft hright.symm)
  have h719Le720 : (719 : ℝ) ≤ 720 :=
    Nat.cast_le.mpr (Nat.le_succ 719)
  have h80Times9 : (80 : ℝ) * 9 = 720 := by
    have hnat : (80 * 9 : ℕ) = 720 := rfl
    exact Eq.trans (Nat.cast_mul 80 9).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have h719Ninths : (719 / 9 : ℝ) ≤ 80 :=
    (div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos 8))).mpr
      (Eq.subst (motive := fun value : ℝ => 719 ≤ value)
        h80Times9.symm h719Le720)
  exact le_trans
    (le_of_eq (Eq.trans hreplace (Eq.trans hnormalized hreduce)))
    h719Ninths

theorem Complex.logarithmicPhaseEightySquareRootCoefficient_le_eighty :
    Complex.logarithmicPhaseEightySquareRootCoefficient ≤ 80 := by
  have hpositive :=
    Complex.logarithmicPhaseExactPositiveTailConstant_le_twenty_seven_halves
  unfold Complex.logarithmicPhaseEightySquareRootCoefficient
  have hsubstitute := add_le_add_left hpositive
    ((55 : ℝ) + 121 / 18 + 2 / 3 + 4)
  have hleft :
      ((55 : ℝ) + 121 / 18 + 2 / 3 + 4) +
          Complex.logarithmicPhaseExactPositiveTailConstant =
        55 + 121 / 18 + 2 / 3 +
          (4 + Complex.logarithmicPhaseExactPositiveTailConstant) :=
    add_assoc ((55 : ℝ) + 121 / 18 + 2 / 3) 4 _
  have hright :
      ((55 : ℝ) + 121 / 18 + 2 / 3 + 4) + 27 / 2 =
        55 + 121 / 18 + 2 / 3 + (4 + 27 / 2) :=
    add_assoc ((55 : ℝ) + 121 / 18 + 2 / 3) 4 (27 / 2)
  exact le_trans (le_of_eq hleft.symm)
    (le_trans hsubstitute
      (le_trans (le_of_eq hright)
        Real.eighty_square_root_rational_ledger_le_eighty))

theorem Real.endpointComponent_add_squareRootComponent_eq_refinedScale
    (t : ℝ) (b : ℕ) :
    Real.logarithmicPhaseEndpointComponent t b +
        Real.logarithmicPhaseSquareRootComponent t =
      Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  unfold Real.logarithmicPhaseEndpointComponent
  unfold Real.logarithmicPhaseSquareRootComponent
  unfold Real.logarithmicPhaseRefinedScale
  have hcastSucc :
      (((b + 1 : ℕ) : ℝ)) = ((b : ℝ) + 1) := by
    exact Eq.trans (Nat.cast_add b 1)
      (congrArg (fun value : ℝ => (b : ℝ) + value) (Nat.cast_one))
  have hcastInt : ((b : ℤ) : ℝ) = (b : ℝ) := rfl
  exact congrArg₂ (fun left right : ℝ => left / ‖t‖ + right)
    (Eq.trans hcastSucc
      (congrArg (fun value : ℝ => value + 1) hcastInt.symm)) rfl

theorem Real.three_mul_endpointComponent_le_eighty_mul_endpointComponent
    (t : ℝ) (b : ℕ) :
    3 * Real.logarithmicPhaseEndpointComponent t b ≤
      80 * Real.logarithmicPhaseEndpointComponent t b := by
  have hcomponent : 0 ≤ Real.logarithmicPhaseEndpointComponent t b := by
    unfold Real.logarithmicPhaseEndpointComponent
    exact div_nonneg (Nat.cast_nonneg (b + 1)) (norm_nonneg t)
  have hsum : (3 : ℝ) + 77 = 80 := by
    have hnat : (3 + 77 : ℕ) = 80 := rfl
    exact Eq.trans (Nat.cast_add 3 77).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hcoefficient : (3 : ℝ) ≤ 80 :=
    (le_add_of_nonneg_right (Nat.cast_nonneg 77)).trans_eq hsum
  exact mul_le_mul_of_nonneg_right hcoefficient hcomponent

theorem Complex.logarithmicPhaseEightyCoefficient_mul_squareRootComponent_le_eighty
    (t : ℝ) :
    Complex.logarithmicPhaseEightySquareRootCoefficient *
        Real.logarithmicPhaseSquareRootComponent t ≤
      80 * Real.logarithmicPhaseSquareRootComponent t := by
  have hcomponent : 0 ≤ Real.logarithmicPhaseSquareRootComponent t := by
    unfold Real.logarithmicPhaseSquareRootComponent
    exact Real.sqrt_nonneg (1 + ‖t‖)
  exact mul_le_mul_of_nonneg_right
    Complex.logarithmicPhaseEightySquareRootCoefficient_le_eighty hcomponent

theorem Complex.logarithmicPhaseEightyTwoComponentLedger_le_eighty_refined
    (t : ℝ) (b : ℕ) :
    Complex.logarithmicPhaseEightyTwoComponentLedger t b ≤
      80 * Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  have hendpoint :=
    Real.three_mul_endpointComponent_le_eighty_mul_endpointComponent t b
  have hsquare :=
    Complex.logarithmicPhaseEightyCoefficient_mul_squareRootComponent_le_eighty t
  have hsum := add_le_add hendpoint hsquare
  unfold Complex.logarithmicPhaseEightyTwoComponentLedger
  exact le_trans hsum
    (le_of_eq
      (Eq.trans
        (mul_add 80
          (Real.logarithmicPhaseEndpointComponent t b)
          (Real.logarithmicPhaseSquareRootComponent t)).symm
        (congrArg (fun value : ℝ => 80 * value)
          (Real.endpointComponent_add_squareRootComponent_eq_refinedScale
            t b))))

theorem Complex.logarithmicPhaseSharpOutsideTailBudget_le_four_plus_positive_mul_squareRootComponent
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseSharpOutsideTailBudget
        t (a : ℤ) (b : ℤ) ≤
      (4 + Complex.logarithmicPhaseExactPositiveTailConstant) *
        Real.logarithmicPhaseSquareRootComponent t := by
  let S := Real.logarithmicPhaseSquareRootComponent t
  let C := 3 + Complex.logarithmicPhaseExactPositiveTailConstant
  have hnegative :=
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_le_sharpMajorant
      t a b ht hgeometry
  have hpositive :=
    Complex.logarithmicPhaseEnhancedPositiveTailBudget_le_exactConstant
      t a b ht hgeometry
  have hsum := add_le_add hnegative hpositive
  have hone : (1 : ℝ) ≤ S := by
    unfold S Real.logarithmicPhaseSquareRootComponent
    exact Real.logarithmicPhase_one_le_sqrt_one_add_norm t ht
  have hconstantNonneg : 0 ≤ C := by
    unfold C
    exact add_nonneg (Nat.cast_nonneg 3)
      Complex.logarithmicPhaseExactPositiveTailConstant_nonneg
  have hconstantScaled : C * 1 ≤ C * S :=
    mul_le_mul_of_nonneg_left hone hconstantNonneg
  have hconstant : C ≤ C * S :=
    Eq.subst (motive := fun value : ℝ => value ≤ C * S)
      (mul_one C) hconstantScaled
  have hrawForm :
      Complex.logarithmicPhaseSharpFarNegativeSeriesMajorant t +
          Complex.logarithmicPhaseExactPositiveTailConstant =
        C + S := by
    unfold Complex.logarithmicPhaseSharpFarNegativeSeriesMajorant
    unfold C S Real.logarithmicPhaseSquareRootComponent
    exact Eq.trans
      (add_assoc (3 : ℝ) (Real.sqrt (1 + ‖t‖))
        Complex.logarithmicPhaseExactPositiveTailConstant)
      (Eq.trans
        (congrArg (fun value : ℝ => 3 + value)
          (add_comm (Real.sqrt (1 + ‖t‖))
            Complex.logarithmicPhaseExactPositiveTailConstant))
        (add_assoc 3 Complex.logarithmicPhaseExactPositiveTailConstant
          (Real.sqrt (1 + ‖t‖))).symm)
  have hconstantPlusS := add_le_add_right hconstant S
  have hcollect : C * S + S = (C + 1) * S := by
    exact Eq.trans
      (congrArg (fun value : ℝ => C * S + value) (one_mul S).symm)
      (add_mul C 1 S).symm
  have hcoefficient :
      C + 1 = 4 + Complex.logarithmicPhaseExactPositiveTailConstant := by
    unfold C
    have hthreeAddOne : (3 : ℝ) + 1 = 4 := by
      have htransition := Real.transition_nat_cast_add 3 1 4 rfl
      have hthree : ((3 : ℕ) : ℝ) = 3 := Nat.cast_ofNat
      have hone : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
      have hfour : ((4 : ℕ) : ℝ) = 4 := Nat.cast_ofNat
      exact Eq.trans
        (congrArg₂ (fun left right : ℝ => left + right)
          hthree.symm hone.symm)
        (Eq.trans htransition hfour)
    exact Eq.trans
      (add_assoc 3 Complex.logarithmicPhaseExactPositiveTailConstant 1)
      (Eq.trans
        (congrArg (fun value : ℝ => 3 + value)
          (add_comm Complex.logarithmicPhaseExactPositiveTailConstant 1))
        (Eq.trans
          (add_assoc 3 1
            Complex.logarithmicPhaseExactPositiveTailConstant).symm
          (congrArg
            (fun value : ℝ =>
              value + Complex.logarithmicPhaseExactPositiveTailConstant)
            hthreeAddOne)))
  unfold Complex.logarithmicPhaseSharpOutsideTailBudget
  exact le_trans hsum
    (le_trans (le_of_eq hrawForm)
      (le_trans hconstantPlusS
        (le_trans (le_of_eq hcollect)
          (le_of_eq (congrArg (fun value : ℝ => value * S) hcoefficient)))))
theorem Complex.logarithmicPhaseSharpBProcessBudget_le_eightyTwoComponentLedger
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseSharpBProcessBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseEightyTwoComponentLedger t b := by
  let S := Real.logarithmicPhaseSquareRootComponent t
  have hactive :=
    Complex.logarithmicPhaseBProcessCompleteActiveBudget_le_fifty_five_scale
      ht hgeometry
  have hfinite :=
    Complex.logarithmicPhaseFiniteInactiveSharpBudget_le_one_hundred_twenty_one_eighteenths_scale
      t ht ht_nonneg a b hgeometry
  have hzero := Real.zeroMode_endpoint_squareRoot_split t ht a b
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have htail :=
    Complex.logarithmicPhaseSharpOutsideTailBudget_le_four_plus_positive_mul_squareRootComponent
      t a b ht hgeometry
  have hscaleIdentity : Complex.logarithmicPhaseBProcessScale t = S := by
    unfold S Real.logarithmicPhaseSquareRootComponent
    rfl
  have hactiveS :
      Complex.logarithmicPhaseBProcessCompleteActiveBudget
          t (a : ℤ) (b : ℤ) ≤ 55 * S :=
    Eq.subst (motive := fun value : ℝ => _ ≤ 55 * value)
      hscaleIdentity hactive
  have hfiniteS :
      Complex.logarithmicPhaseFiniteInactiveSharpBudget
          t (a : ℤ) (b : ℤ) ≤ (121 / 18 : ℝ) * S :=
    Eq.subst (motive := fun value : ℝ => _ ≤ (121 / 18) * value)
      hscaleIdentity hfinite
  unfold Complex.logarithmicPhaseSharpBProcessBudget
  unfold Complex.logarithmicPhaseSharpComplementBudget
  unfold Complex.logarithmicPhaseSharpFiniteComplementBudget
  have hsum := add_le_add hactiveS
    (add_le_add (add_le_add hfiniteS hzero) htail)
  unfold Complex.logarithmicPhaseEightyTwoComponentLedger
  unfold Complex.logarithmicPhaseEightySquareRootCoefficient
  have hreassociate :
      55 * S +
          (((121 / 18 : ℝ) * S +
            (3 * Real.logarithmicPhaseEndpointComponent t b + (2 / 3 : ℝ) * S)) +
          ((4 + Complex.logarithmicPhaseExactPositiveTailConstant) * S)) =
        55 * S + (121 / 18 : ℝ) * S +
          (3 * Real.logarithmicPhaseEndpointComponent t b + (2 / 3 : ℝ) * S) +
          ((4 + Complex.logarithmicPhaseExactPositiveTailConstant) * S) := by
    calc
      55 * S +
          (((121 / 18 : ℝ) * S +
            (3 * Real.logarithmicPhaseEndpointComponent t b + (2 / 3 : ℝ) * S)) +
            ((4 + Complex.logarithmicPhaseExactPositiveTailConstant) * S)) =
          (55 * S +
            ((121 / 18 : ℝ) * S +
              (3 * Real.logarithmicPhaseEndpointComponent t b + (2 / 3 : ℝ) * S))) +
            ((4 + Complex.logarithmicPhaseExactPositiveTailConstant) * S) :=
        (add_assoc (55 * S)
          ((121 / 18 : ℝ) * S +
            (3 * Real.logarithmicPhaseEndpointComponent t b + (2 / 3 : ℝ) * S))
          ((4 + Complex.logarithmicPhaseExactPositiveTailConstant) * S)).symm
      _ = ((55 * S + (121 / 18 : ℝ) * S) +
            (3 * Real.logarithmicPhaseEndpointComponent t b + (2 / 3 : ℝ) * S)) +
            ((4 + Complex.logarithmicPhaseExactPositiveTailConstant) * S) :=
        congrArg (fun value : ℝ =>
          value + ((4 + Complex.logarithmicPhaseExactPositiveTailConstant) * S))
          (add_assoc (55 * S) ((121 / 18 : ℝ) * S)
            (3 * Real.logarithmicPhaseEndpointComponent t b + (2 / 3 : ℝ) * S)).symm
  have hcollect :
      55 * S + (121 / 18 : ℝ) * S +
          (3 * Real.logarithmicPhaseEndpointComponent t b + (2 / 3 : ℝ) * S) +
          ((4 + Complex.logarithmicPhaseExactPositiveTailConstant) * S) =
        3 * Real.logarithmicPhaseEndpointComponent t b +
          (55 + 121 / 18 + 2 / 3 +
            (4 + Complex.logarithmicPhaseExactPositiveTailConstant)) * S := by
    let A := 55 * S + (121 / 18 : ℝ) * S
    let E := 3 * Real.logarithmicPhaseEndpointComponent t b
    let C := (2 / 3 : ℝ) * S
    let T := (4 + Complex.logarithmicPhaseExactPositiveTailConstant) * S
    have hmove : (A + (E + C)) + T = E + (A + C + T) := by
      exact Eq.trans
        (congrArg (fun value : ℝ => value + T)
          (add_assoc A E C).symm)
        (Eq.trans
          (congrArg (fun value : ℝ => (value + C) + T)
            (add_comm A E))
          (Eq.trans
            (congrArg (fun value : ℝ => value + T)
              (add_assoc E A C))
            (add_assoc E (A + C) T)))
    unfold A E C T at hmove
    exact Eq.trans hmove
      (congrArg
        (fun value : ℝ =>
          3 * Real.logarithmicPhaseEndpointComponent t b + value)
        (Real.four_weighted_terms_eq_sum_coeff_mul
          55 (121 / 18) (2 / 3)
          (4 + Complex.logarithmicPhaseExactPositiveTailConstant) S))
  unfold S at hsum hreassociate hcollect
  exact le_trans hsum
    (le_trans (le_of_eq hreassociate)
      (le_of_eq hcollect))

theorem Complex.logarithmicPhaseSharpBProcessBudget_le_eighty_refined
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseSharpBProcessBudget
        t (a : ℤ) (b : ℤ) ≤
      80 * Real.logarithmicPhaseRefinedScale t (b : ℤ) :=
  le_trans
    (Complex.logarithmicPhaseSharpBProcessBudget_le_eightyTwoComponentLedger
      t ht ht_nonneg a b hgeometry)
    (Complex.logarithmicPhaseEightyTwoComponentLedger_le_eighty_refined t b)

end

end LFunctions
end Boundary
