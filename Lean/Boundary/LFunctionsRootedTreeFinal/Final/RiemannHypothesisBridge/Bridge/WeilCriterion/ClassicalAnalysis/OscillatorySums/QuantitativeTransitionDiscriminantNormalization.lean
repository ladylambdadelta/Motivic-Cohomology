import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionScalarDiscriminant

/-!
# Normalization of the transition curvature discriminant

The raw reciprocal-sum discriminant is translated by `s=r+4` in small named
steps.  This file owns the square, cube, core, and penalty normalizations; the
coefficient-level final identity is consumed by the convexity owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.transitionShiftedCore (r : ℝ) : ℝ :=
  r ^ 3 + 8 * r ^ 2 + 16 * r + 4

def Real.transitionShiftedPenalty (r : ℝ) : ℝ :=
  4 * (r + 3) ^ 2 * (r + 4) * r

theorem Real.transition_add_four_sq
    (r : ℝ) :
    (r + 4) ^ 2 = r ^ 2 + 8 * r + 16 := by
  calc
    (r + 4) ^ 2 = (r + 4) * (r + 4) := pow_two (r + 4)
    _ = r * r + r * 4 + (4 * r + 4 * 4) := by
      exact (mul_add (r + 4) r 4).trans
        (congrArg₂ (fun first second : ℝ => first + second)
          (add_mul r 4 r) (add_mul r 4 4))
    _ = r ^ 2 + 4 * r + (4 * r + 16) := by
      exact congrArg₂ (fun first second : ℝ => first + second)
        (congrArg₂ (fun first second : ℝ => first + second)
          (pow_two r).symm (mul_comm r 4))
        (congrArg₂ (fun first second : ℝ => first + second)
          rfl (show (4 : ℝ) * 4 = 16 from rfl))
    _ = r ^ 2 + (4 * r + 4 * r) + 16 := by
      exact (add_assoc (r ^ 2) (4 * r) (4 * r + 16)).trans
        (congrArg (fun value : ℝ => r ^ 2 + value)
          (add_assoc (4 * r) (4 * r) 16).symm)
    _ = r ^ 2 + 8 * r + 16 := by
      exact congrArg
        (fun value : ℝ => r ^ 2 + value + 16)
        ((add_mul 4 4 r).symm.trans
          (congrArg (fun coefficient : ℝ => coefficient * r)
            (show (4 : ℝ) + 4 = 8 from rfl)))

theorem Real.transition_add_four_cube
    (r : ℝ) :
    (r + 4) ^ 3 = r ^ 3 + 12 * r ^ 2 + 48 * r + 64 := by
  have hsquare := Real.transition_add_four_sq r
  have hpower : (r + 4) ^ 3 = (r + 4) ^ 2 * (r + 4) := by
    exact pow_succ (r + 4) 2
  calc
    (r + 4) ^ 3 = (r + 4) ^ 2 * (r + 4) := hpower
    _ = (r ^ 2 + 8 * r + 16) * (r + 4) :=
      congrArg (fun value : ℝ => value * (r + 4)) hsquare
    _ = (r ^ 2 + 8 * r + 16) * r +
        (r ^ 2 + 8 * r + 16) * 4 :=
      mul_add _ r 4
    _ = (r ^ 2 * r + (8 * r) * r + 16 * r) +
        (r ^ 2 * 4 + (8 * r) * 4 + 16 * 4) := by
      exact congrArg₂ (fun first second : ℝ => first + second)
        ((add_mul (r ^ 2 + 8 * r) 16 r).trans
          (congrArg (fun value : ℝ => value + 16 * r)
            (add_mul (r ^ 2) (8 * r) r)))
        ((add_mul (r ^ 2 + 8 * r) 16 4).trans
          (congrArg (fun value : ℝ => value + 16 * 4)
            (add_mul (r ^ 2) (8 * r) 4)))
    _ = (r ^ 3 + 8 * r ^ 2 + 16 * r) +
        (4 * r ^ 2 + 32 * r + 64) := by
      exact congrArg₂ (fun first second : ℝ => first + second)
        (congrArg₂ (fun first second : ℝ => first + second)
          (congrArg₂ (fun first second : ℝ => first + second)
            ((pow_succ r 2).symm)
            ((mul_assoc 8 r r).trans
              (congrArg (fun value : ℝ => 8 * value) (pow_two r).symm)))
          rfl)
        (congrArg₂ (fun first second : ℝ => first + second)
          (congrArg₂ (fun first second : ℝ => first + second)
            (mul_comm (r ^ 2) 4)
            ((mul_assoc 8 r 4).trans
              (Eq.trans
                (congrArg (fun value : ℝ => 8 * value) (mul_comm r 4))
                (mul_assoc 8 4 r).symm).trans
              (congrArg (fun coefficient : ℝ => coefficient * r)
                (show (8 : ℝ) * 4 = 32 from rfl))))
          (show (16 : ℝ) * 4 = 64 from rfl))
    _ = r ^ 3 + (8 * r ^ 2 + 4 * r ^ 2) +
        (16 * r + 32 * r) + 64 := by
      exact
        (add_assoc (r ^ 3 + 8 * r ^ 2 + 16 * r)
          (4 * r ^ 2 + 32 * r) 64).symm.trans
          ((congrArg (fun value : ℝ => value + 64)
            ((add_assoc (r ^ 3 + 8 * r ^ 2 + 16 * r)
              (4 * r ^ 2) (32 * r)).symm.trans
              (congrArg (fun value : ℝ => value + 32 * r)
                ((add_assoc (r ^ 3 + 8 * r ^ 2) (16 * r)
                  (4 * r ^ 2)).trans
                  (congrArg (fun value : ℝ => r ^ 3 + value)
                    ((add_assoc (8 * r ^ 2) (16 * r)
                      (4 * r ^ 2)).symm.trans
                      (congrArg (fun value : ℝ => value + 16 * r)
                        (add_comm (8 * r ^ 2) (4 * r ^ 2))))))))).trans
            (add_assoc
              (r ^ 3 + (8 * r ^ 2 + 4 * r ^ 2))
              (16 * r) (32 * r))))
    _ = r ^ 3 + 12 * r ^ 2 + 48 * r + 64 := by
      have h12 : 8 * r ^ 2 + 4 * r ^ 2 = 12 * r ^ 2 := by
        exact (add_mul 8 4 (r ^ 2)).symm.trans
          (congrArg (fun coefficient : ℝ => coefficient * r ^ 2)
            (show (8 : ℝ) + 4 = 12 from rfl))
      have h48 : 16 * r + 32 * r = 48 * r := by
        exact (add_mul 16 32 r).symm.trans
          (congrArg (fun coefficient : ℝ => coefficient * r)
            (show (16 : ℝ) + 32 = 48 from rfl))
      exact congrArg
        (fun pair : ℝ × ℝ => r ^ 3 + pair.1 + pair.2 + 64)
        (Prod.ext h12 h48)

theorem Real.transition_shifted_core_identity
    (r : ℝ) :
    (r + 4) ^ 3 - 4 * (r + 4) ^ 2 + 4 =
      Real.transitionShiftedCore r := by
  have hcube := Real.transition_add_four_cube r
  have hsquare := Real.transition_add_four_sq r
  unfold Real.transitionShiftedCore
  calc
    (r + 4) ^ 3 - 4 * (r + 4) ^ 2 + 4 =
      (r ^ 3 + 12 * r ^ 2 + 48 * r + 64) -
        4 * (r ^ 2 + 8 * r + 16) + 4 :=
      congrArg₂ (fun first second : ℝ => first - 4 * second + 4)
        hcube hsquare
    _ = (r ^ 3 + 12 * r ^ 2 + 48 * r + 64) -
        (4 * r ^ 2 + 32 * r + 64) + 4 := by
      exact congrArg (fun value : ℝ =>
        (r ^ 3 + 12 * r ^ 2 + 48 * r + 64) - value + 4)
        ((mul_add 4 (r ^ 2 + 8 * r) 16).trans
          (congrArg (fun value : ℝ => value + 4 * 16)
            ((mul_add 4 (r ^ 2) (8 * r)).trans
              (congrArg₂ (fun first second : ℝ => first + second)
                rfl
                ((mul_assoc 4 8 r).symm.trans
                  (congrArg (fun coefficient : ℝ => coefficient * r)
                    (show (4 : ℝ) * 8 = 32 from rfl)))))).trans
          (congrArg (fun value : ℝ => 4 * r ^ 2 + 32 * r + value)
            (show (4 : ℝ) * 16 = 64 from rfl)))
    _ = r ^ 3 + 8 * r ^ 2 + 16 * r + 4 := by
      let A := r ^ 3
      let B := r ^ 2
      calc
        (A + 12 * B + 48 * r + 64) -
            (4 * B + 32 * r + 64) + 4 =
          A + (12 * B - 4 * B) +
            (48 * r - 32 * r) + (64 - 64) + 4 := by
            have houter := sub_add_sub_comm
              (A + 12 * B + 48 * r) 64
              (4 * B + 32 * r) 64
            have hmiddle := congrArg (fun value : ℝ => value + 4)
              (sub_add_sub_comm
                (A + 12 * B) (48 * r)
                (4 * B) (32 * r))
            have hinner := congrArg (fun value : ℝ => value +
              (48 * r - 32 * r) + (64 - 64) + 4)
              (sub_add_sub_comm A (12 * B) 0 (4 * B))
            exact Eq.trans houter (Eq.trans hmiddle hinner)
        _ = A + 8 * B + 16 * r + 4 := by
          have h8 : 12 * B - 4 * B = 8 * B := by
            exact (sub_mul 12 4 B).symm.trans
              (congrArg (fun coefficient : ℝ => coefficient * B)
                (show (12 : ℝ) - 4 = 8 from rfl))
          have h16 : 48 * r - 32 * r = 16 * r := by
            exact (sub_mul 48 32 r).symm.trans
              (congrArg (fun coefficient : ℝ => coefficient * r)
                (show (48 : ℝ) - 32 = 16 from rfl))
          exact congrArg
            (fun triple : ℝ × ℝ × ℝ =>
              A + triple.1 + triple.2 + triple.2.2 + 4)
            (Prod.ext h8 (Prod.ext h16 (sub_self 64)))

theorem Real.transition_shifted_penalty_identity
    (r : ℝ) :
    4 * ((r + 4) - 1) ^ 2 * (r + 4) * ((r + 4) - 4) =
      Real.transitionShiftedPenalty r := by
  unfold Real.transitionShiftedPenalty
  have hthree : (r + 4) - 1 = r + 3 := by
    calc
      (r + 4) - 1 = r + (4 - 1) :=
        (add_sub_assoc r 4 1).symm
      _ = r + 3 :=
        congrArg (fun value : ℝ => r + value)
          (show (4 : ℝ) - 1 = 3 from rfl)
  have hzero : (r + 4) - 4 = r := add_sub_cancel_right r 4
  exact congrArg₂
    (fun first second : ℝ => 4 * first ^ 2 * (r + 4) * second)
    hthree hzero

theorem Real.transitionCurvatureRawDiscriminant_add_four
    (r : ℝ) :
    Real.transitionCurvatureRawDiscriminant (r + 4) =
      Real.transitionShiftedCore r ^ 2 -
        Real.transitionShiftedPenalty r := by
  unfold Real.transitionCurvatureRawDiscriminant
  have hcore := Real.transition_shifted_core_identity r
  have hpenalty := Real.transition_shifted_penalty_identity r
  exact congrArg₂ (fun first second : ℝ => first ^ 2 - second)
    hcore hpenalty

def Real.transitionShiftedCoreSquareExpansion (r : ℝ) : ℝ :=
  16 + 128 * r + 320 * r ^ 2 + 264 * r ^ 3 +
    96 * r ^ 4 + 16 * r ^ 5 + r ^ 6

def Real.transitionShiftedPenaltyExpansion (r : ℝ) : ℝ :=
  144 * r + 132 * r ^ 2 + 40 * r ^ 3 + 4 * r ^ 4

theorem Real.transitionShiftedCore_square_eq_expansion
    (r : ℝ) :
    Real.transitionShiftedCore r ^ 2 =
      Real.transitionShiftedCoreSquareExpansion r := by
  let a := r ^ 3
  let b := 8 * r ^ 2
  let c := 16 * r
  let d : ℝ := 4
  unfold Real.transitionShiftedCore
  unfold Real.transitionShiftedCoreSquareExpansion
  change (a + b + c + d) ^ 2 =
    16 + 128 * r + 320 * r ^ 2 + 264 * r ^ 3 +
      96 * r ^ 4 + 16 * r ^ 5 + r ^ 6
  have hsquare :
      (a + b + c + d) ^ 2 =
        a * a + b * b + c * c + d * d +
          2 * (a * b) + 2 * (a * c) + 2 * (a * d) +
          2 * (b * c) + 2 * (b * d) + 2 * (c * d) := by
    calc
      (a + b + c + d) ^ 2 =
          (a + b + c + d) * (a + b + c + d) :=
        pow_two (a + b + c + d)
      _ = (a + b + c + d) * a +
          (a + b + c + d) * b +
          (a + b + c + d) * c +
          (a + b + c + d) * d := by
        exact (mul_add (a + b + c + d) (a + b + c) d).trans
          ((congrArg (fun value : ℝ => value + (a + b + c + d) * d)
            ((mul_add (a + b + c + d) (a + b) c).trans
              (congrArg (fun value : ℝ => value +
                (a + b + c + d) * c)
                (mul_add (a + b + c + d) a b)))).trans
            (add_assoc
              ((a + b + c + d) * a + (a + b + c + d) * b)
              ((a + b + c + d) * c)
              ((a + b + c + d) * d)).symm)
      _ = (a * a + b * a + c * a + d * a) +
          (a * b + b * b + c * b + d * b) +
          (a * c + b * c + c * c + d * c) +
          (a * d + b * d + c * d + d * d) := by
        exact congrArg₂ (fun first second : ℝ => first + second)
          (congrArg₂ (fun first second : ℝ => first + second)
            (congrArg₂ (fun first second : ℝ => first + second)
              (add_mul (a + b + c) d a)
              (add_mul (a + b + c) d b))
            (add_mul (a + b + c) d c))
          (add_mul (a + b + c) d d)
      _ = a * a + b * b + c * c + d * d +
          2 * (a * b) + 2 * (a * c) + 2 * (a * d) +
          2 * (b * c) + 2 * (b * d) + 2 * (c * d) := by
        have hab : b * a + a * b = 2 * (a * b) := by
          exact (congrArg₂ (fun first second : ℝ => first + second)
            (mul_comm b a) rfl).trans (two_mul (a * b)).symm
        have hac : c * a + a * c = 2 * (a * c) := by
          exact (congrArg₂ (fun first second : ℝ => first + second)
            (mul_comm c a) rfl).trans (two_mul (a * c)).symm
        have had : d * a + a * d = 2 * (a * d) := by
          exact (congrArg₂ (fun first second : ℝ => first + second)
            (mul_comm d a) rfl).trans (two_mul (a * d)).symm
        have hbc : c * b + b * c = 2 * (b * c) := by
          exact (congrArg₂ (fun first second : ℝ => first + second)
            (mul_comm c b) rfl).trans (two_mul (b * c)).symm
        have hbd : d * b + b * d = 2 * (b * d) := by
          exact (congrArg₂ (fun first second : ℝ => first + second)
            (mul_comm d b) rfl).trans (two_mul (b * d)).symm
        have hcd : d * c + c * d = 2 * (c * d) := by
          exact (congrArg₂ (fun first second : ℝ => first + second)
            (mul_comm d c) rfl).trans (two_mul (c * d)).symm
        exact
          Eq.trans
            (add_left_comm
              (a * a + b * a + c * a + d * a)
              (a * b + b * b + c * b + d * b)
              ((a * c + b * c + c * c + d * c) +
                (a * d + b * d + c * d + d * d)))
            (congrArg
              (fun sextuple : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ =>
                a * a + b * b + c * c + d * d +
                  sextuple.1 + sextuple.2.1 + sextuple.2.2.1 +
                  sextuple.2.2.2.1 + sextuple.2.2.2.2.1 +
                  sextuple.2.2.2.2.2)
              (Prod.ext hab
                (Prod.ext hac
                  (Prod.ext had
                    (Prod.ext hbc (Prod.ext hbd hcd))))))
  have hterms :
      a * a + b * b + c * c + d * d +
          2 * (a * b) + 2 * (a * c) + 2 * (a * d) +
          2 * (b * c) + 2 * (b * d) + 2 * (c * d) =
        16 + 128 * r + 320 * r ^ 2 + 264 * r ^ 3 +
          96 * r ^ 4 + 16 * r ^ 5 + r ^ 6 := by
    unfold a b c d
    have h6 : r ^ 3 * r ^ 3 = r ^ 6 := by
      exact (pow_add r 3 3).symm
    have h5 : r ^ 3 * r ^ 2 = r ^ 5 := by
      exact (pow_add r 3 2).symm
    have h4 : r ^ 2 * r ^ 2 = r ^ 4 := by
      exact (pow_add r 2 2).symm
    have h3 : r ^ 2 * r = r ^ 3 := by
      exact (pow_succ r 2).symm
    exact Eq.trans
      (congrArg
        (fun values : ℝ × ℝ × ℝ × ℝ =>
          values.1 + values.2.1 + values.2.2.1 + values.2.2.2)
        (Prod.ext h6 (Prod.ext h5 (Prod.ext h4 h3))))
      rfl
  exact Eq.trans hsquare hterms

theorem Real.transitionShiftedPenalty_eq_expansion
    (r : ℝ) :
    Real.transitionShiftedPenalty r =
      Real.transitionShiftedPenaltyExpansion r := by
  unfold Real.transitionShiftedPenalty
  unfold Real.transitionShiftedPenaltyExpansion
  have hsquare : (r + 3) ^ 2 = r ^ 2 + 6 * r + 9 := by
    calc
      (r + 3) ^ 2 = (r + 3) * (r + 3) := pow_two (r + 3)
      _ = r * r + r * 3 + (3 * r + 3 * 3) := by
        exact (mul_add (r + 3) r 3).trans
          (congrArg₂ (fun first second : ℝ => first + second)
            (add_mul r 3 r) (add_mul r 3 3))
      _ = r ^ 2 + 6 * r + 9 := by
        have hdouble : r * 3 + 3 * r = 6 * r := by
          exact (congrArg₂ (fun first second : ℝ => first + second)
            (mul_comm r 3) rfl).trans
            ((add_mul 3 3 r).symm.trans
              (congrArg (fun coefficient : ℝ => coefficient * r)
                (show (3 : ℝ) + 3 = 6 from rfl)))
        exact Eq.trans
          (congrArg₂ (fun first second : ℝ => first + second)
            (congrArg₂ (fun first second : ℝ => first + second)
              (pow_two r).symm hdouble)
            (show (3 : ℝ) * 3 = 9 from rfl))
          (add_assoc (r ^ 2) (6 * r) 9).symm
  calc
    4 * (r + 3) ^ 2 * (r + 4) * r =
        4 * (r ^ 2 + 6 * r + 9) * (r + 4) * r :=
      congrArg (fun value : ℝ => 4 * value * (r + 4) * r) hsquare
    _ = 144 * r + 132 * r ^ 2 + 40 * r ^ 3 + 4 * r ^ 4 := by
      have h4 : r ^ 3 * r = r ^ 4 := (pow_succ r 3).symm
      have h3 : r ^ 2 * r = r ^ 3 := (pow_succ r 2).symm
      exact Eq.trans
        (mul_assoc (4 * (r ^ 2 + 6 * r + 9)) (r + 4) r)
        (Eq.trans
          (congrArg (fun value : ℝ => value * r)
            (mul_add (4 * (r ^ 2 + 6 * r + 9)) r 4))
          rfl)

theorem Real.transitionShiftedCore_square_sub_penalty_eq_discriminant
    (r : ℝ) :
    Real.transitionShiftedCore r ^ 2 -
        Real.transitionShiftedPenalty r =
      Real.transitionShiftedDiscriminant r := by
  have hcore := Real.transitionShiftedCore_square_eq_expansion r
  have hpenalty := Real.transitionShiftedPenalty_eq_expansion r
  unfold Real.transitionShiftedCoreSquareExpansion at hcore
  unfold Real.transitionShiftedPenaltyExpansion at hpenalty
  unfold Real.transitionShiftedDiscriminant
  exact Eq.trans
    (congrArg₂ (fun first second : ℝ => first - second) hcore hpenalty)
    rfl

theorem Real.transitionCurvatureRawDiscriminant_eq_normalized
    (s : ℝ) :
    Real.transitionCurvatureRawDiscriminant s =
      Real.transitionCurvatureDiscriminant s := by
  let r := s - 4
  have hs : r + 4 = s := by
    unfold r
    exact sub_add_cancel s 4
  have hraw := Real.transitionCurvatureRawDiscriminant_add_four r
  have hnormalized :=
    Real.transitionShiftedCore_square_sub_penalty_eq_discriminant r
  unfold Real.transitionCurvatureDiscriminant
  exact Eq.subst
    (motive := fun value : ℝ =>
      Real.transitionCurvatureRawDiscriminant value =
        Real.transitionShiftedDiscriminant (s - 4))
    hs
    (Eq.trans hraw hnormalized)

theorem Real.transitionCurvatureRawDiscriminant_nonneg
    {s : ℝ}
    (hs : 4 ≤ s) :
    0 ≤ Real.transitionCurvatureRawDiscriminant s := by
  have hidentity :=
    Real.transitionCurvatureRawDiscriminant_eq_normalized s
  have hnonneg := Real.transitionCurvatureDiscriminant_nonneg hs
  exact Eq.subst (motive := fun value : ℝ => 0 ≤ value)
    hidentity.symm hnonneg

end
end LFunctions
end Boundary
