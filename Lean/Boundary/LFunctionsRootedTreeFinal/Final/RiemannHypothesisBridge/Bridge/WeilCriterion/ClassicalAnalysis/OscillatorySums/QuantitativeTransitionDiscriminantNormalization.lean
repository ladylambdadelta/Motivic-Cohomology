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

theorem Real.transition_nat_cast_mul
    (a b c : ℕ)
    (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun value : ℕ => (value : ℝ)) h)

theorem Real.transition_nat_cast_add
    (a b c : ℕ)
    (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun value : ℕ => (value : ℝ)) h)

theorem Real.transition_four_mul_four :
    (4 : ℝ) * 4 = 16 := by
  exact Real.transition_nat_cast_mul 4 4 16 rfl

theorem Real.transition_three_mul_three :
    (3 : ℝ) * 3 = 9 := by
  exact Real.transition_nat_cast_mul 3 3 9 rfl

theorem Real.transition_four_add_four :
    (4 : ℝ) + 4 = 8 := by
  exact Real.transition_nat_cast_add 4 4 8 rfl

theorem Real.transition_three_add_three :
    (3 : ℝ) + 3 = 6 := by
  exact Real.transition_nat_cast_add 3 3 6 rfl

theorem Real.transition_three_add_one :
    (3 : ℝ) + 1 = 4 := by
  have hsucc : ((Nat.succ 3 : ℕ) : ℝ) = (3 : ℝ) + 1 :=
    Nat.cast_succ 3
  exact hsucc.symm

theorem Real.transition_eight_mul_four :
    (8 : ℝ) * 4 = 32 := by
  exact Real.transition_nat_cast_mul 8 4 32 rfl

theorem Real.transition_sixteen_mul_four :
    (16 : ℝ) * 4 = 64 := by
  exact Real.transition_nat_cast_mul 16 4 64 rfl

theorem Real.transition_sixteen_add_thirtytwo :
    (16 : ℝ) + 32 = 48 := by
  exact Real.transition_nat_cast_add 16 32 48 rfl

theorem Real.transition_eight_add_four :
    (8 : ℝ) + 4 = 12 := by
  exact Real.transition_nat_cast_add 8 4 12 rfl

theorem Real.transition_fortyeight_sub_thirtytwo :
    (48 : ℝ) - 32 = 16 := by
  have hsum : (16 : ℝ) + 32 = 48 :=
    Real.transition_sixteen_add_thirtytwo
  calc
    (48 : ℝ) - 32 = (16 + 32) - 32 :=
      congrArg (fun value : ℝ => value - 32) hsum.symm
    _ = 16 := add_sub_cancel_right 16 32

theorem Real.transition_twelve_sub_four :
    (12 : ℝ) - 4 = 8 := by
  have hsum : (8 : ℝ) + 4 = 12 :=
    Real.transition_eight_add_four
  calc
    (12 : ℝ) - 4 = (8 + 4) - 4 :=
      congrArg (fun value : ℝ => value - 4) hsum.symm
    _ = 8 := add_sub_cancel_right 8 4

theorem Real.transition_four_sub_one :
    (4 : ℝ) - 1 = 3 := by
  have hsum := Real.transition_three_add_one
  calc
    (4 : ℝ) - 1 = (3 + 1) - 1 :=
      congrArg (fun value : ℝ => value - 1) hsum.symm
    _ = 3 := add_sub_cancel_right 3 1

theorem Real.transition_twelve_mul_sub_four_mul
    (x : ℝ) :
    12 * x - 4 * x = 8 * x := by
  calc
    12 * x - 4 * x = (12 - 4) * x := (sub_mul 12 4 x).symm
    _ = 8 * x := congrArg (fun coefficient : ℝ => coefficient * x)
      Real.transition_twelve_sub_four

theorem Real.transition_fortyeight_mul_sub_thirtytwo_mul
    (x : ℝ) :
    48 * x - 32 * x = 16 * x := by
  calc
    48 * x - 32 * x = (48 - 32) * x := (sub_mul 48 32 x).symm
    _ = 16 * x := congrArg (fun coefficient : ℝ => coefficient * x)
      Real.transition_fortyeight_sub_thirtytwo

theorem Real.transition_four_mul_eight_mul
    (x : ℝ) :
    4 * (8 * x) = 32 * x := by
  calc
    4 * (8 * x) = (4 * 8) * x := (mul_assoc 4 8 x).symm
    _ = 32 * x := congrArg (fun coefficient : ℝ => coefficient * x)
      (Eq.trans (mul_comm 4 8) Real.transition_eight_mul_four)

theorem Real.transition_four_mul_sixteen_mul
    (x : ℝ) :
    4 * (16 * x) = 64 * x := by
  calc
    4 * (16 * x) = (4 * 16) * x := (mul_assoc 4 16 x).symm
    _ = 64 * x := congrArg (fun coefficient : ℝ => coefficient * x)
      (Eq.trans (mul_comm 4 16) Real.transition_sixteen_mul_four)

theorem Real.transition_collect_two_pairs
    (a x y u v w : ℝ) :
    (a + x + y) + (u + v + w) =
      a + (x + u) + (y + v) + w := by
  calc
    (a + x + y) + (u + v + w) =
        ((a + x + y) + (u + v)) + w :=
      (add_assoc (a + x + y) (u + v) w).symm
    _ = (a + x + y + u + v) + w :=
      congrArg (fun value : ℝ => value + w)
        (add_assoc (a + x + y) u v).symm
    _ = (a + x + u + y + v) + w :=
      congrArg (fun value : ℝ => value + v + w)
        (add_right_comm (a + x) y u)
    _ = (a + (x + u) + y + v) + w :=
      congrArg (fun value : ℝ => value + y + v + w)
        (add_assoc a x u)
    _ = a + (x + u) + (y + v) + w :=
      congrArg (fun value : ℝ => value + w)
        (add_assoc (a + (x + u)) y v)

theorem Real.transition_add_four_sq
    (r : ℝ) :
    (r + 4) ^ 2 = r ^ 2 + 8 * r + 16 := by
  calc
    (r + 4) ^ 2 = (r + 4) * (r + 4) := pow_two (r + 4)
    _ = r * r + 4 * r + (r * 4 + 4 * 4) := by
      exact (mul_add (r + 4) r 4).trans
        (congrArg₂ (fun first second : ℝ => first + second)
          (add_mul r 4 r) (add_mul r 4 4))
    _ = r ^ 2 + 4 * r + (4 * r + 16) := by
      exact congrArg₂ (fun first second : ℝ => first + second)
        (congrArg₂ (fun first second : ℝ => first + second)
          (pow_two r).symm rfl)
        (congrArg₂ (fun first second : ℝ => first + second)
          (mul_comm r 4) Real.transition_four_mul_four)
    _ = r ^ 2 + (4 * r + 4 * r) + 16 := by
      exact Eq.trans
        (add_assoc (r ^ 2) (4 * r) (4 * r + 16))
        (Eq.trans
          (congrArg (fun value : ℝ => r ^ 2 + value)
            (add_assoc (4 * r) (4 * r) 16).symm)
          (add_assoc (r ^ 2) (4 * r + 4 * r) 16).symm)
    _ = r ^ 2 + 8 * r + 16 := by
      exact congrArg
        (fun value : ℝ => r ^ 2 + value + 16)
        ((add_mul 4 4 r).symm.trans
          (congrArg (fun coefficient : ℝ => coefficient * r)
            Real.transition_four_add_four))

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
            (Eq.trans (mul_assoc 8 r 4)
              (Eq.trans
                (congrArg (fun value : ℝ => 8 * value) (mul_comm r 4))
                (Eq.trans (mul_assoc 8 4 r).symm
                  (congrArg (fun coefficient : ℝ => coefficient * r)
                    Real.transition_eight_mul_four)))))
          Real.transition_sixteen_mul_four)
    _ = r ^ 3 + (8 * r ^ 2 + 4 * r ^ 2) +
        (16 * r + 32 * r) + 64 := by
      exact Real.transition_collect_two_pairs
        (r ^ 3) (8 * r ^ 2) (16 * r)
        (4 * r ^ 2) (32 * r) 64
    _ = r ^ 3 + 12 * r ^ 2 + 48 * r + 64 := by
      have h12 : 8 * r ^ 2 + 4 * r ^ 2 = 12 * r ^ 2 := by
        exact (add_mul 8 4 (r ^ 2)).symm.trans
          (congrArg (fun coefficient : ℝ => coefficient * r ^ 2)
            Real.transition_eight_add_four)
      have h48 : 16 * r + 32 * r = 48 * r := by
        exact (add_mul 16 32 r).symm.trans
          (congrArg (fun coefficient : ℝ => coefficient * r)
            Real.transition_sixteen_add_thirtytwo)
      exact congrArg₂
        (fun first second : ℝ => r ^ 3 + first + second + 64)
        h12 h48

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
      have hlinear : 4 * (8 * r) = 32 * r := by
        exact (mul_assoc 4 8 r).symm.trans
          (congrArg (fun coefficient : ℝ => coefficient * r)
            (Eq.trans (mul_comm 4 8)
              Real.transition_eight_mul_four))
      have hproduct :
          4 * (r ^ 2 + 8 * r + 16) =
            4 * r ^ 2 + 32 * r + 64 := by
        calc
          4 * (r ^ 2 + 8 * r + 16) =
              4 * (r ^ 2 + 8 * r) + 4 * 16 :=
            mul_add 4 (r ^ 2 + 8 * r) 16
          _ = (4 * r ^ 2 + 4 * (8 * r)) + 4 * 16 :=
            congrArg (fun value : ℝ => value + 4 * 16)
              (mul_add 4 (r ^ 2) (8 * r))
          _ = 4 * r ^ 2 + 32 * r + 64 :=
            congrArg₂
              (fun first second : ℝ => 4 * r ^ 2 + first + second)
              hlinear
              (Eq.trans (mul_comm 4 16)
                Real.transition_sixteen_mul_four)
      exact congrArg (fun value : ℝ =>
        (r ^ 3 + 12 * r ^ 2 + 48 * r + 64) - value + 4) hproduct
    _ = r ^ 3 + 8 * r ^ 2 + 16 * r + 4 := by
      let A := r ^ 3
      let B := r ^ 2
      calc
        (A + 12 * B + 48 * r + 64) -
            (4 * B + 32 * r + 64) + 4 =
          A + (12 * B - 4 * B) +
            (48 * r - 32 * r) + (64 - 64) + 4 := by
            have houter := congrArg (fun value : ℝ => value + 4)
              (sub_add_sub_comm
                (A + 12 * B + 48 * r) (4 * B + 32 * r)
                64 64).symm
            have hmiddle := congrArg (fun value : ℝ =>
              value + (64 - 64) + 4)
              (sub_add_sub_comm
                (A + 12 * B) (4 * B)
                (48 * r) (32 * r)).symm
            have hinnerBase :
                (A + 12 * B) - 4 * B =
                  A + (12 * B - 4 * B) := by
              calc
                (A + 12 * B) - 4 * B =
                    (A + 12 * B) - (0 + 4 * B) :=
                  congrArg (fun value : ℝ => (A + 12 * B) - value)
                    (zero_add (4 * B)).symm
                _ = (A - 0) + (12 * B - 4 * B) :=
                  (sub_add_sub_comm A 0 (12 * B) (4 * B)).symm
                _ = A + (12 * B - 4 * B) :=
                  congrArg (fun value : ℝ =>
                    value + (12 * B - 4 * B)) (sub_zero A)
            have hinner := congrArg (fun value : ℝ => value +
              (48 * r - 32 * r) + (64 - 64) + 4) hinnerBase
            exact Eq.trans houter (Eq.trans hmiddle hinner)
        _ = A + 8 * B + 16 * r + 4 := by
          have h8 : 12 * B - 4 * B = 8 * B := by
            exact (sub_mul 12 4 B).symm.trans
              (congrArg (fun coefficient : ℝ => coefficient * B)
                Real.transition_twelve_sub_four)
          have h16 : 48 * r - 32 * r = 16 * r := by
            exact (sub_mul 48 32 r).symm.trans
              (congrArg (fun coefficient : ℝ => coefficient * r)
                Real.transition_fortyeight_sub_thirtytwo)
          have hzero : (64 : ℝ) - 64 = 0 := sub_self 64
          exact Eq.trans
            (congrArg (fun value : ℝ =>
              A + value + (48 * r - 32 * r) + (64 - 64) + 4) h8)
            (Eq.trans
              (congrArg (fun value : ℝ =>
                A + 8 * B + value + (64 - 64) + 4) h16)
              (Eq.trans
                (congrArg (fun value : ℝ =>
                  A + 8 * B + 16 * r + value + 4) hzero)
                (congrArg (fun value : ℝ => value + 4)
                  (add_zero (A + 8 * B + 16 * r)))))

theorem Real.transition_shifted_penalty_identity
    (r : ℝ) :
    4 * ((r + 4) - 1) ^ 2 * (r + 4) * ((r + 4) - 4) =
      Real.transitionShiftedPenalty r := by
  unfold Real.transitionShiftedPenalty
  have hthree : (r + 4) - 1 = r + 3 := by
    calc
      (r + 4) - 1 = r + (4 - 1) :=
        add_sub_assoc r 4 1
      _ = r + 3 :=
        congrArg (fun value : ℝ => r + value)
          Real.transition_four_sub_one
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

theorem Real.transition_reverse_three_add
    (a b c : ℝ) :
    a + b + c = c + b + a := by
  calc
    a + b + c = c + (a + b) := add_comm (a + b) c
    _ = c + (b + a) :=
      congrArg (fun value : ℝ => c + value) (add_comm a b)
    _ = c + b + a := (add_assoc c b a).symm

theorem Real.transition_reverse_four_add
    (a b c d : ℝ) :
    a + b + c + d = d + c + b + a := by
  calc
    a + b + c + d = d + (a + b + c) :=
      add_comm (a + b + c) d
    _ = d + (c + (a + b)) :=
      congrArg (fun value : ℝ => d + value)
        (add_comm (a + b) c)
    _ = d + (c + (b + a)) :=
      congrArg (fun value : ℝ => d + (c + value))
        (add_comm a b)
    _ = d + c + (b + a) :=
      (add_assoc d c (b + a)).symm
    _ = d + c + b + a :=
      (add_assoc (d + c) b a).symm

theorem Real.transition_scaled_product
    (a b x y : ℝ) :
    (a * x) * (b * y) = (a * b) * (x * y) := by
  calc
    (a * x) * (b * y) = a * (x * (b * y)) :=
      mul_assoc a x (b * y)
    _ = a * ((x * b) * y) :=
      congrArg (fun value : ℝ => a * value)
        (mul_assoc x b y).symm
    _ = a * ((b * x) * y) :=
      congrArg (fun value : ℝ => a * (value * y))
        (mul_comm x b)
    _ = a * (b * (x * y)) :=
      congrArg (fun value : ℝ => a * value)
        (mul_assoc b x y)
    _ = (a * b) * (x * y) :=
      (mul_assoc a b (x * y)).symm

theorem Real.transition_add_square_expansion
    (x y : ℝ) :
    (x + y) ^ 2 = x ^ 2 + 2 * (x * y) + y ^ 2 := by
  have hcross : y * x + x * y = 2 * (x * y) := by
    exact (congrArg₂ (fun first second : ℝ => first + second)
      (mul_comm y x) rfl).trans (two_mul (x * y)).symm
  calc
    (x + y) ^ 2 = (x + y) * (x + y) := pow_two (x + y)
    _ = (x + y) * x + (x + y) * y := mul_add (x + y) x y
    _ = (x * x + y * x) + (x * y + y * y) :=
      congrArg₂ (fun first second : ℝ => first + second)
        (add_mul x y x) (add_mul x y y)
    _ = x * x + (y * x + x * y) + y * y := by
      exact (add_assoc (x * x + y * x) (x * y) (y * y)).symm.trans
        (congrArg (fun value : ℝ => value + y * y)
          (add_assoc (x * x) (y * x) (x * y)))
    _ = x * x + 2 * (x * y) + y * y :=
      congrArg (fun value : ℝ => x * x + value + y * y) hcross
    _ = x ^ 2 + 2 * (x * y) + y ^ 2 :=
      congrArg₂
        (fun first second : ℝ => first + 2 * (x * y) + second)
        (pow_two x).symm (pow_two y).symm

theorem Real.transition_collect_one_pair
    (a b c d : ℝ) :
    (a + b) + (c + d) = a + (b + c) + d := by
  calc
    (a + b) + (c + d) = (a + b + c) + d :=
      (add_assoc (a + b) c d).symm
    _ = a + (b + c) + d :=
      congrArg (fun value : ℝ => value + d) (add_assoc a b c)

theorem Real.transition_collect_middle_pair
    (a b c d e : ℝ) :
    (a + b + c) + (d + e) = a + b + (c + d) + e := by
  calc
    (a + b + c) + (d + e) = (a + b + c + d) + e :=
      (add_assoc (a + b + c) d e).symm
    _ = a + b + (c + d) + e :=
      congrArg (fun value : ℝ => value + e)
        (add_assoc (a + b) c d)

theorem Real.transition_two_mul_sixtyfour :
    (2 : ℝ) * 64 = 128 := by
  exact Real.transition_nat_cast_mul 2 64 128 rfl

theorem Real.transition_sixteen_mul_sixteen :
    (16 : ℝ) * 16 = 256 := by
  exact Real.transition_nat_cast_mul 16 16 256 rfl

theorem Real.transition_sixteen_mul_eight :
    (16 : ℝ) * 8 = 128 := by
  exact Real.transition_nat_cast_mul 16 8 128 rfl

theorem Real.transition_two_mul_thirtytwo :
    (2 : ℝ) * 32 = 64 := by
  exact Real.transition_nat_cast_mul 2 32 64 rfl

theorem Real.transition_two_mul_onehundredtwentyeight :
    (2 : ℝ) * 128 = 256 := by
  exact Real.transition_nat_cast_mul 2 128 256 rfl

theorem Real.transition_eight_mul_eight :
    (8 : ℝ) * 8 = 64 := by
  exact Real.transition_nat_cast_mul 8 8 64 rfl

theorem Real.transition_twohundredfiftysix_add_sixtyfour :
    (256 : ℝ) + 64 = 320 := by
  exact Real.transition_nat_cast_add 256 64 320 rfl

theorem Real.transition_two_mul_four :
    (2 : ℝ) * 4 = 8 := by
  exact Real.transition_nat_cast_mul 2 4 8 rfl

theorem Real.transition_two_mul_sixteen :
    (2 : ℝ) * 16 = 32 := by
  exact Real.transition_nat_cast_mul 2 16 32 rfl

theorem Real.transition_two_mul_eight :
    (2 : ℝ) * 8 = 16 := by
  exact Real.transition_nat_cast_mul 2 8 16 rfl

theorem Real.transition_twohundredfiftysix_add_eight :
    (256 : ℝ) + 8 = 264 := by
  exact Real.transition_nat_cast_add 256 8 264 rfl

theorem Real.transition_sixtyfour_add_thirtytwo :
    (64 : ℝ) + 32 = 96 := by
  exact Real.transition_nat_cast_add 64 32 96 rfl

theorem Real.transition_linear_core_square
    (r : ℝ) :
    (4 + 16 * r) ^ 2 = 16 + 128 * r + 256 * r ^ 2 := by
  have hconstant : (4 : ℝ) ^ 2 = 16 := by
    exact Eq.trans (pow_two 4) Real.transition_four_mul_four
  have hlinear : 2 * (4 * (16 * r)) = 128 * r := by
    calc
      2 * (4 * (16 * r)) = 2 * (64 * r) :=
        congrArg (fun value : ℝ => 2 * value)
          (Real.transition_four_mul_sixteen_mul r)
      _ = (2 * 64) * r := (mul_assoc 2 64 r).symm
      _ = 128 * r :=
        congrArg (fun coefficient : ℝ => coefficient * r)
          Real.transition_two_mul_sixtyfour
  have hquadratic : (16 * r) ^ 2 = 256 * r ^ 2 := by
    calc
      (16 * r) ^ 2 = (16 * r) * (16 * r) := pow_two (16 * r)
      _ = (16 * 16) * (r * r) :=
        Real.transition_scaled_product 16 16 r r
      _ = 256 * r ^ 2 :=
        congrArg₂ (fun coefficient power : ℝ => coefficient * power)
          Real.transition_sixteen_mul_sixteen (pow_two r).symm
  calc
    (4 + 16 * r) ^ 2 =
        4 ^ 2 + 2 * (4 * (16 * r)) + (16 * r) ^ 2 :=
      Real.transition_add_square_expansion 4 (16 * r)
    _ = 16 + 2 * (4 * (16 * r)) + (16 * r) ^ 2 :=
      congrArg (fun value : ℝ =>
        value + 2 * (4 * (16 * r)) + (16 * r) ^ 2) hconstant
    _ = 16 + 128 * r + (16 * r) ^ 2 :=
      congrArg (fun value : ℝ => 16 + value + (16 * r) ^ 2) hlinear
    _ = 16 + 128 * r + 256 * r ^ 2 :=
      congrArg (fun value : ℝ => 16 + 128 * r + value) hquadratic

theorem Real.transition_quadratic_core_cross
    (r : ℝ) :
    2 * ((4 + 16 * r) * (8 * r ^ 2)) =
      64 * r ^ 2 + 256 * r ^ 3 := by
  have hpower : r * r ^ 2 = r ^ 3 := by
    exact Eq.trans (mul_comm r (r ^ 2)) (pow_succ r 2).symm
  have hfirst : 4 * (8 * r ^ 2) = 32 * r ^ 2 :=
    Real.transition_four_mul_eight_mul (r ^ 2)
  have hsecond : (16 * r) * (8 * r ^ 2) = 128 * r ^ 3 := by
    calc
      (16 * r) * (8 * r ^ 2) = (16 * 8) * (r * r ^ 2) :=
        Real.transition_scaled_product 16 8 r (r ^ 2)
      _ = 128 * r ^ 3 :=
        congrArg₂ (fun coefficient power : ℝ => coefficient * power)
          Real.transition_sixteen_mul_eight hpower
  have hproduct :
      (4 + 16 * r) * (8 * r ^ 2) =
        32 * r ^ 2 + 128 * r ^ 3 := by
    exact Eq.trans (add_mul 4 (16 * r) (8 * r ^ 2))
      (congrArg₂ (fun first second : ℝ => first + second)
        hfirst hsecond)
  have hleft : 2 * (32 * r ^ 2) = 64 * r ^ 2 := by
    calc
      2 * (32 * r ^ 2) = (2 * 32) * r ^ 2 :=
        (mul_assoc 2 32 (r ^ 2)).symm
      _ = 64 * r ^ 2 :=
        congrArg (fun coefficient : ℝ => coefficient * r ^ 2)
          Real.transition_two_mul_thirtytwo
  have hright : 2 * (128 * r ^ 3) = 256 * r ^ 3 := by
    calc
      2 * (128 * r ^ 3) = (2 * 128) * r ^ 3 :=
        (mul_assoc 2 128 (r ^ 3)).symm
      _ = 256 * r ^ 3 :=
        congrArg (fun coefficient : ℝ => coefficient * r ^ 3)
          Real.transition_two_mul_onehundredtwentyeight
  calc
    2 * ((4 + 16 * r) * (8 * r ^ 2)) =
        2 * (32 * r ^ 2 + 128 * r ^ 3) :=
      congrArg (fun value : ℝ => 2 * value) hproduct
    _ = 2 * (32 * r ^ 2) + 2 * (128 * r ^ 3) :=
      mul_add 2 (32 * r ^ 2) (128 * r ^ 3)
    _ = 64 * r ^ 2 + 256 * r ^ 3 :=
      congrArg₂ (fun first second : ℝ => first + second)
        hleft hright

theorem Real.transition_eight_r_sq_square
    (r : ℝ) :
    (8 * r ^ 2) ^ 2 = 64 * r ^ 4 := by
  calc
    (8 * r ^ 2) ^ 2 = (8 * r ^ 2) * (8 * r ^ 2) :=
      pow_two (8 * r ^ 2)
    _ = (8 * 8) * (r ^ 2 * r ^ 2) :=
      Real.transition_scaled_product 8 8 (r ^ 2) (r ^ 2)
    _ = 64 * r ^ 4 :=
      congrArg₂ (fun coefficient power : ℝ => coefficient * power)
        Real.transition_eight_mul_eight (pow_add r 2 2).symm

theorem Real.transition_quadratic_core_square
    (r : ℝ) :
    (4 + 16 * r + 8 * r ^ 2) ^ 2 =
      16 + 128 * r + 320 * r ^ 2 + 256 * r ^ 3 + 64 * r ^ 4 := by
  have hlinear := Real.transition_linear_core_square r
  have hcross := Real.transition_quadratic_core_cross r
  have hlast := Real.transition_eight_r_sq_square r
  have hsubstitute :
      (4 + 16 * r) ^ 2 +
          2 * ((4 + 16 * r) * (8 * r ^ 2)) +
          (8 * r ^ 2) ^ 2 =
        (16 + 128 * r + 256 * r ^ 2) +
          (64 * r ^ 2 + 256 * r ^ 3) + 64 * r ^ 4 := by
    exact congrArg₂ (fun first second : ℝ => first + second)
      (congrArg₂ (fun first second : ℝ => first + second)
        hlinear hcross) hlast
  have hcoefficient :
      256 * r ^ 2 + 64 * r ^ 2 = 320 * r ^ 2 := by
    exact (add_mul 256 64 (r ^ 2)).symm.trans
      (congrArg (fun coefficient : ℝ => coefficient * r ^ 2)
        Real.transition_twohundredfiftysix_add_sixtyfour)
  calc
    (4 + 16 * r + 8 * r ^ 2) ^ 2 =
        (4 + 16 * r) ^ 2 +
          2 * ((4 + 16 * r) * (8 * r ^ 2)) +
          (8 * r ^ 2) ^ 2 :=
      Real.transition_add_square_expansion
        (4 + 16 * r) (8 * r ^ 2)
    _ = (16 + 128 * r + 256 * r ^ 2) +
        (64 * r ^ 2 + 256 * r ^ 3) + 64 * r ^ 4 :=
      hsubstitute
    _ = 16 + 128 * r + (256 * r ^ 2 + 64 * r ^ 2) +
        256 * r ^ 3 + 64 * r ^ 4 :=
      congrArg (fun value : ℝ => value + 64 * r ^ 4)
        (Real.transition_collect_middle_pair
          16 (128 * r) (256 * r ^ 2)
          (64 * r ^ 2) (256 * r ^ 3))
    _ = 16 + 128 * r + 320 * r ^ 2 +
        256 * r ^ 3 + 64 * r ^ 4 :=
      congrArg
        (fun value : ℝ =>
          16 + 128 * r + value + 256 * r ^ 3 + 64 * r ^ 4)
        hcoefficient

theorem Real.transition_cubic_core_cross
    (r : ℝ) :
    2 * ((4 + 16 * r + 8 * r ^ 2) * r ^ 3) =
      8 * r ^ 3 + 32 * r ^ 4 + 16 * r ^ 5 := by
  have h4 : (16 * r) * r ^ 3 = 16 * r ^ 4 := by
    calc
      (16 * r) * r ^ 3 = 16 * (r * r ^ 3) :=
        mul_assoc 16 r (r ^ 3)
      _ = 16 * (r ^ 3 * r) :=
        congrArg (fun value : ℝ => 16 * value)
          (mul_comm r (r ^ 3))
      _ = 16 * r ^ 4 :=
        congrArg (fun value : ℝ => 16 * value)
          (pow_succ r 3).symm
  have h5 : (8 * r ^ 2) * r ^ 3 = 8 * r ^ 5 := by
    calc
      (8 * r ^ 2) * r ^ 3 = 8 * (r ^ 2 * r ^ 3) :=
        mul_assoc 8 (r ^ 2) (r ^ 3)
      _ = 8 * r ^ 5 :=
        congrArg (fun value : ℝ => 8 * value)
          (pow_add r 2 3).symm
  have hproduct :
      (4 + 16 * r + 8 * r ^ 2) * r ^ 3 =
        4 * r ^ 3 + 16 * r ^ 4 + 8 * r ^ 5 := by
    calc
      (4 + 16 * r + 8 * r ^ 2) * r ^ 3 =
          (4 + 16 * r) * r ^ 3 + (8 * r ^ 2) * r ^ 3 :=
        add_mul (4 + 16 * r) (8 * r ^ 2) (r ^ 3)
      _ = (4 * r ^ 3 + (16 * r) * r ^ 3) +
          (8 * r ^ 2) * r ^ 3 :=
        congrArg (fun value : ℝ => value + (8 * r ^ 2) * r ^ 3)
          (add_mul 4 (16 * r) (r ^ 3))
      _ = 4 * r ^ 3 + 16 * r ^ 4 + 8 * r ^ 5 :=
        congrArg₂ (fun first second : ℝ => first + second)
          (congrArg (fun value : ℝ => 4 * r ^ 3 + value) h4) h5
  have hfirst : 2 * (4 * r ^ 3) = 8 * r ^ 3 := by
    calc
      2 * (4 * r ^ 3) = (2 * 4) * r ^ 3 :=
        (mul_assoc 2 4 (r ^ 3)).symm
      _ = 8 * r ^ 3 :=
        congrArg (fun coefficient : ℝ => coefficient * r ^ 3)
          Real.transition_two_mul_four
  have hsecond : 2 * (16 * r ^ 4) = 32 * r ^ 4 := by
    calc
      2 * (16 * r ^ 4) = (2 * 16) * r ^ 4 :=
        (mul_assoc 2 16 (r ^ 4)).symm
      _ = 32 * r ^ 4 :=
        congrArg (fun coefficient : ℝ => coefficient * r ^ 4)
          Real.transition_two_mul_sixteen
  have hthird : 2 * (8 * r ^ 5) = 16 * r ^ 5 := by
    calc
      2 * (8 * r ^ 5) = (2 * 8) * r ^ 5 :=
        (mul_assoc 2 8 (r ^ 5)).symm
      _ = 16 * r ^ 5 :=
        congrArg (fun coefficient : ℝ => coefficient * r ^ 5)
          Real.transition_two_mul_eight
  calc
    2 * ((4 + 16 * r + 8 * r ^ 2) * r ^ 3) =
        2 * (4 * r ^ 3 + 16 * r ^ 4 + 8 * r ^ 5) :=
      congrArg (fun value : ℝ => 2 * value) hproduct
    _ = 2 * (4 * r ^ 3 + 16 * r ^ 4) +
        2 * (8 * r ^ 5) :=
      mul_add 2 (4 * r ^ 3 + 16 * r ^ 4) (8 * r ^ 5)
    _ = (2 * (4 * r ^ 3) + 2 * (16 * r ^ 4)) +
        2 * (8 * r ^ 5) :=
      congrArg (fun value : ℝ => value + 2 * (8 * r ^ 5))
        (mul_add 2 (4 * r ^ 3) (16 * r ^ 4))
    _ = 8 * r ^ 3 + 32 * r ^ 4 + 16 * r ^ 5 :=
      congrArg₂ (fun first second : ℝ => first + second)
        (congrArg₂ (fun first second : ℝ => first + second)
          hfirst hsecond) hthird

theorem Real.transition_cubic_core_square
    (r : ℝ) :
    (4 + 16 * r + 8 * r ^ 2 + r ^ 3) ^ 2 =
      16 + 128 * r + 320 * r ^ 2 + 264 * r ^ 3 +
        96 * r ^ 4 + 16 * r ^ 5 + r ^ 6 := by
  have hquadratic := Real.transition_quadratic_core_square r
  have hcross := Real.transition_cubic_core_cross r
  have hlast : (r ^ 3) ^ 2 = r ^ 6 := by
    exact Eq.trans (pow_two (r ^ 3)) (pow_add r 3 3).symm
  have hsubstitute :
      (4 + 16 * r + 8 * r ^ 2) ^ 2 +
          2 * ((4 + 16 * r + 8 * r ^ 2) * r ^ 3) +
          (r ^ 3) ^ 2 =
        (16 + 128 * r + 320 * r ^ 2 +
            256 * r ^ 3 + 64 * r ^ 4) +
          (8 * r ^ 3 + 32 * r ^ 4 + 16 * r ^ 5) + r ^ 6 := by
    exact congrArg₂ (fun first second : ℝ => first + second)
      (congrArg₂ (fun first second : ℝ => first + second)
        hquadratic hcross) hlast
  have h264 : 256 * r ^ 3 + 8 * r ^ 3 = 264 * r ^ 3 := by
    exact (add_mul 256 8 (r ^ 3)).symm.trans
      (congrArg (fun coefficient : ℝ => coefficient * r ^ 3)
        Real.transition_twohundredfiftysix_add_eight)
  have h96 : 64 * r ^ 4 + 32 * r ^ 4 = 96 * r ^ 4 := by
    exact (add_mul 64 32 (r ^ 4)).symm.trans
      (congrArg (fun coefficient : ℝ => coefficient * r ^ 4)
        Real.transition_sixtyfour_add_thirtytwo)
  let low := 16 + 128 * r + 320 * r ^ 2
  calc
    (4 + 16 * r + 8 * r ^ 2 + r ^ 3) ^ 2 =
        (4 + 16 * r + 8 * r ^ 2) ^ 2 +
          2 * ((4 + 16 * r + 8 * r ^ 2) * r ^ 3) +
          (r ^ 3) ^ 2 :=
      Real.transition_add_square_expansion
        (4 + 16 * r + 8 * r ^ 2) (r ^ 3)
    _ = (low + 256 * r ^ 3 + 64 * r ^ 4) +
        (8 * r ^ 3 + 32 * r ^ 4 + 16 * r ^ 5) + r ^ 6 :=
      hsubstitute
    _ = low + (256 * r ^ 3 + 8 * r ^ 3) +
        (64 * r ^ 4 + 32 * r ^ 4) + 16 * r ^ 5 + r ^ 6 :=
      congrArg (fun value : ℝ => value + r ^ 6)
        (Real.transition_collect_two_pairs
          low (256 * r ^ 3) (64 * r ^ 4)
          (8 * r ^ 3) (32 * r ^ 4) (16 * r ^ 5))
    _ = low + 264 * r ^ 3 + 96 * r ^ 4 + 16 * r ^ 5 + r ^ 6 :=
      congrArg₂
        (fun first second : ℝ =>
          low + first + second + 16 * r ^ 5 + r ^ 6)
        h264 h96

theorem Real.transitionShiftedCore_square_eq_expansion
    (r : ℝ) :
    Real.transitionShiftedCore r ^ 2 =
      Real.transitionShiftedCoreSquareExpansion r := by
  unfold Real.transitionShiftedCore
  unfold Real.transitionShiftedCoreSquareExpansion
  calc
    (r ^ 3 + 8 * r ^ 2 + 16 * r + 4) ^ 2 =
        (4 + 16 * r + 8 * r ^ 2 + r ^ 3) ^ 2 :=
      congrArg (fun value : ℝ => value ^ 2)
        (Real.transition_reverse_four_add
          (r ^ 3) (8 * r ^ 2) (16 * r) 4)
    _ = 16 + 128 * r + 320 * r ^ 2 + 264 * r ^ 3 +
        96 * r ^ 4 + 16 * r ^ 5 + r ^ 6 :=
      Real.transition_cubic_core_square r

theorem Real.transition_four_mul_six :
    (4 : ℝ) * 6 = 24 := by
  exact Real.transition_nat_cast_mul 4 6 24 rfl

theorem Real.transition_four_mul_nine :
    (4 : ℝ) * 9 = 36 := by
  exact Real.transition_nat_cast_mul 4 9 36 rfl

theorem Real.transition_thirtysix_mul_four :
    (36 : ℝ) * 4 = 144 := by
  exact Real.transition_nat_cast_mul 36 4 144 rfl

theorem Real.transition_twentyfour_mul_four :
    (24 : ℝ) * 4 = 96 := by
  exact Real.transition_nat_cast_mul 24 4 96 rfl

theorem Real.transition_thirtysix_add_ninetysix :
    (36 : ℝ) + 96 = 132 := by
  exact Real.transition_nat_cast_add 36 96 132 rfl

theorem Real.transition_twentyfour_add_sixteen :
    (24 : ℝ) + 16 = 40 := by
  exact Real.transition_nat_cast_add 24 16 40 rfl

theorem Real.transition_scaled_penalty_quadratic
    (r : ℝ) :
    4 * (r ^ 2 + 6 * r + 9) = 36 + 24 * r + 4 * r ^ 2 := by
  have hlinear : 4 * (6 * r) = 24 * r := by
    calc
      4 * (6 * r) = (4 * 6) * r := (mul_assoc 4 6 r).symm
      _ = 24 * r :=
        congrArg (fun coefficient : ℝ => coefficient * r)
          Real.transition_four_mul_six
  have hdescending :
      4 * (r ^ 2 + 6 * r + 9) = 4 * r ^ 2 + 24 * r + 36 := by
    calc
      4 * (r ^ 2 + 6 * r + 9) =
          4 * (r ^ 2 + 6 * r) + 4 * 9 :=
        mul_add 4 (r ^ 2 + 6 * r) 9
      _ = (4 * r ^ 2 + 4 * (6 * r)) + 4 * 9 :=
        congrArg (fun value : ℝ => value + 4 * 9)
          (mul_add 4 (r ^ 2) (6 * r))
      _ = 4 * r ^ 2 + 24 * r + 36 :=
        congrArg₂ (fun first second : ℝ => 4 * r ^ 2 + first + second)
          hlinear Real.transition_four_mul_nine
  exact Eq.trans hdescending
    (Real.transition_reverse_three_add
      (4 * r ^ 2) (24 * r) 36)

theorem Real.transition_penalty_constant_product
    (r : ℝ) :
    36 * (r + 4) = 144 + 36 * r := by
  calc
    36 * (r + 4) = 36 * r + 36 * 4 := mul_add 36 r 4
    _ = 36 * r + 144 :=
      congrArg (fun value : ℝ => 36 * r + value)
        Real.transition_thirtysix_mul_four
    _ = 144 + 36 * r := add_comm (36 * r) 144

theorem Real.transition_penalty_linear_product
    (r : ℝ) :
    (24 * r) * (r + 4) = 96 * r + 24 * r ^ 2 := by
  have hquadratic : (24 * r) * r = 24 * r ^ 2 := by
    calc
      (24 * r) * r = 24 * (r * r) := mul_assoc 24 r r
      _ = 24 * r ^ 2 :=
        congrArg (fun value : ℝ => 24 * value) (pow_two r).symm
  have hlinear : (24 * r) * 4 = 96 * r := by
    calc
      (24 * r) * 4 = 24 * (r * 4) := mul_assoc 24 r 4
      _ = 24 * (4 * r) :=
        congrArg (fun value : ℝ => 24 * value) (mul_comm r 4)
      _ = (24 * 4) * r := (mul_assoc 24 4 r).symm
      _ = 96 * r :=
        congrArg (fun coefficient : ℝ => coefficient * r)
          Real.transition_twentyfour_mul_four
  calc
    (24 * r) * (r + 4) = (24 * r) * r + (24 * r) * 4 :=
      mul_add (24 * r) r 4
    _ = 24 * r ^ 2 + 96 * r :=
      congrArg₂ (fun first second : ℝ => first + second)
        hquadratic hlinear
    _ = 96 * r + 24 * r ^ 2 :=
      add_comm (24 * r ^ 2) (96 * r)

theorem Real.transition_penalty_quadratic_product
    (r : ℝ) :
    (4 * r ^ 2) * (r + 4) = 16 * r ^ 2 + 4 * r ^ 3 := by
  have hcubic : (4 * r ^ 2) * r = 4 * r ^ 3 := by
    calc
      (4 * r ^ 2) * r = 4 * (r ^ 2 * r) :=
        mul_assoc 4 (r ^ 2) r
      _ = 4 * r ^ 3 :=
        congrArg (fun value : ℝ => 4 * value) (pow_succ r 2).symm
  have hquadratic : (4 * r ^ 2) * 4 = 16 * r ^ 2 := by
    calc
      (4 * r ^ 2) * 4 = 4 * (r ^ 2 * 4) :=
        mul_assoc 4 (r ^ 2) 4
      _ = 4 * (4 * r ^ 2) :=
        congrArg (fun value : ℝ => 4 * value) (mul_comm (r ^ 2) 4)
      _ = (4 * 4) * r ^ 2 := (mul_assoc 4 4 (r ^ 2)).symm
      _ = 16 * r ^ 2 :=
        congrArg (fun coefficient : ℝ => coefficient * r ^ 2)
          Real.transition_four_mul_four
  calc
    (4 * r ^ 2) * (r + 4) =
        (4 * r ^ 2) * r + (4 * r ^ 2) * 4 :=
      mul_add (4 * r ^ 2) r 4
    _ = 4 * r ^ 3 + 16 * r ^ 2 :=
      congrArg₂ (fun first second : ℝ => first + second)
        hcubic hquadratic
    _ = 16 * r ^ 2 + 4 * r ^ 3 :=
      add_comm (4 * r ^ 3) (16 * r ^ 2)

theorem Real.transition_penalty_before_final_r
    (r : ℝ) :
    (36 + 24 * r + 4 * r ^ 2) * (r + 4) =
      144 + 132 * r + 40 * r ^ 2 + 4 * r ^ 3 := by
  have hconstant := Real.transition_penalty_constant_product r
  have hlinear := Real.transition_penalty_linear_product r
  have hquadratic := Real.transition_penalty_quadratic_product r
  have hexpand :
      (36 + 24 * r + 4 * r ^ 2) * (r + 4) =
        (144 + 36 * r) + (96 * r + 24 * r ^ 2) +
          (16 * r ^ 2 + 4 * r ^ 3) := by
    calc
      (36 + 24 * r + 4 * r ^ 2) * (r + 4) =
          (36 + 24 * r) * (r + 4) + (4 * r ^ 2) * (r + 4) :=
        add_mul (36 + 24 * r) (4 * r ^ 2) (r + 4)
      _ = (36 * (r + 4) + (24 * r) * (r + 4)) +
          (4 * r ^ 2) * (r + 4) :=
        congrArg (fun value : ℝ => value + (4 * r ^ 2) * (r + 4))
          (add_mul 36 (24 * r) (r + 4))
      _ = (144 + 36 * r) + (96 * r + 24 * r ^ 2) +
          (16 * r ^ 2 + 4 * r ^ 3) :=
        congrArg₂ (fun first second : ℝ => first + second)
          (congrArg₂ (fun first second : ℝ => first + second)
            hconstant hlinear) hquadratic
  have h132 : 36 * r + 96 * r = 132 * r := by
    exact (add_mul 36 96 r).symm.trans
      (congrArg (fun coefficient : ℝ => coefficient * r)
        Real.transition_thirtysix_add_ninetysix)
  have h40 : 24 * r ^ 2 + 16 * r ^ 2 = 40 * r ^ 2 := by
    exact (add_mul 24 16 (r ^ 2)).symm.trans
      (congrArg (fun coefficient : ℝ => coefficient * r ^ 2)
        Real.transition_twentyfour_add_sixteen)
  calc
    (36 + 24 * r + 4 * r ^ 2) * (r + 4) =
        (144 + 36 * r) + (96 * r + 24 * r ^ 2) +
          (16 * r ^ 2 + 4 * r ^ 3) := hexpand
    _ = (144 + (36 * r + 96 * r) + 24 * r ^ 2) +
        (16 * r ^ 2 + 4 * r ^ 3) :=
      congrArg
        (fun value : ℝ => value + (16 * r ^ 2 + 4 * r ^ 3))
        (Real.transition_collect_one_pair
          144 (36 * r) (96 * r) (24 * r ^ 2))
    _ = (144 + 132 * r + 24 * r ^ 2) +
        (16 * r ^ 2 + 4 * r ^ 3) :=
      congrArg
        (fun value : ℝ => 144 + value + 24 * r ^ 2 +
          (16 * r ^ 2 + 4 * r ^ 3))
        h132
    _ = 144 + 132 * r + (24 * r ^ 2 + 16 * r ^ 2) +
        4 * r ^ 3 :=
      Real.transition_collect_middle_pair
        144 (132 * r) (24 * r ^ 2) (16 * r ^ 2) (4 * r ^ 3)
    _ = 144 + 132 * r + 40 * r ^ 2 + 4 * r ^ 3 :=
      congrArg (fun value : ℝ => 144 + 132 * r + value + 4 * r ^ 3)
        h40

theorem Real.transition_penalty_final_r
    (r : ℝ) :
    (144 + 132 * r + 40 * r ^ 2 + 4 * r ^ 3) * r =
      144 * r + 132 * r ^ 2 + 40 * r ^ 3 + 4 * r ^ 4 := by
  have h2 : (132 * r) * r = 132 * r ^ 2 := by
    calc
      (132 * r) * r = 132 * (r * r) := mul_assoc 132 r r
      _ = 132 * r ^ 2 :=
        congrArg (fun value : ℝ => 132 * value) (pow_two r).symm
  have h3 : (40 * r ^ 2) * r = 40 * r ^ 3 := by
    calc
      (40 * r ^ 2) * r = 40 * (r ^ 2 * r) :=
        mul_assoc 40 (r ^ 2) r
      _ = 40 * r ^ 3 :=
        congrArg (fun value : ℝ => 40 * value) (pow_succ r 2).symm
  have h4 : (4 * r ^ 3) * r = 4 * r ^ 4 := by
    calc
      (4 * r ^ 3) * r = 4 * (r ^ 3 * r) :=
        mul_assoc 4 (r ^ 3) r
      _ = 4 * r ^ 4 :=
        congrArg (fun value : ℝ => 4 * value) (pow_succ r 3).symm
  calc
    (144 + 132 * r + 40 * r ^ 2 + 4 * r ^ 3) * r =
        (144 + 132 * r + 40 * r ^ 2) * r + (4 * r ^ 3) * r :=
      add_mul (144 + 132 * r + 40 * r ^ 2) (4 * r ^ 3) r
    _ = ((144 + 132 * r) * r + (40 * r ^ 2) * r) +
        (4 * r ^ 3) * r :=
      congrArg (fun value : ℝ => value + (4 * r ^ 3) * r)
        (add_mul (144 + 132 * r) (40 * r ^ 2) r)
    _ = ((144 * r + (132 * r) * r) + (40 * r ^ 2) * r) +
        (4 * r ^ 3) * r :=
      congrArg (fun value : ℝ => value + (40 * r ^ 2) * r +
        (4 * r ^ 3) * r) (add_mul 144 (132 * r) r)
    _ = 144 * r + 132 * r ^ 2 + 40 * r ^ 3 + 4 * r ^ 4 :=
      congrArg₂ (fun first second : ℝ => first + second)
        (congrArg₂ (fun first second : ℝ => first + second)
          (congrArg (fun value : ℝ => 144 * r + value) h2) h3) h4

theorem Real.transitionShiftedPenalty_eq_expansion
    (r : ℝ) :
    Real.transitionShiftedPenalty r =
      Real.transitionShiftedPenaltyExpansion r := by
  unfold Real.transitionShiftedPenalty
  unfold Real.transitionShiftedPenaltyExpansion
  have hsquare : (r + 3) ^ 2 = r ^ 2 + 6 * r + 9 := by
    have hdouble : 3 * r + r * 3 = 6 * r := by
      calc
        3 * r + r * 3 = 3 * r + 3 * r :=
          congrArg (fun value : ℝ => 3 * r + value) (mul_comm r 3)
        _ = (3 + 3) * r := (add_mul 3 3 r).symm
        _ = 6 * r :=
          congrArg (fun coefficient : ℝ => coefficient * r)
            Real.transition_three_add_three
    calc
      (r + 3) ^ 2 = (r + 3) * (r + 3) := pow_two (r + 3)
      _ = (r * r + 3 * r) + (r * 3 + 3 * 3) := by
        exact (mul_add (r + 3) r 3).trans
          (congrArg₂ (fun first second : ℝ => first + second)
            (add_mul r 3 r)
            (add_mul r 3 3))
      _ = r * r + (3 * r + r * 3) + 3 * 3 :=
        Real.transition_collect_one_pair
          (r * r) (3 * r) (r * 3) (3 * 3)
      _ = r ^ 2 + 6 * r + 9 :=
        congrArg₂ (fun first second : ℝ => first + second)
          (congrArg₂ (fun first second : ℝ => first + second)
            (pow_two r).symm hdouble)
          Real.transition_three_mul_three
  calc
    4 * (r + 3) ^ 2 * (r + 4) * r =
        4 * (r ^ 2 + 6 * r + 9) * (r + 4) * r :=
      congrArg (fun value : ℝ => 4 * value * (r + 4) * r) hsquare
    _ = (36 + 24 * r + 4 * r ^ 2) * (r + 4) * r :=
      congrArg (fun value : ℝ => value * (r + 4) * r)
        (Real.transition_scaled_penalty_quadratic r)
    _ = (144 + 132 * r + 40 * r ^ 2 + 4 * r ^ 3) * r :=
      congrArg (fun value : ℝ => value * r)
        (Real.transition_penalty_before_final_r r)
    _ = 144 * r + 132 * r ^ 2 + 40 * r ^ 3 + 4 * r ^ 4 :=
      Real.transition_penalty_final_r r

theorem Real.transition_four_coefficient_subtraction
    (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℝ) :
    (a₁ + a₂ + a₃ + a₄) - (b₁ + b₂ + b₃ + b₄) =
      (a₁ - b₁) + (a₂ - b₂) + (a₃ - b₃) + (a₄ - b₄) := by
  have houter := (sub_add_sub_comm
    (a₁ + a₂ + a₃) (b₁ + b₂ + b₃) a₄ b₄).symm
  have hmiddle := congrArg
    (fun value : ℝ => value + (a₄ - b₄))
    (sub_add_sub_comm (a₁ + a₂) (b₁ + b₂) a₃ b₃).symm
  have hinner := congrArg
    (fun value : ℝ => value + (a₃ - b₃) + (a₄ - b₄))
    (sub_add_sub_comm a₁ b₁ a₂ b₂).symm
  exact Eq.trans houter (Eq.trans hmiddle hinner)

theorem Real.transition_reassociate_five_head
    (a₀ a₁ a₂ a₃ a₄ : ℝ) :
    a₀ + a₁ + a₂ + a₃ + a₄ =
      a₀ + (a₁ + a₂ + a₃ + a₄) := by
  calc
    a₀ + a₁ + a₂ + a₃ + a₄ =
        a₀ + (a₁ + a₂) + a₃ + a₄ :=
      congrArg (fun value : ℝ => value + a₃ + a₄)
        (add_assoc a₀ a₁ a₂)
    _ = a₀ + (a₁ + a₂ + a₃) + a₄ :=
      congrArg (fun value : ℝ => value + a₄)
        (add_assoc a₀ (a₁ + a₂) a₃)
    _ = a₀ + (a₁ + a₂ + a₃ + a₄) :=
      add_assoc a₀ (a₁ + a₂ + a₃) a₄

theorem Real.transition_five_coefficient_subtraction
    (a₀ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℝ) :
    (a₀ + a₁ + a₂ + a₃ + a₄) -
        (b₁ + b₂ + b₃ + b₄) =
      a₀ + (a₁ - b₁) + (a₂ - b₂) +
        (a₃ - b₃) + (a₄ - b₄) := by
  let lowerA := a₁ + a₂ + a₃ + a₄
  let lowerB := b₁ + b₂ + b₃ + b₄
  have hfour := Real.transition_four_coefficient_subtraction
    a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄
  change lowerA - lowerB =
    (a₁ - b₁) + (a₂ - b₂) + (a₃ - b₃) + (a₄ - b₄) at hfour
  calc
    (a₀ + a₁ + a₂ + a₃ + a₄) -
        (b₁ + b₂ + b₃ + b₄) =
      (a₀ + lowerA) - (0 + lowerB) :=
        congrArg₂ (fun first second : ℝ => first - second)
          (Real.transition_reassociate_five_head
            a₀ a₁ a₂ a₃ a₄)
          (zero_add lowerB).symm
    _ = (a₀ - 0) + (lowerA - lowerB) :=
      (sub_add_sub_comm a₀ 0 lowerA lowerB).symm
    _ = a₀ +
        ((a₁ - b₁) + (a₂ - b₂) + (a₃ - b₃) + (a₄ - b₄)) :=
      congrArg₂ (fun first second : ℝ => first + second)
        (sub_zero a₀) hfour
    _ = a₀ + (a₁ - b₁) + (a₂ - b₂) +
        (a₃ - b₃) + (a₄ - b₄) :=
      (Real.transition_reassociate_five_head
        a₀ (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) (a₄ - b₄)).symm

theorem Real.transition_seven_sub_four_coefficients
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ : ℝ) :
    (a₀ + a₁ + a₂ + a₃ + a₄ + a₅ + a₆) -
        (b₁ + b₂ + b₃ + b₄) =
      a₀ + (a₁ - b₁) + (a₂ - b₂) + (a₃ - b₃) +
        (a₄ - b₄) + a₅ + a₆ := by
  let low := a₀ + a₁ + a₂ + a₃ + a₄
  let high := a₅ + a₆
  let penalty := b₁ + b₂ + b₃ + b₄
  have hlow := Real.transition_five_coefficient_subtraction
    a₀ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄
  change low - penalty =
    a₀ + (a₁ - b₁) + (a₂ - b₂) + (a₃ - b₃) +
      (a₄ - b₄) at hlow
  let collected :=
    a₀ + (a₁ - b₁) + (a₂ - b₂) + (a₃ - b₃) +
      (a₄ - b₄)
  change low - penalty = collected at hlow
  calc
    (a₀ + a₁ + a₂ + a₃ + a₄ + a₅ + a₆) -
        (b₁ + b₂ + b₃ + b₄) =
      (low + high) - (penalty + 0) :=
        congrArg₂ (fun first second : ℝ => first - second)
          (add_assoc low a₅ a₆) (add_zero penalty).symm
    _ = (low - penalty) + (high - 0) :=
      (sub_add_sub_comm low penalty high 0).symm
    _ = collected + high :=
      congrArg₂ (fun first second : ℝ => first + second)
        hlow (sub_zero high)
    _ = collected + a₅ + a₆ :=
      (add_assoc collected a₅ a₆).symm

theorem Real.transition_onehundredtwentyeight_add_sixteen :
    (128 : ℝ) + 16 = 144 := by
  exact Real.transition_nat_cast_add 128 16 144 rfl

theorem Real.transition_onehundredeightyeight_add_onehundredthirtytwo :
    (188 : ℝ) + 132 = 320 := by
  exact Real.transition_nat_cast_add 188 132 320 rfl

theorem Real.transition_twohundredtwentyfour_add_forty :
    (224 : ℝ) + 40 = 264 := by
  exact Real.transition_nat_cast_add 224 40 264 rfl

theorem Real.transition_ninetytwo_add_four :
    (92 : ℝ) + 4 = 96 := by
  exact Real.transition_nat_cast_add 92 4 96 rfl

theorem Real.transition_onehundredtwentyeight_sub_onehundredfortyfour :
    (128 : ℝ) - 144 = -16 := by
  have hleft : ((128 : ℝ) - 144) + 144 = 128 :=
    sub_add_cancel 128 144
  have hright : (-16 : ℝ) + 144 = 128 := by
    calc
      (-16 : ℝ) + 144 = -16 + (16 + 128) :=
        congrArg (fun value : ℝ => -16 + value)
          (Real.transition_nat_cast_add 16 128 144 rfl).symm
      _ = (-16 + 16) + 128 := (add_assoc (-16) 16 128).symm
      _ = 0 + 128 :=
        congrArg (fun value : ℝ => value + 128) (neg_add_cancel 16)
      _ = 128 := zero_add 128
  have hequal : ((128 : ℝ) - 144) + 144 = (-16 : ℝ) + 144 :=
    Eq.trans hleft hright.symm
  exact add_right_cancel hequal

theorem Real.transition_threehundredtwenty_sub_onehundredthirtytwo :
    (320 : ℝ) - 132 = 188 := by
  have hsum :=
    Real.transition_onehundredeightyeight_add_onehundredthirtytwo
  calc
    (320 : ℝ) - 132 = (188 + 132) - 132 :=
      congrArg (fun value : ℝ => value - 132) hsum.symm
    _ = 188 := add_sub_cancel_right 188 132

theorem Real.transition_twohundredsixtyfour_sub_forty :
    (264 : ℝ) - 40 = 224 := by
  have hsum := Real.transition_twohundredtwentyfour_add_forty
  calc
    (264 : ℝ) - 40 = (224 + 40) - 40 :=
      congrArg (fun value : ℝ => value - 40) hsum.symm
    _ = 224 := add_sub_cancel_right 224 40

theorem Real.transition_ninetysix_sub_four :
    (96 : ℝ) - 4 = 92 := by
  have hsum := Real.transition_ninetytwo_add_four
  calc
    (96 : ℝ) - 4 = (92 + 4) - 4 :=
      congrArg (fun value : ℝ => value - 4) hsum.symm
    _ = 92 := add_sub_cancel_right 92 4

theorem Real.transition_discriminant_linear_coefficient
    (r : ℝ) :
    128 * r - 144 * r = -(16 * r) := by
  calc
    128 * r - 144 * r = (128 - 144) * r :=
      (sub_mul 128 144 r).symm
    _ = (-16) * r :=
      congrArg (fun coefficient : ℝ => coefficient * r)
        Real.transition_onehundredtwentyeight_sub_onehundredfortyfour
    _ = -(16 * r) := neg_mul 16 r

theorem Real.transition_discriminant_quadratic_coefficient
    (r : ℝ) :
    320 * r ^ 2 - 132 * r ^ 2 = 188 * r ^ 2 := by
  exact (sub_mul 320 132 (r ^ 2)).symm.trans
    (congrArg (fun coefficient : ℝ => coefficient * r ^ 2)
      Real.transition_threehundredtwenty_sub_onehundredthirtytwo)

theorem Real.transition_discriminant_cubic_coefficient
    (r : ℝ) :
    264 * r ^ 3 - 40 * r ^ 3 = 224 * r ^ 3 := by
  exact (sub_mul 264 40 (r ^ 3)).symm.trans
    (congrArg (fun coefficient : ℝ => coefficient * r ^ 3)
      Real.transition_twohundredsixtyfour_sub_forty)

theorem Real.transition_discriminant_quartic_coefficient
    (r : ℝ) :
    96 * r ^ 4 - 4 * r ^ 4 = 92 * r ^ 4 := by
  exact (sub_mul 96 4 (r ^ 4)).symm.trans
    (congrArg (fun coefficient : ℝ => coefficient * r ^ 4)
      Real.transition_ninetysix_sub_four)

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
  have hsubstitute :=
    congrArg₂ (fun first second : ℝ => first - second) hcore hpenalty
  have hlinear := Real.transition_discriminant_linear_coefficient r
  have hquadratic :=
    Real.transition_discriminant_quadratic_coefficient r
  have hcubic := Real.transition_discriminant_cubic_coefficient r
  have hquartic := Real.transition_discriminant_quartic_coefficient r
  calc
    Real.transitionShiftedCore r ^ 2 - Real.transitionShiftedPenalty r =
        (16 + 128 * r + 320 * r ^ 2 + 264 * r ^ 3 +
            96 * r ^ 4 + 16 * r ^ 5 + r ^ 6) -
          (144 * r + 132 * r ^ 2 + 40 * r ^ 3 + 4 * r ^ 4) :=
      hsubstitute
    _ = 16 + (128 * r - 144 * r) +
        (320 * r ^ 2 - 132 * r ^ 2) +
        (264 * r ^ 3 - 40 * r ^ 3) +
        (96 * r ^ 4 - 4 * r ^ 4) + 16 * r ^ 5 + r ^ 6 :=
      Real.transition_seven_sub_four_coefficients
        16 (128 * r) (320 * r ^ 2) (264 * r ^ 3)
        (96 * r ^ 4) (16 * r ^ 5) (r ^ 6)
        (144 * r) (132 * r ^ 2) (40 * r ^ 3) (4 * r ^ 4)
    _ = 16 + -(16 * r) +
        (320 * r ^ 2 - 132 * r ^ 2) +
        (264 * r ^ 3 - 40 * r ^ 3) +
        (96 * r ^ 4 - 4 * r ^ 4) + 16 * r ^ 5 + r ^ 6 :=
      congrArg (fun value : ℝ =>
        16 + value + (320 * r ^ 2 - 132 * r ^ 2) +
          (264 * r ^ 3 - 40 * r ^ 3) +
          (96 * r ^ 4 - 4 * r ^ 4) + 16 * r ^ 5 + r ^ 6) hlinear
    _ = 16 + -(16 * r) + 188 * r ^ 2 +
        (264 * r ^ 3 - 40 * r ^ 3) +
        (96 * r ^ 4 - 4 * r ^ 4) + 16 * r ^ 5 + r ^ 6 :=
      congrArg (fun value : ℝ =>
        16 + -(16 * r) + value +
          (264 * r ^ 3 - 40 * r ^ 3) +
          (96 * r ^ 4 - 4 * r ^ 4) + 16 * r ^ 5 + r ^ 6) hquadratic
    _ = 16 + -(16 * r) + 188 * r ^ 2 + 224 * r ^ 3 +
        (96 * r ^ 4 - 4 * r ^ 4) + 16 * r ^ 5 + r ^ 6 :=
      congrArg (fun value : ℝ =>
        16 + -(16 * r) + 188 * r ^ 2 + value +
          (96 * r ^ 4 - 4 * r ^ 4) + 16 * r ^ 5 + r ^ 6) hcubic
    _ = 16 + -(16 * r) + 188 * r ^ 2 + 224 * r ^ 3 +
        92 * r ^ 4 + 16 * r ^ 5 + r ^ 6 :=
      congrArg (fun value : ℝ =>
        16 + -(16 * r) + 188 * r ^ 2 + 224 * r ^ 3 +
          value + 16 * r ^ 5 + r ^ 6) hquartic
    _ = 16 - 16 * r + 188 * r ^ 2 + 224 * r ^ 3 +
        92 * r ^ 4 + 16 * r ^ 5 + r ^ 6 :=
      congrArg
        (fun value : ℝ =>
          value + 188 * r ^ 2 + 224 * r ^ 3 +
            92 * r ^ 4 + 16 * r ^ 5 + r ^ 6)
        (sub_eq_add_neg 16 (16 * r)).symm

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
