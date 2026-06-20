import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteFormula
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaUpperResidual
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Finite Abel-Plana algebra owners

This file owns algebraic and scalar-normalization lemmas used by the finite Abel-Plana asymptotic estimates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

/-- Additive regrouping used by the real factorial Stirling endpoint
normalization.  The variables are intentionally abstract: this is only the
bookkeeping that moves the factorial, endpoint, and `π` logarithms into their
standard places. -/
theorem Real.factorialStirlingEndpoint_final_regroup
    (A X Y Z U V : ℝ) :
    A + (-(X + Y - Z) + (-(U) + -(V))) =
      (A - (U + Y) - (X - Z)) - V := by
  have hleft_sub :
      X + Y - Z = X + Y + -Z :=
    sub_eq_add_neg (X + Y) Z
  have hneg_left :
      -(X + Y - Z) = -(X + Y) + Z := by
    calc
      -(X + Y - Z) = -(X + Y + -Z) := by
        exact congrArg Neg.neg hleft_sub
      _ = -(X + Y) + -(-Z) := neg_add (X + Y) (-Z)
      _ = -(X + Y) + Z := by
        exact congrArg (fun r : ℝ => -(X + Y) + r) (neg_neg Z)
  have hneg_xy :
      -(X + Y) = -X + -Y :=
    neg_add X Y
  have htarget_sub₁ :
      A - (U + Y) = A + -(U + Y) :=
    sub_eq_add_neg A (U + Y)
  have htarget_sub₂ :
      A - (U + Y) - (X - Z) =
        (A - (U + Y)) + -(X - Z) :=
    sub_eq_add_neg (A - (U + Y)) (X - Z)
  have htarget_sub₃ :
      (A - (U + Y) - (X - Z)) - V =
        (A - (U + Y) - (X - Z)) + -V :=
    sub_eq_add_neg (A - (U + Y) - (X - Z)) V
  have hneg_uy :
      -(U + Y) = -U + -Y :=
    neg_add U Y
  have hneg_xz :
      -(X - Z) = -X + Z := by
    calc
      -(X - Z) = -(X + -Z) := by
        exact congrArg Neg.neg (sub_eq_add_neg X Z)
      _ = -X + -(-Z) := neg_add X (-Z)
      _ = -X + Z := by
        exact congrArg (fun r : ℝ => -X + r) (neg_neg Z)
  have hleft_normal :
      A + (-(X + Y - Z) + (-(U) + -(V))) =
        A + ((-U + -Y) + (-X + Z) + -V) := by
    calc
      A + (-(X + Y - Z) + (-(U) + -(V))) =
          A + ((-(X + Y) + Z) + (-U + -V)) := by
        exact congrArg
          (fun r : ℝ => A + (r + (-U + -V)))
          hneg_left
      _ = A + (((-X + -Y) + Z) + (-U + -V)) := by
        exact congrArg
          (fun r : ℝ => A + ((r + Z) + (-U + -V)))
          hneg_xy
      _ = A + ((-U + -Y) + (-X + Z) + -V) := by
        calc
          A + (((-X + -Y) + Z) + (-U + -V)) =
              A + (((-X + -Y) + Z) + (-V + -U)) := by
            exact congrArg
              (fun r : ℝ => A + (((-X + -Y) + Z) + r))
              (add_comm (-U) (-V))
          _ = A + ((((-X + -Y) + Z) + -V) + -U) := by
            exact congrArg
              (fun r : ℝ => A + r)
              (add_assoc ((-X + -Y) + Z) (-V) (-U)).symm
          _ = A + (-U + (((-X + -Y) + Z) + -V)) := by
            exact congrArg
              (fun r : ℝ => A + r)
              (add_comm (((-X + -Y) + Z) + -V) (-U))
          _ = A + ((-U + -Y) + (-X + Z) + -V) := by
            exact
              Eq.symm
                (calc
                  A + ((-U + -Y) + (-X + Z) + -V) =
                      A + (((-U + -Y) + (-X + Z)) + -V) := rfl
                  _ = A + ((-U + -Y) + ((-X + Z) + -V)) := by
                    exact congrArg (fun r : ℝ => A + r)
                      (add_assoc (-U + -Y) (-X + Z) (-V))
                  _ = A + (-U + (-Y + ((-X + Z) + -V))) := by
                    exact congrArg (fun r : ℝ => A + r)
                      (add_assoc (-U) (-Y) ((-X + Z) + -V))
                  _ = A + (-U + (((-X + Z) + -V) + -Y)) := by
                    exact congrArg
                      (fun r : ℝ => A + (-U + r))
                      (add_comm (-Y) ((-X + Z) + -V))
                  _ = A + (-U + (((-X + Z) + (-V + -Y)))) := by
                    exact congrArg
                      (fun r : ℝ => A + (-U + r))
                      (add_assoc (-X + Z) (-V) (-Y))
                  _ = A + (-U + (((-X + Z) + (-Y + -V)))) := by
                    exact congrArg
                      (fun r : ℝ => A + (-U + ((-X + Z) + r)))
                      (add_comm (-V) (-Y))
                  _ = A + (-U + (((-X + Z) + -Y) + -V)) := by
                    exact congrArg
                      (fun r : ℝ => A + (-U + r))
                      (add_assoc (-X + Z) (-Y) (-V)).symm
                  _ = A + (-U + (((-X + -Y) + Z) + -V)) := by
                    have hneg_rotate :
                        (-X + Z) + -Y = (-X + -Y) + Z := by
                      calc
                        (-X + Z) + -Y = -X + (Z + -Y) := by
                          exact add_assoc (-X) Z (-Y)
                        _ = -X + (-Y + Z) := by
                          exact congrArg (fun r : ℝ => -X + r)
                            (add_comm Z (-Y))
                        _ = (-X + -Y) + Z := by
                          exact (add_assoc (-X) (-Y) Z).symm
                    exact congrArg
                      (fun r : ℝ => A + (-U + (r + -V)))
                      hneg_rotate)
  have hright_normal :
      (A - (U + Y) - (X - Z)) - V =
        A + ((-U + -Y) + (-X + Z) + -V) := by
    calc
      (A - (U + Y) - (X - Z)) - V =
          (A - (U + Y) - (X - Z)) + -V := htarget_sub₃
      _ = ((A - (U + Y)) + -(X - Z)) + -V := by
        exact congrArg (fun r : ℝ => r + -V) htarget_sub₂
      _ = ((A + -(U + Y)) + -(X - Z)) + -V := by
        exact congrArg
          (fun r : ℝ => (r + -(X - Z)) + -V)
          htarget_sub₁
      _ = ((A + (-U + -Y)) + -(X - Z)) + -V := by
        exact congrArg
          (fun r : ℝ => ((A + r) + -(X - Z)) + -V)
          hneg_uy
      _ = ((A + (-U + -Y)) + (-X + Z)) + -V := by
        exact congrArg
          (fun r : ℝ => ((A + (-U + -Y)) + r) + -V)
          hneg_xz
      _ = (A + ((-U + -Y) + (-X + Z))) + -V := by
        exact congrArg
          (fun r : ℝ => r + -V)
          (add_assoc A (-U + -Y) (-X + Z))
      _ = A + (((-U + -Y) + (-X + Z)) + -V) :=
        add_assoc A ((-U + -Y) + (-X + Z)) (-V)
      _ = A + ((-U + -Y) + (-X + Z) + -V) := rfl
  exact Eq.trans hleft_normal hright_normal.symm

/-- Subtracting a difference expands by adding the right endpoint. -/
theorem Complex.sub_sub_sub_eq_sub_sub_add
    (a b c d : ℂ) :
    (a - b) - (c - d) = a - b - c + d := by
  calc
    (a - b) - (c - d) = (a - b) + -(c - d) :=
      sub_eq_add_neg (a - b) (c - d)
    _ = (a - b) + (-c + d) := by
      have hneg : -(c - d) = -c + d := by
        calc
          -(c - d) = d - c := neg_sub c d
          _ = d + -c := sub_eq_add_neg d c
          _ = -c + d := add_comm d (-c)
      exact congrArg (fun z : ℂ => (a - b) + z) hneg
    _ = ((a - b) + -c) + d :=
      (add_assoc (a - b) (-c) d).symm
    _ = (a - b - c) + d := by
      exact congrArg (fun z : ℂ => z + d)
        (sub_eq_add_neg (a - b) c).symm

/-- Expanding the endpoint product in the finite Binet remainder. -/
theorem Complex.endpoint_product_expand
    (w M logwM : ℂ) :
    (w + M) * logwM = w * logwM + M * logwM := by
  exact add_mul w M logwM

/-- Removing a sum from the right of a subtraction removes the two summands
successively. -/
theorem Complex.sub_add_right_as_sub_sub
    (a b c : ℂ) :
    a - (b + c) = a - b - c := by
  calc
    a - (b + c) = a + -(b + c) :=
      sub_eq_add_neg a (b + c)
    _ = a + (-b + -c) := by
      exact congrArg (fun z : ℂ => a + z) (neg_add b c)
    _ = (a + -b) + -c :=
      (add_assoc a (-b) (-c)).symm
    _ = a - b - c := by
      exact congrArg (fun z : ℂ => z + -c)
        (sub_eq_add_neg a b).symm

/-- Subtracting a difference adds back the right-hand term. -/
theorem Complex.sub_sub_right_as_sub_add
    (a b c : ℂ) :
    a - (b - c) = a - b + c := by
  calc
    a - (b - c) = a - (b + -c) := by
      exact congrArg (fun z : ℂ => a - z) (sub_eq_add_neg b c)
    _ = a - b - (-c) :=
      Complex.sub_add_right_as_sub_sub a b (-c)
    _ = a - b + c := by
      exact congrArg (fun z : ℂ => a - b + z) (neg_neg c)

/-- Subtracting an expanded four-term endpoint expression exposes the four
successive additive contributions. -/
theorem Complex.endpoint_subtract_four_term_expand
    (p a b c d e f : ℂ) :
    p - (a - b - c + d) - e - f =
      p - a + b + c - d - e - f := by
  calc
    p - (a - b - c + d) - e - f =
        (p - (a - b - c) - d) - e - f := by
      exact congrArg (fun z : ℂ => z - e - f)
        (Complex.sub_add_right_as_sub_sub p (a - b - c) d)
    _ = ((p - (a - b) + c) - d) - e - f := by
      exact congrArg (fun z : ℂ => (z - d) - e - f)
        (Complex.sub_sub_right_as_sub_add p (a - b) c)
    _ = (((p - a + b) + c) - d) - e - f := by
      exact congrArg (fun z : ℂ => (z + c - d) - e - f)
        (Complex.sub_sub_right_as_sub_add p a b)
    _ = p - a + b + c - d - e - f := rfl

/-- Subtracting a three-term expression of the form `a - b + c`. -/
theorem Complex.sub_sub_add_three_term_expand
    (p a b c : ℂ) :
    p - (a - b + c) = p - a + b - c := by
  calc
    p - (a - b + c) = p - (a - b) - c :=
      Complex.sub_add_right_as_sub_sub p (a - b) c
    _ = p - a + b - c := by
      exact congrArg (fun z : ℂ => z - c)
        (Complex.sub_sub_right_as_sub_add p a b)

/-- Expanding subtraction of an endpoint product. -/
theorem Complex.sub_endpoint_product_expand
    (p w M logwM : ℂ) :
    p - (w + M) * logwM =
      p - w * logwM - M * logwM := by
  calc
    p - (w + M) * logwM =
        p - (w * logwM + M * logwM) := by
      exact congrArg (fun z : ℂ => p - z)
        (Complex.endpoint_product_expand w M logwM)
    _ = p - w * logwM - M * logwM :=
      Complex.sub_add_right_as_sub_sub p (w * logwM) (M * logwM)

/-- Expanding the shifted logarithm product in the left endpoint normal form. -/
theorem Complex.sub_shifted_log_product_expand
    (p w logw : ℂ) :
    p - (w - (1 / 2 : ℂ)) * logw =
      p - w * logw + (1 / 2 : ℂ) * logw := by
  calc
    p - (w - (1 / 2 : ℂ)) * logw =
        p - (w * logw - (1 / 2 : ℂ) * logw) := by
      exact congrArg (fun z : ℂ => p - z)
        (sub_mul w (1 / 2 : ℂ) logw)
    _ = p - w * logw + (1 / 2 : ℂ) * logw :=
      Complex.sub_sub_right_as_sub_add p (w * logw) ((1 / 2 : ℂ) * logw)

/-- The two half-logarithm contributions cancel in the endpoint normal form. -/
theorem Complex.sub_half_logsum_add_half_log
    (p logw logwM : ℂ) :
    p - (logw + logwM) / 2 + (1 / 2 : ℂ) * logw =
      p - (1 / 2 : ℂ) * logwM := by
  have hsplit :
      (logw + logwM) / 2 =
        (1 / 2 : ℂ) * logw + (1 / 2 : ℂ) * logwM := by
    calc
      (logw + logwM) / 2 =
          (logw + logwM) * (2 : ℂ)⁻¹ :=
        div_eq_mul_inv (logw + logwM) (2 : ℂ)
      _ = (logw + logwM) * (1 / 2 : ℂ) := by
        exact congrArg (fun z : ℂ => (logw + logwM) * z)
          (inv_eq_one_div (2 : ℂ))
      _ = (1 / 2 : ℂ) * (logw + logwM) := by
        exact mul_comm (logw + logwM) (1 / 2 : ℂ)
      _ = (1 / 2 : ℂ) * logw + (1 / 2 : ℂ) * logwM :=
        mul_add (1 / 2 : ℂ) logw logwM
  calc
    p - (logw + logwM) / 2 + (1 / 2 : ℂ) * logw =
        p - ((1 / 2 : ℂ) * logw + (1 / 2 : ℂ) * logwM) +
          (1 / 2 : ℂ) * logw := by
      exact congrArg
        (fun z : ℂ => p - z + (1 / 2 : ℂ) * logw)
        hsplit
    _ = p - (1 / 2 : ℂ) * logw - (1 / 2 : ℂ) * logwM +
          (1 / 2 : ℂ) * logw :=
      congrArg
        (fun z : ℂ => z + (1 / 2 : ℂ) * logw)
        (Complex.sub_add_right_as_sub_sub
          p
          ((1 / 2 : ℂ) * logw)
          ((1 / 2 : ℂ) * logwM))
    _ = (p - (1 / 2 : ℂ) * logw + (1 / 2 : ℂ) * logw) -
          (1 / 2 : ℂ) * logwM := by
      calc
        p - (1 / 2 : ℂ) * logw - (1 / 2 : ℂ) * logwM +
            (1 / 2 : ℂ) * logw =
          (p - (1 / 2 : ℂ) * logw - (1 / 2 : ℂ) * logwM) +
            (1 / 2 : ℂ) * logw := rfl
        _ =
          (p - (1 / 2 : ℂ) * logw + (1 / 2 : ℂ) * logw) -
            (1 / 2 : ℂ) * logwM := by
          exact
            Eq.symm
              (calc
                (p - (1 / 2 : ℂ) * logw + (1 / 2 : ℂ) * logw) -
                    (1 / 2 : ℂ) * logwM =
                    (p - (1 / 2 : ℂ) * logw + (1 / 2 : ℂ) * logw) +
                      -((1 / 2 : ℂ) * logwM) :=
                  sub_eq_add_neg
                    (p - (1 / 2 : ℂ) * logw + (1 / 2 : ℂ) * logw)
                    ((1 / 2 : ℂ) * logwM)
                _ =
                    ((p - (1 / 2 : ℂ) * logw) +
                      (1 / 2 : ℂ) * logw) +
                      -((1 / 2 : ℂ) * logwM) := rfl
                _ =
                    (p - (1 / 2 : ℂ) * logw) +
                      ((1 / 2 : ℂ) * logw +
                        -((1 / 2 : ℂ) * logwM)) :=
                  add_assoc
                    (p - (1 / 2 : ℂ) * logw)
                    ((1 / 2 : ℂ) * logw)
                    (-((1 / 2 : ℂ) * logwM))
                _ =
                    (p - (1 / 2 : ℂ) * logw) +
                      (-((1 / 2 : ℂ) * logwM) +
                        (1 / 2 : ℂ) * logw) := by
                  exact congrArg
                    (fun z : ℂ => (p - (1 / 2 : ℂ) * logw) + z)
                    (add_comm ((1 / 2 : ℂ) * logw)
                      (-((1 / 2 : ℂ) * logwM)))
                _ =
                    ((p - (1 / 2 : ℂ) * logw) +
                      -((1 / 2 : ℂ) * logwM)) +
                      (1 / 2 : ℂ) * logw :=
                  (add_assoc
                    (p - (1 / 2 : ℂ) * logw)
                    (-((1 / 2 : ℂ) * logwM))
                    ((1 / 2 : ℂ) * logw)).symm
                _ =
                    p - (1 / 2 : ℂ) * logw -
                      (1 / 2 : ℂ) * logwM +
                        (1 / 2 : ℂ) * logw := rfl)
    _ = p - (1 / 2 : ℂ) * logwM := by
      exact congrArg
        (fun z : ℂ => z - (1 / 2 : ℂ) * logwM)
        (sub_add_cancel p ((1 / 2 : ℂ) * logw))

/-- Expanding the shifted endpoint product against a logarithm difference. -/
theorem Complex.shifted_endpoint_product_logdiff_expand
    (w M logM logwM : ℂ) :
    (w + M + (1 / 2 : ℂ)) * (logM - logwM) =
      w * logM - w * logwM +
        (M * logM - M * logwM) +
          ((1 / 2 : ℂ) * logM - (1 / 2 : ℂ) * logwM) := by
  calc
    (w + M + (1 / 2 : ℂ)) * (logM - logwM) =
        ((w + M) + (1 / 2 : ℂ)) * (logM - logwM) := rfl
    _ =
        (w + M) * (logM - logwM) +
          (1 / 2 : ℂ) * (logM - logwM) :=
      add_mul (w + M) (1 / 2 : ℂ) (logM - logwM)
    _ =
        (w * (logM - logwM) + M * (logM - logwM)) +
          (1 / 2 : ℂ) * (logM - logwM) := by
      exact congrArg
        (fun z : ℂ => z + (1 / 2 : ℂ) * (logM - logwM))
        (add_mul w M (logM - logwM))
    _ =
        ((w * logM - w * logwM) +
          (M * logM - M * logwM)) +
          ((1 / 2 : ℂ) * logM - (1 / 2 : ℂ) * logwM) := by
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ HAdd.hAdd
          (mul_sub w logM logwM)
          (mul_sub M logM logwM))
        (mul_sub (1 / 2 : ℂ) logM logwM)
    _ =
      w * logM - w * logwM +
        (M * logM - M * logwM) +
          ((1 / 2 : ℂ) * logM - (1 / 2 : ℂ) * logwM) := rfl

/-- Final additive reassociation for the left endpoint normal form. -/
theorem Complex.left_endpoint_shift_cancel
    (A w M H L : ℂ) :
    A + (w + M) - w - H + w - L =
      A + M + w - H - L := by
  calc
    A + (w + M) - w - H + w - L =
        (((A + (w + M)) + -w) + -H + w) + -L := by
      rfl
    _ =
        ((((A + (w + M)) + -w) + -H) + w) + -L := rfl
    _ =
        (((A + (w + M)) + -w) + (-H + w)) + -L := by
      exact congrArg (fun z : ℂ => z + -L)
        (add_assoc ((A + (w + M)) + -w) (-H) w)
    _ =
        (((A + (w + M)) + -w) + (w + -H)) + -L := by
      exact congrArg (fun z : ℂ => (((A + (w + M)) + -w) + z) + -L)
        (add_comm (-H) w)
    _ =
        ((((A + (w + M)) + -w) + w) + -H) + -L := by
      exact congrArg (fun z : ℂ => z + -L)
        (add_assoc ((A + (w + M)) + -w) w (-H)).symm
    _ =
        (((A + (w + M)) + (-w + w)) + -H) + -L := by
      exact congrArg (fun z : ℂ => (z + -H) + -L)
        (add_assoc (A + (w + M)) (-w) w)
    _ =
        (((A + (w + M)) + 0) + -H) + -L := by
      exact congrArg (fun z : ℂ => ((A + (w + M)) + z + -H) + -L)
        (neg_add_cancel w)
    _ =
        ((A + (w + M)) + -H) + -L := by
      exact congrArg (fun z : ℂ => (z + -H) + -L)
        (add_zero (A + (w + M)))
    _ =
        (A + (M + w) + -H) + -L := by
      exact congrArg (fun z : ℂ => (A + z + -H) + -L)
        (add_comm w M)
    _ =
        ((A + M + w) + -H) + -L := by
      exact congrArg (fun z : ℂ => (z + -H) + -L)
        (add_assoc A M w).symm
    _ = A + M + w - H - L := by
      exact congrArg (fun z : ℂ => z - L)
        (sub_eq_add_neg (A + M + w) H).symm

/-- Moving two already-subtracted endpoint products past the surviving affine
endpoint terms. -/
theorem Complex.endpoint_subtractions_after_affine
    (P a b M w H L : ℂ) :
    (P - a - b) + M + w - H - L =
      P + M + w - a - b - H - L := by
  calc
    (P - a - b) + M + w - H - L =
        (((((P + -a) + -b) + M) + w) + -H) + -L := by
      rfl
    _ = ((((P + -a) + (-b + M)) + w) + -H) + -L := by
      exact congrArg (fun z : ℂ => ((z + w) + -H) + -L)
        (add_assoc (P + -a) (-b) M)
    _ = ((((P + -a) + (M + -b)) + w) + -H) + -L := by
      exact congrArg (fun z : ℂ => ((((P + -a) + z) + w) + -H) + -L)
        (add_comm (-b) M)
    _ = (((((P + -a) + M) + -b) + w) + -H) + -L := by
      exact congrArg (fun z : ℂ => ((z + w) + -H) + -L)
        (add_assoc (P + -a) M (-b)).symm
    _ = ((((P + (-a + M)) + -b) + w) + -H) + -L := by
      exact congrArg (fun z : ℂ => ((z + -b) + w + -H) + -L)
        (add_assoc P (-a) M)
    _ = ((((P + (M + -a)) + -b) + w) + -H) + -L := by
      exact congrArg (fun z : ℂ => (((P + z) + -b) + w + -H) + -L)
        (add_comm (-a) M)
    _ = (((((P + M) + -a) + -b) + w) + -H) + -L := by
      exact congrArg (fun z : ℂ => ((z + -b) + w + -H) + -L)
        (add_assoc P M (-a)).symm
    _ = ((((P + M) + -a) + (-b + w)) + -H) + -L := by
      exact congrArg (fun z : ℂ => (z + -H) + -L)
        (add_assoc (((P + M) + -a)) (-b) w)
    _ = ((((P + M) + -a) + (w + -b)) + -H) + -L := by
      exact congrArg (fun z : ℂ => ((((P + M) + -a) + z) + -H) + -L)
        (add_comm (-b) w)
    _ = (((((P + M) + -a) + w) + -b) + -H) + -L := by
      exact congrArg (fun z : ℂ => (z + -H) + -L)
        (add_assoc (((P + M) + -a)) w (-b)).symm
    _ = ((((P + M) + (-a + w)) + -b) + -H) + -L := by
      exact congrArg (fun z : ℂ => ((z + -b) + -H) + -L)
        (add_assoc (P + M) (-a) w)
    _ = ((((P + M) + (w + -a)) + -b) + -H) + -L := by
      exact congrArg (fun z : ℂ => (((P + M) + z) + -b + -H) + -L)
        (add_comm (-a) w)
    _ = (((((P + M) + w) + -a) + -b) + -H) + -L := by
      exact congrArg (fun z : ℂ => ((z + -b) + -H) + -L)
        (add_assoc (P + M) w (-a)).symm
    _ = P + M + w - a - b - H - L := by
      rfl

/-- Endpoint normal-form reassociation after the half-log cancellation. -/
theorem Complex.endpoint_normal_form_reassociate_core
    (P a b w M H L : ℂ) :
    P - a - b + (w + M) - w - H + w - L =
      P + M + w - a - b - H - L := by
  calc
    P - a - b + (w + M) - w - H + w - L =
        (P - a - b) + (w + M) - w - H + w - L := by
      rfl
    _ = (P - a - b) + M + w - H - L :=
      Complex.left_endpoint_shift_cancel (P - a - b) w M H L
    _ = P + M + w - a - b - H - L :=
      Complex.endpoint_subtractions_after_affine P a b M w H L

/-- The first two endpoint summands commute into the public normal form. -/
theorem Complex.endpoint_initial_sum_commute
    (logfac wlogM M w a b H L : ℂ) :
    (wlogM + logfac) + M + w - a - b - H - L =
      logfac + wlogM + M + w - a - b - H - L := by
  calc
    (wlogM + logfac) + M + w - a - b - H - L =
        (logfac + wlogM) + M + w - a - b - H - L := by
      exact congrArg (fun z : ℂ => z + M + w - a - b - H - L)
        (add_comm wlogM logfac)
    _ = logfac + wlogM + M + w - a - b - H - L := rfl

/-- Move the two endpoint-cancellation summands next to the endpoint
subtractions before the affine endpoint reassociation. -/
theorem Complex.endpoint_move_cancellands_left
    (Q X Y Z w : ℂ) :
    Q + ((X + Y + Z) + w) = (Q + Y + Z) + (X + w) := by
  have hswap (A B C : ℂ) :
      (A + B) + C = (A + C) + B := by
    calc
      (A + B) + C = A + (B + C) :=
        add_assoc A B C
      _ = A + (C + B) := by
        exact congrArg (fun r : ℂ => A + r) (add_comm B C)
      _ = (A + C) + B :=
        (add_assoc A C B).symm
  calc
    Q + ((X + Y + Z) + w) =
        (Q + (X + Y + Z)) + w := by
      exact (add_assoc Q (X + Y + Z) w).symm
    _ = ((Q + (X + Y)) + Z) + w := by
      exact congrArg (fun r : ℂ => r + w)
        (add_assoc Q (X + Y) Z).symm
    _ = (((Q + X) + Y) + Z) + w := by
      exact congrArg (fun r : ℂ => (r + Z) + w)
        (add_assoc Q X Y).symm
    _ = (((Q + Y) + X) + Z) + w := by
      exact congrArg (fun r : ℂ => (r + Z) + w)
        (hswap Q X Y)
    _ = (((Q + Y) + Z) + X) + w := by
      exact congrArg (fun r : ℂ => r + w)
        (hswap (Q + Y) X Z)
    _ = ((Q + Y) + Z) + (X + w) := by
      exact add_assoc ((Q + Y) + Z) X w
    _ = (Q + Y + Z) + (X + w) := by
      rfl

/-- Interleave endpoint cancellands beside the subtractions they cancel. -/
theorem Complex.endpoint_interleave_cancellands
    (P C H M L Y Z : ℂ) :
    (P - C - H + M - L + Y + Z) =
      P - C + Y - H + Z + M - L := by
  calc
    P - C - H + M - L + Y + Z =
        (((((P + -C) + -H) + M) + -L) + Y) + Z := by
      rfl
    _ = (((((P + -C) + -H) + M) + Y) + -L) + Z := by
      exact congrArg (fun r : ℂ => r + Z)
        (add_right_comm (((P + -C) + -H) + M) (-L) Y)
    _ = (((((P + -C) + -H) + Y) + M) + -L) + Z := by
      exact congrArg (fun r : ℂ => (r + -L) + Z)
        (add_right_comm ((P + -C) + -H) M Y)
    _ = (((((P + -C) + Y) + -H) + M) + -L) + Z := by
      exact congrArg (fun r : ℂ => ((r + M) + -L) + Z)
        (add_right_comm (P + -C) (-H) Y)
    _ = ((((P + -C) + Y) + -H) + M) + (-L + Z) := by
      exact add_assoc ((((P + -C) + Y) + -H) + M) (-L) Z
    _ = ((((P + -C) + Y) + -H) + M) + (Z + -L) := by
      exact congrArg
        (fun r : ℂ => ((((P + -C) + Y) + -H) + M) + r)
        (add_comm (-L) Z)
    _ = (((((P + -C) + Y) + -H) + M) + Z) + -L := by
      exact (add_assoc ((((P + -C) + Y) + -H) + M) Z (-L)).symm
    _ = (((((P + -C) + Y) + -H) + Z) + M) + -L := by
      exact congrArg (fun r : ℂ => r + -L)
        (add_right_comm (((P + -C) + Y) + -H) M Z)
    _ = P - C + Y - H + Z + M - L := by
      rfl

/-- Expanding the right endpoint Stirling term exposes the same normal-form
spine as the left endpoint calculation. -/
theorem Complex.right_endpoint_expanded_to_left_shape
    (w M logM logwM logfac log2pi : ℂ) :
    (logfac - ((M + (1 / 2 : ℂ)) * logM - M + log2pi / 2)) +
        ((w * logM - w * logwM +
          (M * logM - M * logwM) +
            ((1 / 2 : ℂ) * logM - (1 / 2 : ℂ) * logwM)) + w) =
      w * logM + logfac - w * logwM - M * logwM + (w + M) - w -
        (1 / 2 : ℂ) * logwM + w - log2pi / 2 := by
  let H : ℂ := (1 / 2 : ℂ) * logM
  let K : ℂ := (1 / 2 : ℂ) * logwM
  let A : ℂ := w * logM
  let B : ℂ := w * logwM
  let C : ℂ := M * logM
  let D : ℂ := M * logwM
  let L : ℂ := log2pi / 2
  have hmul :
      (M + (1 / 2 : ℂ)) * logM = C + H := by
    calc
      (M + (1 / 2 : ℂ)) * logM =
          M * logM + (1 / 2 : ℂ) * logM :=
        add_mul M (1 / 2 : ℂ) logM
      _ = C + H := rfl
  have hstirling :
      logfac - ((M + (1 / 2 : ℂ)) * logM - M + log2pi / 2) =
        logfac - C - H + M - L := by
    calc
      logfac - ((M + (1 / 2 : ℂ)) * logM - M + log2pi / 2) =
          logfac - ((C + H) - M + L) := by
        exact congrArg
          (fun z : ℂ => logfac - (z - M + L))
          hmul
      _ = logfac - (C + H) + M - L :=
        Complex.sub_sub_add_three_term_expand logfac (C + H) M L
      _ = logfac - C - H + M - L := by
        calc
          logfac - (C + H) + M - L =
              (logfac - C - H) + M - L := by
            exact congrArg (fun z : ℂ => z + M - L)
              (Complex.sub_add_right_as_sub_sub logfac C H)
          _ = logfac - C - H + M - L := rfl
  have hsum :
      w * logM - w * logwM +
          (M * logM - M * logwM) +
            ((1 / 2 : ℂ) * logM - (1 / 2 : ℂ) * logwM) =
        A - B + (C - D) + (H - K) := by
    rfl
  calc
    (logfac - ((M + (1 / 2 : ℂ)) * logM - M + log2pi / 2)) +
        ((w * logM - w * logwM +
          (M * logM - M * logwM) +
            ((1 / 2 : ℂ) * logM - (1 / 2 : ℂ) * logwM)) + w) =
        (logfac - C - H + M - L) + ((A - B + (C - D) + (H - K)) + w) := by
      exact congrArg₂ HAdd.hAdd hstirling
        (congrArg (fun z : ℂ => z + w) hsum)
    _ = (A + logfac - B - D + (w + M) - w - K + w - L) := by
      calc
        (logfac - C - H + M - L) + ((A - B + (C - D) + (H - K)) + w) =
            (logfac - C + (C - D) - H + (H - K) + M - L) + (A - B + w) := by
          calc
            (logfac - C - H + M - L) + ((A - B + (C - D) + (H - K)) + w) =
                (logfac - C - H + M - L + (C - D) + (H - K)) +
                  (A - B + w) := by
              exact
                Complex.endpoint_move_cancellands_left
                  (logfac - C - H + M - L)
                  (A - B)
                  (C - D)
                  (H - K)
                  w
            _ =
                (logfac - C + (C - D) - H + (H - K) + M - L) +
                  (A - B + w) := by
              exact congrArg
                (fun r : ℂ => r + (A - B + w))
                (Complex.endpoint_interleave_cancellands
                  logfac C H M L (C - D) (H - K))
        _ = (logfac - D - K + M - L + A + w - B) := by
          have hCcancel :
              logfac - C + (C - D) = logfac - D :=
            sub_add_sub_cancel logfac C D
          have hHcancel :
              logfac - D - H + (H - K) = logfac - D - K :=
            sub_add_sub_cancel (logfac - D) H K
          calc
            (logfac - C + (C - D) - H + (H - K) + M - L) + (A - B + w) =
                logfac - C + (C - D) - H + (H - K) + M - L + A + w - B := by
              calc
                (logfac - C + (C - D) - H + (H - K) + M - L) + (A - B + w) =
                    (logfac - C + (C - D) - H + (H - K) + M - L) + ((A - B) + w) := by
                  rfl
                _ = (logfac - C + (C - D) - H + (H - K) + M - L) + ((A + -B) + w) := by
                  rfl
                _ = (logfac - C + (C - D) - H + (H - K) + M - L) + (A + (-B + w)) := by
                  exact congrArg
                    (fun z : ℂ =>
                      (logfac - C + (C - D) - H + (H - K) + M - L) + z)
                    (add_assoc A (-B) w)
                _ = (logfac - C + (C - D) - H + (H - K) + M - L) + (A + (w + -B)) := by
                  exact congrArg
                    (fun z : ℂ =>
                      (logfac - C + (C - D) - H + (H - K) + M - L) +
                        (A + z))
                    (add_comm (-B) w)
                _ = (logfac - C + (C - D) - H + (H - K) + M - L + A) + (w + -B) := by
                  exact
                    (add_assoc
                      (logfac - C + (C - D) - H + (H - K) + M - L)
                      A
                      (w + -B)).symm
                _ =
                    ((logfac - C + (C - D) - H + (H - K) + M - L + A) + w) +
                      -B := by
                  exact
                    (add_assoc
                      (logfac - C + (C - D) - H + (H - K) + M - L + A)
                      w
                      (-B)).symm
                _ = (logfac - C + (C - D) - H + (H - K) + M - L + A) + w - B := by
                  exact
                    (sub_eq_add_neg
                      ((logfac - C + (C - D) - H + (H - K) + M - L + A) + w)
                      B).symm
                _ = logfac - C + (C - D) - H + (H - K) + M - L + A + w - B := by
                  rfl
            _ =
                (logfac - C + (C - D)) - H + (H - K) + M - L + A + w - B := rfl
            _ = (logfac - D) - H + (H - K) + M - L + A + w - B := by
              exact congrArg
                (fun z : ℂ => z - H + (H - K) + M - L + A + w - B)
                hCcancel
            _ = logfac - D - K + M - L + A + w - B := by
              exact congrArg
                (fun z : ℂ => z + M - L + A + w - B)
                hHcancel
        _ = A + logfac - B - D + (w + M) - w - K + w - L := by
          have hcancel_order :
              logfac - D - K + M - L =
                logfac + M - D - K - L := by
            have hraw :
                (logfac - D - K) + M + 0 - 0 - L =
                  logfac + M + 0 - D - K - 0 - L :=
              Complex.endpoint_subtractions_after_affine
                logfac D K M 0 0 L
            calc
              logfac - D - K + M - L =
                  (logfac - D - K) + M + 0 - 0 - L := by
                calc
                  logfac - D - K + M - L =
                      ((logfac - D - K) + M) - L := rfl
                  _ = (((logfac - D - K) + M) + 0) - 0 - L := by
                    exact
                      Eq.symm
                        (calc
                          (((logfac - D - K) + M) + 0) - 0 - L =
                              ((logfac - D - K) + M) + 0 - L := by
                            exact congrArg (fun z : ℂ => z - L)
                              (sub_zero (((logfac - D - K) + M) + 0))
                          _ = ((logfac - D - K) + M) - L := by
                            exact congrArg (fun z : ℂ => z - L)
                              (add_zero ((logfac - D - K) + M)))
              _ = logfac + M + 0 - D - K - 0 - L := hraw
              _ = logfac + M - D - K - L := by
                calc
                  logfac + M + 0 - D - K - 0 - L =
                      (logfac + M) - D - K - 0 - L := by
                    exact congrArg (fun z : ℂ => z - D - K - 0 - L)
                      (add_zero (logfac + M))
                  _ = (logfac + M) - D - K - L := by
                    exact congrArg (fun z : ℂ => z - L)
                      (sub_zero ((logfac + M) - D - K))
                  _ = logfac + M - D - K - L := rfl
          calc
            logfac - D - K + M - L + A + w - B =
                (logfac + M - D - K - L) + A + w - B := by
              exact congrArg (fun z : ℂ => z + A + w - B) hcancel_order
            _ =
                A + logfac + M + w - B - D - K - L := by
              have hswap (X Y Z : ℂ) :
                  (X + Y) + Z = (X + Z) + Y := by
                calc
                  (X + Y) + Z = X + (Y + Z) :=
                    add_assoc X Y Z
                  _ = X + (Z + Y) := by
                    exact congrArg (fun r : ℂ => X + r) (add_comm Y Z)
                  _ = (X + Z) + Y :=
                    (add_assoc X Z Y).symm
              let R : ℂ := A + logfac + M
              calc
                (logfac + M - D - K - L) + A + w - B =
                    (((((logfac + M) + -D) + -K) + -L) + A) + w + -B := rfl
                _ =
                    (A + ((((logfac + M) + -D) + -K) + -L)) + w + -B := by
                  exact congrArg (fun z : ℂ => z + w + -B)
                    (add_comm
                      ((((logfac + M) + -D) + -K) + -L)
                      A)
                _ =
                    (((((A + logfac) + M) + -D) + -K) + -L) + w + -B := by
                  exact congrArg (fun z : ℂ => z + w + -B) <| by
                    calc
                      A + ((((logfac + M) + -D) + -K) + -L) =
                          (A + (((logfac + M) + -D) + -K)) + -L :=
                        (add_assoc A (((logfac + M) + -D) + -K) (-L)).symm
                      _ = ((A + ((logfac + M) + -D)) + -K) + -L := by
                        exact congrArg (fun z : ℂ => z + -L)
                          (add_assoc A ((logfac + M) + -D) (-K)).symm
                      _ = (((A + (logfac + M)) + -D) + -K) + -L := by
                        exact congrArg (fun z : ℂ => (z + -K) + -L)
                          (add_assoc A (logfac + M) (-D)).symm
                      _ = ((((A + logfac) + M) + -D) + -K) + -L := by
                        exact congrArg (fun z : ℂ => (z + -D) + -K + -L)
                          (add_assoc A logfac M).symm
                _ = (((((R + -D) + -K) + -L) + w) + -B) := rfl
                _ = ((((R + -D) + -K) + w) + -L) + -B := by
                  exact congrArg (fun z : ℂ => z + -B)
                    (hswap (((R + -D) + -K)) (-L) w)
                _ = (((R + -D) + w) + -K) + -L + -B := by
                  exact congrArg (fun z : ℂ => (z + -L) + -B)
                    (hswap (R + -D) (-K) w)
                _ = ((R + w) + -D) + -K + -L + -B := by
                  exact congrArg (fun z : ℂ => (z + -K) + -L + -B)
                    (hswap R (-D) w)
                _ = (((R + w) + -D) + -K + -B) + -L := by
                  exact hswap (((R + w) + -D) + -K) (-L) (-B)
                _ = ((((R + w) + -D) + -B) + -K) + -L := by
                  exact congrArg (fun z : ℂ => z + -L)
                    (hswap ((R + w) + -D) (-K) (-B))
                _ = (((R + w) + -B) + -D) + -K + -L := by
                  exact congrArg (fun z : ℂ => (z + -K) + -L)
                    (hswap (R + w) (-D) (-B))
                _ = A + logfac + M + w - B - D - K - L := rfl
            _ = A + logfac - B - D + (w + M) - w - K + w - L := by
              exact
                Eq.symm
                  (Complex.endpoint_normal_form_reassociate_core
                    (A + logfac) B D w M K L)
    _ =
      w * logM + logfac - w * logwM - M * logwM + (w + M) - w -
        (1 / 2 : ℂ) * logwM + w - log2pi / 2 := rfl

/-- Final additive reassociation for the left endpoint normal form. -/
theorem Complex.left_endpoint_normal_form_reassociate
    (w M logM logwM logfac log2pi : ℂ) :
    w * logM + logfac - w * logwM - M * logwM + (w + M) - w -
        (1 / 2 : ℂ) * logwM + w - log2pi / 2 =
      logfac + w * logM + M + w - w * logwM -
        M * logwM - (1 / 2 : ℂ) * logwM - log2pi / 2 := by
  have hcore :
      (w * logM + logfac) - w * logwM - M * logwM +
          (w + M) - w - (1 / 2 : ℂ) * logwM + w - log2pi / 2 =
        (w * logM + logfac) + M + w - w * logwM -
          M * logwM - (1 / 2 : ℂ) * logwM - log2pi / 2 :=
    Complex.endpoint_normal_form_reassociate_core
      (w * logM + logfac)
      (w * logwM)
      (M * logwM)
      w
      M
      ((1 / 2 : ℂ) * logwM)
      (log2pi / 2)
  have hcomm :
      (w * logM + logfac) + M + w - w * logwM -
          M * logwM - (1 / 2 : ℂ) * logwM - log2pi / 2 =
        logfac + w * logM + M + w - w * logwM -
          M * logwM - (1 / 2 : ℂ) * logwM - log2pi / 2 :=
    Complex.endpoint_initial_sum_commute
      logfac
      (w * logM)
      M
      w
      (w * logwM)
      (M * logwM)
      ((1 / 2 : ℂ) * logwM)
      (log2pi / 2)
  exact Eq.trans hcore hcomm

/-- Final additive reassociation for the right endpoint normal form. -/
theorem Complex.right_endpoint_normal_form_reassociate
    (w M logM logwM logfac log2pi : ℂ)
    (hshift :
      (w + M + (1 / 2 : ℂ)) * (logM - logwM) =
        w * logM - w * logwM +
          (M * logM - M * logwM) +
            ((1 / 2 : ℂ) * logM - (1 / 2 : ℂ) * logwM)) :
      (logfac - ((M + (1 / 2 : ℂ)) * logM - M + log2pi / 2)) +
          (((w + M + (1 / 2 : ℂ)) * (logM - logwM)) + w) =
        logfac + w * logM + M + w - w * logwM -
          M * logwM - (1 / 2 : ℂ) * logwM - log2pi / 2 := by
  have hexpanded :
      (logfac - ((M + (1 / 2 : ℂ)) * logM - M + log2pi / 2)) +
          ((w * logM - w * logwM +
            (M * logM - M * logwM) +
              ((1 / 2 : ℂ) * logM - (1 / 2 : ℂ) * logwM)) + w) =
        logfac + w * logM + M + w - w * logwM -
          M * logwM - (1 / 2 : ℂ) * logwM - log2pi / 2 := by
    calc
      (logfac - ((M + (1 / 2 : ℂ)) * logM - M + log2pi / 2)) +
          ((w * logM - w * logwM +
            (M * logM - M * logwM) +
              ((1 / 2 : ℂ) * logM - (1 / 2 : ℂ) * logwM)) + w) =
          w * logM + logfac - w * logwM - M * logwM + (w + M) - w -
            (1 / 2 : ℂ) * logwM + w - log2pi / 2 :=
        Complex.right_endpoint_expanded_to_left_shape
          w M logM logwM logfac log2pi
      _ =
        logfac + w * logM + M + w - w * logwM -
          M * logwM - (1 / 2 : ℂ) * logwM - log2pi / 2 :=
        Complex.left_endpoint_normal_form_reassociate
          w M logM logwM logfac log2pi
  exact hshift.symm ▸ hexpanded

/-- Left normal form for the unfolded endpoint Stirling remainder. -/
theorem Complex.binet_endpoint_left_unfolded_normal_form
    (w M logM logw logwM logfac log2pi : ℂ) :
    w * logM + logfac - (w + M) * logwM + (w + M) +
        w * logw - w - (logw + logwM) / 2 -
        (w - (1 / 2 : ℂ)) * logw + w - log2pi / 2 =
      logfac + w * logM + M + w - w * logwM -
        M * logwM - (1 / 2 : ℂ) * logwM - log2pi / 2 := by
  have hprod :
      w * logM + logfac - (w + M) * logwM =
        w * logM + logfac - w * logwM - M * logwM :=
    Complex.sub_endpoint_product_expand (w * logM + logfac) w M logwM
  have hshift :
      w * logM + logfac - w * logwM - M * logwM + (w + M) +
          w * logw - w - (logw + logwM) / 2 -
          (w - (1 / 2 : ℂ)) * logw =
        w * logM + logfac - w * logwM - M * logwM + (w + M) +
          w * logw - w - (logw + logwM) / 2 -
          w * logw + (1 / 2 : ℂ) * logw :=
    Complex.sub_shifted_log_product_expand
      (w * logM + logfac - w * logwM - M * logwM + (w + M) +
        w * logw - w - (logw + logwM) / 2)
      w
      logw
  have hhalf :
      w * logM + logfac - w * logwM - M * logwM + (w + M) +
          w * logw - w - (logw + logwM) / 2 -
          w * logw + (1 / 2 : ℂ) * logw =
        w * logM + logfac - w * logwM - M * logwM + (w + M) - w -
          (1 / 2 : ℂ) * logwM := by
    let P : ℂ := w * logM + logfac - w * logwM - M * logwM + (w + M)
    have hadd_swap (X Y Z : ℂ) :
        (X + Y) + Z = (X + Z) + Y := by
      calc
        (X + Y) + Z = X + (Y + Z) :=
          add_assoc X Y Z
        _ = X + (Z + Y) := by
          exact congrArg (fun r : ℂ => X + r) (add_comm Y Z)
        _ = (X + Z) + Y :=
          (add_assoc X Z Y).symm
    have hstart :
        P + w * logw - w - (logw + logwM) / 2 -
            w * logw + (1 / 2 : ℂ) * logw =
          (P + w * logw - w - w * logw) -
            (logw + logwM) / 2 + (1 / 2 : ℂ) * logw := by
      calc
        P + w * logw - w - (logw + logwM) / 2 -
            w * logw + (1 / 2 : ℂ) * logw =
            ((P + w * logw - w) - (logw + logwM) / 2) -
              w * logw + (1 / 2 : ℂ) * logw := rfl
        _ =
            ((P + w * logw - w) + -((logw + logwM) / 2)) -
              w * logw + (1 / 2 : ℂ) * logw := by
          exact congrArg
            (fun z : ℂ => z - w * logw + (1 / 2 : ℂ) * logw)
            (sub_eq_add_neg
              (P + w * logw - w)
              ((logw + logwM) / 2))
        _ =
            ((P + w * logw - w) + -((logw + logwM) / 2)) +
              -(w * logw) + (1 / 2 : ℂ) * logw := by
          exact congrArg
            (fun z : ℂ => z + (1 / 2 : ℂ) * logw)
            (sub_eq_add_neg
              ((P + w * logw - w) + -((logw + logwM) / 2))
              (w * logw))
        _ =
            (((P + w * logw - w) + -((logw + logwM) / 2)) +
              -(w * logw)) + (1 / 2 : ℂ) * logw := by
          rfl
        _ =
            ((P + w * logw - w) + -(w * logw)) +
              -((logw + logwM) / 2) + (1 / 2 : ℂ) * logw := by
          exact congrArg
            (fun z : ℂ => z + (1 / 2 : ℂ) * logw)
            (hadd_swap
              (P + w * logw - w)
              (-((logw + logwM) / 2))
              (-(w * logw)))
        _ =
            (P + w * logw - w - w * logw) +
              -((logw + logwM) / 2) + (1 / 2 : ℂ) * logw := by
          exact congrArg
            (fun z : ℂ => z + -((logw + logwM) / 2) + (1 / 2 : ℂ) * logw)
            (sub_eq_add_neg (P + w * logw - w) (w * logw)).symm
        _ =
            (P + w * logw - w - w * logw) -
              (logw + logwM) / 2 + (1 / 2 : ℂ) * logw := by
          exact congrArg
            (fun z : ℂ => z + (1 / 2 : ℂ) * logw)
            (sub_eq_add_neg
              (P + w * logw - w - w * logw)
              ((logw + logwM) / 2)).symm
    have hcancel :
        P + w * logw - w - w * logw = P - w := by
      calc
        P + w * logw - w - w * logw =
            ((P + w * logw) + -w) + -(w * logw) := rfl
        _ = (P + w * logw) + (-(w) + -(w * logw)) := by
          exact add_assoc (P + w * logw) (-w) (-(w * logw))
        _ = (P + w * logw) + (-(w * logw) + -w) := by
          exact congrArg (fun z : ℂ => (P + w * logw) + z)
            (add_comm (-w) (-(w * logw)))
        _ = ((P + w * logw) + -(w * logw)) + -w := by
          exact (add_assoc (P + w * logw) (-(w * logw)) (-w)).symm
        _ = (P + (w * logw + -(w * logw))) + -w := by
          exact congrArg (fun z : ℂ => z + -w)
            (add_assoc P (w * logw) (-(w * logw)))
        _ = (P + 0) + -w := by
          exact congrArg (fun z : ℂ => (P + z) + -w)
            (add_neg_cancel (w * logw))
        _ = P + -w := by
          exact congrArg (fun z : ℂ => z + -w) (add_zero P)
        _ = P - w := rfl
    calc
      w * logM + logfac - w * logwM - M * logwM + (w + M) +
          w * logw - w - (logw + logwM) / 2 -
          w * logw + (1 / 2 : ℂ) * logw =
          P + w * logw - w - (logw + logwM) / 2 -
            w * logw + (1 / 2 : ℂ) * logw := rfl
      _ =
          (P + w * logw - w - w * logw) -
            (logw + logwM) / 2 + (1 / 2 : ℂ) * logw :=
        hstart
      _ = (P + w * logw - w - w * logw) -
            (1 / 2 : ℂ) * logwM := by
        exact
          Complex.sub_half_logsum_add_half_log
            (P + w * logw - w - w * logw)
            logw
            logwM
      _ = (P - w) - (1 / 2 : ℂ) * logwM := by
        exact congrArg (fun z : ℂ => z - (1 / 2 : ℂ) * logwM) hcancel
      _ =
          w * logM + logfac - w * logwM - M * logwM + (w + M) - w -
            (1 / 2 : ℂ) * logwM := rfl
  calc
    w * logM + logfac - (w + M) * logwM + (w + M) +
        w * logw - w - (logw + logwM) / 2 -
        (w - (1 / 2 : ℂ)) * logw + w - log2pi / 2 =
      w * logM + logfac - w * logwM - M * logwM + (w + M) +
        w * logw - w - (logw + logwM) / 2 -
        (w - (1 / 2 : ℂ)) * logw + w - log2pi / 2 := by
      exact congrArg
        (fun z : ℂ =>
          z + (w + M) + w * logw - w - (logw + logwM) / 2 -
            (w - (1 / 2 : ℂ)) * logw + w - log2pi / 2)
        hprod
    _ =
      w * logM + logfac - w * logwM - M * logwM + (w + M) +
        w * logw - w - (logw + logwM) / 2 -
        w * logw + (1 / 2 : ℂ) * logw + w - log2pi / 2 := by
      exact congrArg
        (fun z : ℂ => z + w - log2pi / 2)
        hshift
    _ =
      w * logM + logfac - w * logwM - M * logwM + (w + M) - w -
        (1 / 2 : ℂ) * logwM + w - log2pi / 2 := by
      exact congrArg
        (fun z : ℂ => z + w - log2pi / 2)
        hhalf
    _ =
      logfac + w * logM + M + w - w * logwM -
        M * logwM - (1 / 2 : ℂ) * logwM - log2pi / 2 := by
      exact
        Complex.left_endpoint_normal_form_reassociate
          w M logM logwM logfac log2pi

/-- Right normal form for the unfolded endpoint Stirling remainder. -/
theorem Complex.binet_endpoint_right_unfolded_normal_form
    (w M logM logwM logfac log2pi : ℂ) :
    (logfac - ((M + (1 / 2 : ℂ)) * logM - M + log2pi / 2)) +
        (((w + M + (1 / 2 : ℂ)) * (logM - logwM)) + w) =
      logfac + w * logM + M + w - w * logwM -
        M * logwM - (1 / 2 : ℂ) * logwM - log2pi / 2 := by
  have hshift :
      (w + M + (1 / 2 : ℂ)) * (logM - logwM) =
        w * logM - w * logwM +
          (M * logM - M * logwM) +
            ((1 / 2 : ℂ) * logM - (1 / 2 : ℂ) * logwM) :=
    Complex.shifted_endpoint_product_logdiff_expand w M logM logwM
  exact
    Complex.right_endpoint_normal_form_reassociate
      w M logM logwM logfac log2pi hshift

/-- Ring bookkeeping for the complex endpoint remainder after the finite main
term, the limiting Binet main term, the factorial Stirling error, and the
endpoint logarithmic shift have all been unfolded. -/
theorem Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_unfolded_regroup
    (w M logM logw logwM logfac log2pi : ℂ) :
    w * logM + logfac -
          (((w + M) * logwM - (w + M)) - (w * logw - w)) -
        (logw + logwM) / 2 -
        ((w - (1 / 2 : ℂ)) * logw - w + log2pi / 2) =
      (logfac - ((M + (1 / 2 : ℂ)) * logM - M + log2pi / 2)) +
        (((w + M + (1 / 2 : ℂ)) * (logM - logwM)) + w) := by
  -- Both sides expand to the same form: logfac + w*logM + M + w - w*logwM - M*logwM - (1/2)*logwM - log2pi/2
  -- Strategy: expand LHS, expand RHS, show equality
  calc w * logM + logfac -
          (((w + M) * logwM - (w + M)) - (w * logw - w)) -
        (logw + logwM) / 2 -
        ((w - (1 / 2 : ℂ)) * logw - w + log2pi / 2)
    = w * logM + logfac - ((w + M) * logwM - (w + M) - w * logw + w) - (logw + logwM) / 2 - ((w - (1 / 2 : ℂ)) * logw - w + log2pi / 2) := by
        exact congrArg
          (fun z : ℂ =>
            w * logM + logfac - z - (logw + logwM) / 2 -
              ((w - (1 / 2 : ℂ)) * logw - w + log2pi / 2))
          (Complex.sub_sub_sub_eq_sub_sub_add
            ((w + M) * logwM)
            (w + M)
            (w * logw)
            w)
    _ = w * logM + logfac - (w + M) * logwM + (w + M) + w * logw - w - (logw + logwM) / 2 - ((w - (1 / 2 : ℂ)) * logw - w + log2pi / 2) := by
        exact
          Complex.endpoint_subtract_four_term_expand
            (w * logM + logfac)
            ((w + M) * logwM)
            (w + M)
            (w * logw)
            w
            ((logw + logwM) / 2)
            ((w - (1 / 2 : ℂ)) * logw - w + log2pi / 2)
    _ = w * logM + logfac - (w + M) * logwM + (w + M) + w * logw - w - (logw + logwM) / 2 - (w - (1 / 2 : ℂ)) * logw + w - log2pi / 2 := by
        exact
          Complex.sub_sub_add_three_term_expand
            (w * logM + logfac - (w + M) * logwM + (w + M) +
              w * logw - w - (logw + logwM) / 2)
            ((w - (1 / 2 : ℂ)) * logw)
            w
            (log2pi / 2)
    _ = logfac + w * logM + M + w - w * logwM - M * logwM - (1 / 2 : ℂ) * logwM - log2pi / 2 := by
        exact
          Complex.binet_endpoint_left_unfolded_normal_form
            w M logM logw logwM logfac log2pi
    _ = (logfac - ((M + (1 / 2 : ℂ)) * logM - M + log2pi / 2)) + (((w + M + (1 / 2 : ℂ)) * (logM - logwM)) + w) := by
        exact
          (Complex.binet_endpoint_right_unfolded_normal_form
            w M logM logwM logfac log2pi).symm

/-- Algebraic normalization of the real factorial endpoint error. -/
theorem Real.factorialStirlingEndpoint_algebra_normalization
    (A M L L₂ Lπ : ℝ) :
    A - (((M + (1 / 2 : ℝ)) * L - M + (L₂ + Lπ) / 2)) =
      (A - (1 / 2 : ℝ) * (L₂ + L) - M * (L - 1)) - Lπ / 2 := by
  calc
    A - (((M + (1 / 2 : ℝ)) * L - M + (L₂ + Lπ) / 2)) =
        A - ((M * L + (1 / 2 : ℝ) * L - M) +
          (L₂ / 2 + Lπ / 2)) := by
      exact congrArg (fun x : ℝ => A - x) <| by
        calc
          (M + (1 / 2 : ℝ)) * L - M + (L₂ + Lπ) / 2 =
              (M * L + (1 / 2 : ℝ) * L) - M + (L₂ + Lπ) / 2 := by
            exact congrArg (fun x : ℝ => x - M + (L₂ + Lπ) / 2)
              (add_mul M (1 / 2 : ℝ) L)
          _ = (M * L + (1 / 2 : ℝ) * L - M) + (L₂ + Lπ) / 2 := rfl
          _ = (M * L + (1 / 2 : ℝ) * L - M) + (L₂ / 2 + Lπ / 2) := by
            exact congrArg (fun x : ℝ => (M * L + (1 / 2 : ℝ) * L - M) + x)
              (add_div L₂ Lπ 2)
    _ = A + -((M * L + (1 / 2 : ℝ) * L - M) +
          (L₂ / 2 + Lπ / 2)) := sub_eq_add_neg A _
    _ = A + (-(M * L + (1 / 2 : ℝ) * L - M) +
          -(L₂ / 2 + Lπ / 2)) := by
      exact congrArg (fun x : ℝ => A + x)
        (neg_add (M * L + (1 / 2 : ℝ) * L - M) (L₂ / 2 + Lπ / 2))
    _ = A + (-(M * L + (1 / 2 : ℝ) * L - M) +
          (-(L₂ / 2) + -(Lπ / 2))) := by
      exact congrArg
        (fun x : ℝ => A + (-(M * L + (1 / 2 : ℝ) * L - M) + x))
        (neg_add (L₂ / 2) (Lπ / 2))
    _ = (A - (1 / 2 : ℝ) * (L₂ + L) - M * (L - 1)) - Lπ / 2 := by
      have hhalf :
          (1 / 2 : ℝ) * (L₂ + L) =
            L₂ / 2 + (1 / 2 : ℝ) * L := by
        calc
          (1 / 2 : ℝ) * (L₂ + L) =
              (1 / 2 : ℝ) * L₂ + (1 / 2 : ℝ) * L :=
            mul_add (1 / 2 : ℝ) L₂ L
          _ = L₂ / 2 + (1 / 2 : ℝ) * L := by
            have hhalf_left : (1 / 2 : ℝ) * L₂ = L₂ / 2 := by
              calc
                (1 / 2 : ℝ) * L₂ = L₂ * (1 / 2 : ℝ) :=
                  mul_comm (1 / 2 : ℝ) L₂
                _ = L₂ / 2 := by
                  have hinv : (2 : ℝ)⁻¹ = (1 / 2 : ℝ) :=
                    inv_eq_one_div (2 : ℝ)
                  exact Eq.trans
                    (congrArg (fun y : ℝ => L₂ * y) hinv.symm)
                    (div_eq_mul_inv L₂ 2).symm
            exact congrArg (fun x : ℝ => x + (1 / 2 : ℝ) * L) hhalf_left
      have hM :
          M * (L - 1) = M * L - M := by
        calc
          M * (L - 1) = M * L - M * 1 := mul_sub M L 1
          _ = M * L - M := by
            exact congrArg (fun x : ℝ => M * L - x) (mul_one M)
      calc
        A + (-(M * L + (1 / 2 : ℝ) * L - M) +
            (-(L₂ / 2) + -(Lπ / 2))) =
            (A - (L₂ / 2 + (1 / 2 : ℝ) * L) - (M * L - M)) -
              Lπ / 2 := by
          exact
            Real.factorialStirlingEndpoint_final_regroup
              A (M * L) ((1 / 2 : ℝ) * L) M (L₂ / 2) (Lπ / 2)
        _ = (A - (1 / 2 : ℝ) * (L₂ + L) - (M * L - M)) -
              Lπ / 2 := by
          exact congrArg
            (fun x : ℝ => (A - x - (M * L - M)) - Lπ / 2)
            hhalf.symm
        _ = (A - (1 / 2 : ℝ) * (L₂ + L) - M * (L - 1)) -
              Lπ / 2 := by
          exact congrArg
            (fun x : ℝ => (A - (1 / 2 : ℝ) * (L₂ + L) - x) - Lπ / 2)
            hM.symm

/-- Coercion of the logarithm of a nonnegative real into the principal complex
logarithm. -/
theorem Complex.ofReal_log_nonneg_eq_complex_log
    {x : ℝ}
    (hx : 0 ≤ x) :
    ((Real.log x : ℝ) : ℂ) = Complex.log (x : ℂ) := by
  exact Complex.ofReal_log hx

/-- Coercion preserves the algebraic shape of the factorial Stirling endpoint
error. -/
theorem Complex.ofReal_factorialStirlingEndpoint_algebra
    (A M L L₂π : ℝ) :
    ((A - (((M + (1 / 2 : ℝ)) * L - M + L₂π / 2)) : ℝ) : ℂ) =
      (A : ℂ) -
        (((M : ℂ) + (1 / 2 : ℂ)) * (L : ℂ) -
          (M : ℂ) + (L₂π : ℂ) / 2) := by
  have hhalf :
      (((1 / 2 : ℝ) : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    exact map_div₀ Complex.ofRealHom (1 : ℝ) (2 : ℝ)
  have hdiv :
      (((L₂π / 2 : ℝ) : ℝ) : ℂ) = (L₂π : ℂ) / 2 := by
    exact map_div₀ Complex.ofRealHom L₂π (2 : ℝ)
  have hinner :
      ((((M + (1 / 2 : ℝ)) * L - M + L₂π / 2) : ℝ) : ℂ) =
        (((M : ℂ) + (1 / 2 : ℂ)) * (L : ℂ) -
          (M : ℂ) + (L₂π : ℂ) / 2) := by
    calc
      ((((M + (1 / 2 : ℝ)) * L - M + L₂π / 2) : ℝ) : ℂ) =
          (((M + (1 / 2 : ℝ)) * L - M : ℝ) : ℂ) +
            ((L₂π / 2 : ℝ) : ℂ) :=
        map_add Complex.ofRealHom (((M + (1 / 2 : ℝ)) * L - M)) (L₂π / 2)
      _ =
          (((M + (1 / 2 : ℝ)) * L : ℝ) : ℂ) -
            (M : ℂ) + ((L₂π / 2 : ℝ) : ℂ) := by
        exact congrArg
          (fun z : ℂ => z + ((L₂π / 2 : ℝ) : ℂ))
          (map_sub Complex.ofRealHom ((M + (1 / 2 : ℝ)) * L) M)
      _ =
          (((M + (1 / 2 : ℝ) : ℝ) : ℂ) * (L : ℂ)) -
            (M : ℂ) + ((L₂π / 2 : ℝ) : ℂ) := by
        exact congrArg
          (fun z : ℂ => z - (M : ℂ) + ((L₂π / 2 : ℝ) : ℂ))
          (map_mul Complex.ofRealHom (M + (1 / 2 : ℝ)) L)
      _ =
          (((M : ℂ) + ((1 / 2 : ℝ) : ℂ)) * (L : ℂ)) -
            (M : ℂ) + ((L₂π / 2 : ℝ) : ℂ) := by
        exact congrArg
          (fun z : ℂ => z * (L : ℂ) - (M : ℂ) + ((L₂π / 2 : ℝ) : ℂ))
          (map_add Complex.ofRealHom M (1 / 2 : ℝ))
      _ =
          (((M : ℂ) + (1 / 2 : ℂ)) * (L : ℂ)) -
            (M : ℂ) + ((L₂π / 2 : ℝ) : ℂ) := by
        exact congrArg
          (fun z : ℂ => ((M : ℂ) + z) * (L : ℂ) - (M : ℂ) +
            ((L₂π / 2 : ℝ) : ℂ))
          hhalf
      _ =
          (((M : ℂ) + (1 / 2 : ℂ)) * (L : ℂ)) -
            (M : ℂ) + (L₂π : ℂ) / 2 := by
        exact congrArg
          (fun z : ℂ => (((M : ℂ) + (1 / 2 : ℂ)) * (L : ℂ)) -
            (M : ℂ) + z)
          hdiv
  calc
    ((A - (((M + (1 / 2 : ℝ)) * L - M + L₂π / 2)) : ℝ) : ℂ) =
        (A : ℂ) -
          ((((M + (1 / 2 : ℝ)) * L - M + L₂π / 2) : ℝ) : ℂ) :=
      map_sub Complex.ofRealHom A
        (((M + (1 / 2 : ℝ)) * L - M + L₂π / 2))
    _ =
      (A : ℂ) -
        (((M : ℂ) + (1 / 2 : ℂ)) * (L : ℂ) -
          (M : ℂ) + (L₂π : ℂ) / 2) := by
      exact congrArg (fun z : ℂ => (A : ℂ) - z) hinner

/-- Subtracting an appended term from the original term gives the negative
appended term. -/
theorem Complex.sub_add_cancel_to_neg
    (a b : ℂ) :
    a - (a + b) = -b := by
  calc
    a - (a + b) = a + -(a + b) := sub_eq_add_neg a (a + b)
    _ = a + (-a + -b) := by
      exact congrArg (fun x : ℂ => a + x) (neg_add a b)
    _ = (a + -a) + -b := (add_assoc a (-a) (-b)).symm
    _ = 0 + -b := by
      exact congrArg (fun x : ℂ => x + -b) (add_neg_cancel a)
    _ = -b := zero_add (-b)

/-- Multiplying the endpoint affine factor by the endpoint scale leaves the
linear term after the quadratic part is removed. -/
theorem Complex.binetEndpoint_affine_mul_small_sub_quadratic_div
    {w : ℂ}
    {M : ℕ}
    (hM : M ≠ 0) :
    ((w + (M : ℂ) + (1 / 2 : ℂ)) * (w / (M : ℂ))) -
        ((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) =
      w := by
  have hM_ne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hquad :
      (w + (1 / 2 : ℂ)) * (w / (M : ℂ)) =
        (w * (w + (1 / 2 : ℂ))) / (M : ℂ) := by
    calc
      (w + (1 / 2 : ℂ)) * (w / (M : ℂ)) =
          (w + (1 / 2 : ℂ)) * (w * (M : ℂ)⁻¹) :=
        congrArg (fun x : ℂ => (w + (1 / 2 : ℂ)) * x)
          (div_eq_mul_inv w (M : ℂ))
      _ = ((w + (1 / 2 : ℂ)) * w) * (M : ℂ)⁻¹ :=
        (mul_assoc (w + (1 / 2 : ℂ)) w (M : ℂ)⁻¹).symm
      _ = (w * (w + (1 / 2 : ℂ))) * (M : ℂ)⁻¹ := by
        exact congrArg (fun x : ℂ => x * (M : ℂ)⁻¹)
          (mul_comm (w + (1 / 2 : ℂ)) w)
      _ = (w * (w + (1 / 2 : ℂ))) / (M : ℂ) :=
        (div_eq_mul_inv (w * (w + (1 / 2 : ℂ))) (M : ℂ)).symm
  have hlin :
      (M : ℂ) * (w / (M : ℂ)) = w := by
    calc
      (M : ℂ) * (w / (M : ℂ)) =
          (M : ℂ) * (w * (M : ℂ)⁻¹) :=
        congrArg (fun x : ℂ => (M : ℂ) * x)
          (div_eq_mul_inv w (M : ℂ))
      _ = (M : ℂ) * ((M : ℂ)⁻¹ * w) := by
        exact congrArg (fun x : ℂ => (M : ℂ) * x)
          (mul_comm w (M : ℂ)⁻¹)
      _ = ((M : ℂ) * (M : ℂ)⁻¹) * w :=
        (mul_assoc (M : ℂ) (M : ℂ)⁻¹ w).symm
      _ = 1 * w := by
        exact congrArg (fun x : ℂ => x * w) (mul_inv_cancel₀ hM_ne)
      _ = w := one_mul w
  have haff :
      w + (M : ℂ) + (1 / 2 : ℂ) = (w + (1 / 2 : ℂ)) + (M : ℂ) := by
    calc
      w + (M : ℂ) + (1 / 2 : ℂ) =
          (w + (M : ℂ)) + (1 / 2 : ℂ) := rfl
      _ = w + ((M : ℂ) + (1 / 2 : ℂ)) :=
        add_assoc w (M : ℂ) (1 / 2 : ℂ)
      _ = w + ((1 / 2 : ℂ) + (M : ℂ)) := by
        exact congrArg (fun x : ℂ => w + x)
          (add_comm (M : ℂ) (1 / 2 : ℂ))
      _ = (w + (1 / 2 : ℂ)) + (M : ℂ) :=
        (add_assoc w (1 / 2 : ℂ) (M : ℂ)).symm
  calc
    ((w + (M : ℂ) + (1 / 2 : ℂ)) * (w / (M : ℂ))) -
        ((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) =
      (((w + (1 / 2 : ℂ)) + (M : ℂ)) * (w / (M : ℂ))) -
        ((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) := by
        exact congrArg
          (fun x : ℂ =>
            x * (w / (M : ℂ)) -
              ((w * (w + (1 / 2 : ℂ))) / (M : ℂ)))
          haff
    _ =
      (((w + (1 / 2 : ℂ)) * (w / (M : ℂ))) +
          ((M : ℂ) * (w / (M : ℂ)))) -
        ((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) := by
        exact congrArg
          (fun x : ℂ =>
            x - ((w * (w + (1 / 2 : ℂ))) / (M : ℂ)))
          (add_mul (w + (1 / 2 : ℂ)) (M : ℂ) (w / (M : ℂ)))
    _ =
      (((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) + w) -
        ((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) := by
        exact congrArg₂ HSub.hSub (congrArg₂ HAdd.hAdd hquad hlin) rfl
    _ = w := add_sub_cancel_left ((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) w

/-- Endpoint Taylor algebra once the branch logarithm has been separated. -/
theorem Complex.binetEndpointLogShiftError_taylor_algebra
    {w L : ℂ}
    {M : ℕ}
    (hM : M ≠ 0) :
    ((w + (M : ℂ) + (1 / 2 : ℂ)) *
        (Complex.log (M : ℂ) - (Complex.log (M : ℂ) + L))) + w =
      -((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) -
        (w + (M : ℂ) + (1 / 2 : ℂ)) * (L - w / (M : ℂ)) := by
  let A : ℂ := w + (M : ℂ) + (1 / 2 : ℂ)
  let Q : ℂ := (w * (w + (1 / 2 : ℂ))) / (M : ℂ)
  have hlogdiff :
      Complex.log (M : ℂ) - (Complex.log (M : ℂ) + L) = -L :=
    Complex.sub_add_cancel_to_neg (Complex.log (M : ℂ)) L
  have hendpoint : A * (w / (M : ℂ)) - Q = w := by
    exact Complex.binetEndpoint_affine_mul_small_sub_quadratic_div hM
  have hregroup :
      -(A * L) + (A * (w / (M : ℂ)) - Q) =
        -Q - A * (L - w / (M : ℂ)) := by
    calc
      -(A * L) + (A * (w / (M : ℂ)) - Q) =
          -(A * L) + (A * (w / (M : ℂ)) + -Q) := by
        exact congrArg (fun x : ℂ => -(A * L) + x)
          (sub_eq_add_neg (A * (w / (M : ℂ))) Q)
      _ = (-(A * L) + A * (w / (M : ℂ))) + -Q :=
        (add_assoc (-(A * L)) (A * (w / (M : ℂ))) (-Q)).symm
      _ = -Q + (-(A * L) + A * (w / (M : ℂ))) := by
        exact add_comm (-(A * L) + A * (w / (M : ℂ))) (-Q)
      _ = -Q + (-(A * L) + A * (w / (M : ℂ))) := rfl
      _ = -Q + -(A * (L - w / (M : ℂ))) := by
        exact congrArg (fun x : ℂ => -Q + x) <| by
          calc
            -(A * L) + A * (w / (M : ℂ)) =
                A * (w / (M : ℂ)) + -(A * L) :=
              add_comm (-(A * L)) (A * (w / (M : ℂ)))
            _ = A * (w / (M : ℂ)) - A * L :=
              (sub_eq_add_neg (A * (w / (M : ℂ))) (A * L)).symm
            _ = -(A * L - A * (w / (M : ℂ))) :=
              (neg_sub (A * L) (A * (w / (M : ℂ)))).symm
            _ = -(A * (L - w / (M : ℂ))) :=
              (congrArg Neg.neg
                (mul_sub A L (w / (M : ℂ)))).symm
      _ = -Q - A * (L - w / (M : ℂ)) :=
        (sub_eq_add_neg (-Q) (A * (L - w / (M : ℂ)))).symm
  calc
    A * (Complex.log (M : ℂ) - (Complex.log (M : ℂ) + L)) + w =
        A * (-L) + w := by
      exact congrArg (fun x : ℂ => A * x + w) hlogdiff
    _ = -(A * L) + w := by
      exact congrArg (fun x : ℂ => x + w) (mul_neg A L)
    _ = -(A * L) + (A * (w / (M : ℂ)) - Q) := by
      exact congrArg (fun x : ℂ => -(A * L) + x) hendpoint.symm
    _ = -Q - A * (L - w / (M : ℂ)) := hregroup

/-- The factorial part of the logarithmic Stirling endpoint error. -/
noncomputable def Complex.binetAbelPlanaFactorialStirlingError
    (M : ℕ) : ℂ :=
  Complex.log ((Nat.factorial M : ℕ) : ℂ) -
    (((M : ℂ) + (1 / 2 : ℂ)) * Complex.log (M : ℂ) -
      (M : ℂ) +
        (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2)

/-- Definition unfolding for the complex factorial Stirling endpoint error. -/
theorem Complex.binetAbelPlanaFactorialStirlingError_unfold
    (M : ℕ) :
    Complex.binetAbelPlanaFactorialStirlingError M =
      Complex.log ((Nat.factorial M : ℕ) : ℂ) -
        (((M : ℂ) + (1 / 2 : ℂ)) * Complex.log (M : ℂ) -
          (M : ℂ) +
            (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2) :=
  rfl

/-- Real-valued factorial Stirling endpoint error before coercion to `ℂ`. -/
noncomputable def Real.binetAbelPlanaFactorialStirlingError
    (M : ℕ) : ℝ :=
  Real.log ((Nat.factorial M : ℕ) : ℝ) -
    (((M : ℝ) + (1 / 2 : ℝ)) * Real.log (M : ℝ) -
      (M : ℝ) +
        Real.log (2 * Real.pi) / 2)

/-- Definition unfolding for the real factorial Stirling endpoint error. -/
theorem Real.binetAbelPlanaFactorialStirlingError_unfold
    (M : ℕ) :
    Real.binetAbelPlanaFactorialStirlingError M =
      Real.log ((Nat.factorial M : ℕ) : ℝ) -
        (((M : ℝ) + (1 / 2 : ℝ)) * Real.log (M : ℝ) -
          (M : ℝ) +
            Real.log (2 * Real.pi) / 2) :=
  rfl

/-- The real factorial Stirling endpoint error is the logarithm of mathlib's
Stirling sequence, normalized by its limiting value `√π`. -/
theorem Real.binetAbelPlanaFactorialStirlingError_eq_log_stirlingSeq_sub_log_sqrt_pi
    (M : ℕ)
    (hM : M ≠ 0) :
    Real.binetAbelPlanaFactorialStirlingError M =
      Real.log (Stirling.stirlingSeq M) - Real.log (Real.sqrt Real.pi) := by
  have hMpos_nat : 0 < M := Nat.pos_of_ne_zero hM
  have hMpos_real : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos_nat
  have htwoMpos : 0 < (2 : ℝ) * M := mul_pos two_pos hMpos_real
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hsqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi_pos
  have hlog_sqrt_pi :
      Real.log (Real.sqrt Real.pi) = Real.log Real.pi / 2 := by
    exact Real.log_sqrt hpi_pos.le
  have hlog_two_mul_M :
      Real.log ((2 : ℝ) * M) = Real.log (2 : ℝ) + Real.log (M : ℝ) := by
    exact Real.log_mul two_ne_zero hMpos_real.ne'
  have hlog_M_div_exp :
      Real.log ((M : ℝ) / Real.exp 1) = Real.log (M : ℝ) - 1 := by
    have hdiv : Real.log ((M : ℝ) / Real.exp 1) =
        Real.log (M : ℝ) - Real.log (Real.exp 1) :=
      Real.log_div hMpos_real.ne' (Real.exp_pos 1).ne'
    have hlog_exp : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    calc
      Real.log ((M : ℝ) / Real.exp 1) =
          Real.log (M : ℝ) - Real.log (Real.exp 1) :=
        hdiv
      _ = Real.log (M : ℝ) - 1 := by
        exact congrArg (fun x : ℝ => Real.log (M : ℝ) - x) hlog_exp
  have hlog_two_pi :
      Real.log (2 * Real.pi) = Real.log (2 : ℝ) + Real.log Real.pi := by
    exact Real.log_mul two_ne_zero hpi_pos.ne'
  calc
    Real.binetAbelPlanaFactorialStirlingError M
        =
        Real.log ((Nat.factorial M : ℕ) : ℝ) -
          (((M : ℝ) + (1 / 2 : ℝ)) * Real.log (M : ℝ) -
            (M : ℝ) +
              Real.log (2 * Real.pi) / 2) := by
          rfl
    _ =
        (Real.log ((Nat.factorial M : ℕ) : ℝ) -
            (1 / 2 : ℝ) * Real.log ((2 : ℝ) * M) -
              (M : ℝ) * Real.log ((M : ℝ) / Real.exp 1)) -
          Real.log (Real.sqrt Real.pi) := by
          have h1 := hlog_sqrt_pi
          have h2 := hlog_two_mul_M
          have h3 := hlog_M_div_exp
          have h4 := hlog_two_pi
          have hlog_two_from_two_pi :
              Real.log (2 * Real.pi) - Real.log Real.pi =
                Real.log (2 : ℝ) := by
            calc
              Real.log (2 * Real.pi) - Real.log Real.pi =
                  (Real.log (2 : ℝ) + Real.log Real.pi) -
                    Real.log Real.pi := by
                exact congrArg (fun x : ℝ => x - Real.log Real.pi) h4
              _ = Real.log (2 : ℝ) := by
                exact add_sub_cancel_right (Real.log (2 : ℝ)) (Real.log Real.pi)
          calc
            Real.log ((Nat.factorial M : ℕ) : ℝ) -
                (((M : ℝ) + (1 / 2 : ℝ)) * Real.log (M : ℝ) -
                  (M : ℝ) +
                    Real.log (2 * Real.pi) / 2) =
                Real.log ((Nat.factorial M : ℕ) : ℝ) -
                (((M : ℝ) + (1 / 2 : ℝ)) * Real.log (M : ℝ) -
                  (M : ℝ) +
                    ((Real.log (2 * Real.pi) - Real.log Real.pi) +
                      Real.log Real.pi) / 2) := by
                have hrestore :
                    (Real.log (2 * Real.pi) - Real.log Real.pi) +
                      Real.log Real.pi =
                    Real.log (2 * Real.pi) :=
                  sub_add_cancel (Real.log (2 * Real.pi)) (Real.log Real.pi)
                exact congrArg
                  (fun x : ℝ =>
                    Real.log ((Nat.factorial M : ℕ) : ℝ) -
                      (((M : ℝ) + (1 / 2 : ℝ)) * Real.log (M : ℝ) -
                        (M : ℝ) + x / 2))
                  hrestore.symm
            _ =
                (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                    (1 / 2 : ℝ) *
                      (Real.log (2 * Real.pi) - Real.log Real.pi +
                        Real.log (M : ℝ)) -
                      (M : ℝ) *
                        (Real.log (M : ℝ) - 1)) -
                  Real.log Real.pi / 2 := by
                exact
                  Real.factorialStirlingEndpoint_algebra_normalization
                    (Real.log ((Nat.factorial M : ℕ) : ℝ))
                    (M : ℝ)
                    (Real.log (M : ℝ))
                    (Real.log (2 * Real.pi) - Real.log Real.pi)
                    (Real.log Real.pi)
            _ =
                (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                    (1 / 2 : ℝ) * Real.log ((2 : ℝ) * M) -
                      (M : ℝ) * Real.log ((M : ℝ) / Real.exp 1)) -
                  Real.log (Real.sqrt Real.pi) := by
                calc
                  (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                      (1 / 2 : ℝ) *
                        (Real.log (2 * Real.pi) - Real.log Real.pi +
                          Real.log (M : ℝ)) -
                        (M : ℝ) *
                          (Real.log (M : ℝ) - 1)) -
                    Real.log Real.pi / 2 =
                      (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                        (1 / 2 : ℝ) *
                          (Real.log (2 : ℝ) + Real.log (M : ℝ)) -
                          (M : ℝ) *
                            (Real.log (M : ℝ) - 1)) -
                      Real.log Real.pi / 2 := by
                    exact congrArg
                      (fun x : ℝ =>
                        (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                          (1 / 2 : ℝ) * (x + Real.log (M : ℝ)) -
                            (M : ℝ) * (Real.log (M : ℝ) - 1)) -
                          Real.log Real.pi / 2)
                      hlog_two_from_two_pi
                  _ =
                      (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                        (1 / 2 : ℝ) * Real.log ((2 : ℝ) * M) -
                          (M : ℝ) *
                            (Real.log (M : ℝ) - 1)) -
                      Real.log Real.pi / 2 := by
                    exact congrArg
                      (fun x : ℝ =>
                        (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                          (1 / 2 : ℝ) * x -
                            (M : ℝ) * (Real.log (M : ℝ) - 1)) -
                          Real.log Real.pi / 2)
                      h2.symm
                  _ =
                      (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                        (1 / 2 : ℝ) * Real.log ((2 : ℝ) * M) -
                          (M : ℝ) *
                            Real.log ((M : ℝ) / Real.exp 1)) -
                      Real.log Real.pi / 2 := by
                    exact congrArg
                      (fun x : ℝ =>
                        (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                          (1 / 2 : ℝ) * Real.log ((2 : ℝ) * M) -
                            (M : ℝ) * x) -
                          Real.log Real.pi / 2)
                      h3.symm
                  _ =
                      (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                        (1 / 2 : ℝ) * Real.log ((2 : ℝ) * M) -
                          (M : ℝ) *
                            Real.log ((M : ℝ) / Real.exp 1)) -
                      Real.log (Real.sqrt Real.pi) := by
                    exact congrArg
                      (fun x : ℝ =>
                        (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                          (1 / 2 : ℝ) * Real.log ((2 : ℝ) * M) -
                            (M : ℝ) *
                              Real.log ((M : ℝ) / Real.exp 1)) -
                          x)
                      h1.symm
      _ =
          Real.log (Stirling.stirlingSeq M) -
            Real.log (Real.sqrt Real.pi) := by
            exact congrArg
              (fun x : ℝ => x - Real.log (Real.sqrt Real.pi))
              (Stirling.log_stirlingSeq_formula M).symm

/-- The complex factorial Stirling endpoint error is the coercion of its real
normal form. -/
theorem Complex.binetAbelPlanaFactorialStirlingError_eq_ofReal
    (M : ℕ)
    (hM : M ≠ 0) :
    Complex.binetAbelPlanaFactorialStirlingError M =
      (Real.binetAbelPlanaFactorialStirlingError M : ℂ) := by
  have hMpos_nat : 0 < M := Nat.pos_of_ne_zero hM
  have hMpos_real : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos_nat
  have hfact_nonneg :
      0 ≤ ((Nat.factorial M : ℕ) : ℝ) :=
    Nat.cast_nonneg (Nat.factorial M)
  have hM_nonneg : 0 ≤ (M : ℝ) := hMpos_real.le
  have htwo_pi_nonneg : 0 ≤ (2 : ℝ) * Real.pi :=
    (mul_pos two_pos Real.pi_pos).le
  have hcomplex_unfold :
      Complex.binetAbelPlanaFactorialStirlingError M =
        Complex.log ((Nat.factorial M : ℕ) : ℂ) -
          (((M : ℂ) + (1 / 2 : ℂ)) * Complex.log (M : ℂ) -
            (M : ℂ) +
              (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2) :=
    Complex.binetAbelPlanaFactorialStirlingError_unfold M
  have hreal_unfold :
      Real.binetAbelPlanaFactorialStirlingError M =
        Real.log ((Nat.factorial M : ℕ) : ℝ) -
          (((M : ℝ) + (1 / 2 : ℝ)) * Real.log (M : ℝ) -
            (M : ℝ) +
              Real.log (2 * Real.pi) / 2) :=
    Real.binetAbelPlanaFactorialStirlingError_unfold M
  calc
    Complex.binetAbelPlanaFactorialStirlingError M =
        Complex.log (((Nat.factorial M : ℕ) : ℂ)) -
          (((M : ℂ) + (1 / 2 : ℂ)) * Complex.log (M : ℂ) -
            (M : ℂ) + (((Real.log (2 * Real.pi) : ℝ) : ℂ) / 2)) :=
          hcomplex_unfold
    _ =
        ((Real.log ((Nat.factorial M : ℕ) : ℝ) : ℝ) : ℂ) -
          (((M : ℂ) + (1 / 2 : ℂ)) *
            Complex.log (M : ℂ) -
            (M : ℂ) + (((Real.log (2 * Real.pi) : ℝ) : ℂ) / 2)) := by
        exact
          congrArg
            (fun z : ℂ =>
              z -
                (((M : ℂ) + (1 / 2 : ℂ)) * Complex.log (M : ℂ) -
                  (M : ℂ) +
                    (((Real.log (2 * Real.pi) : ℝ) : ℂ) / 2)))
            (Complex.ofReal_log_nonneg_eq_complex_log hfact_nonneg).symm
    _ =
        ((Real.log ((Nat.factorial M : ℕ) : ℝ) : ℝ) : ℂ) -
          (((M : ℂ) + (1 / 2 : ℂ)) *
            ((Real.log (M : ℝ) : ℝ) : ℂ) -
            (M : ℂ) +
              (((Real.log (2 * Real.pi) : ℝ) : ℂ) / 2)) := by
        exact
          congrArg
            (fun z : ℂ =>
              ((Real.log ((Nat.factorial M : ℕ) : ℝ) : ℝ) : ℂ) -
                (((M : ℂ) + (1 / 2 : ℂ)) * z -
                  (M : ℂ) +
                    (((Real.log (2 * Real.pi) : ℝ) : ℂ) / 2)))
            (Complex.ofReal_log_nonneg_eq_complex_log hM_nonneg).symm
    _ =
        (Real.log ((Nat.factorial M : ℕ) : ℝ) -
          (((M : ℝ) + (1 / 2 : ℝ)) * Real.log (M : ℝ) -
            (M : ℝ) + Real.log (2 * Real.pi) / 2) : ℝ) := by
        exact
          (Complex.ofReal_factorialStirlingEndpoint_algebra
            (Real.log ((Nat.factorial M : ℕ) : ℝ))
            (M : ℝ)
            (Real.log (M : ℝ))
            (Real.log (2 * Real.pi))).symm
    _ = (Real.binetAbelPlanaFactorialStirlingError M : ℂ) := by
        exact congrArg (fun x : ℝ => (x : ℂ)) hreal_unfold.symm

/-- The real factorial Stirling endpoint error tends to zero. -/
theorem Real.binetAbelPlanaFactorialStirlingError_tendsto_zero_owner :
    Filter.Tendsto
      (fun N : ℕ =>
        Real.binetAbelPlanaFactorialStirlingError (N + 1))
      Filter.atTop
      (𝓝 (0 : ℝ)) := by
  have hstirling :
      Filter.Tendsto
        (fun N : ℕ => Stirling.stirlingSeq (N + 1))
        Filter.atTop
        (𝓝 (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp
      (Filter.tendsto_add_atTop_nat 1)
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hlog :
      Filter.Tendsto
        (fun N : ℕ => Real.log (Stirling.stirlingSeq (N + 1)))
        Filter.atTop
        (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log hsqrt_ne).tendsto.comp hstirling
  have hsub :
      Filter.Tendsto
        (fun N : ℕ =>
          Real.log (Stirling.stirlingSeq (N + 1)) -
            Real.log (Real.sqrt Real.pi))
        Filter.atTop
        (𝓝 (Real.log (Real.sqrt Real.pi) -
          Real.log (Real.sqrt Real.pi))) :=
    hlog.sub tendsto_const_nhds
  have hevent :
      (fun N : ℕ =>
        Real.log (Stirling.stirlingSeq (N + 1)) -
          Real.log (Real.sqrt Real.pi)) =ᶠ[Filter.atTop]
      (fun N : ℕ =>
        Real.binetAbelPlanaFactorialStirlingError (N + 1)) :=
    Filter.Eventually.of_forall
      (fun N =>
        (Real.binetAbelPlanaFactorialStirlingError_eq_log_stirlingSeq_sub_log_sqrt_pi
          (N + 1)
          (Nat.succ_ne_zero N)).symm)
  exact sub_self (Real.log (Real.sqrt Real.pi)) ▸ (hsub.congr' hevent)

/-- The endpoint shift error measuring
`(M + w + 1/2) log (1 + w/M) - w`, in branch-safe difference form. -/
noncomputable def Complex.binetAbelPlanaEndpointLogShiftError
    (w : ℂ)
    (M : ℕ) : ℂ :=
  ((w + (M : ℂ) + (1 / 2 : ℂ)) *
      (Complex.log (M : ℂ) - Complex.log (w + (M : ℂ)))) +
    w

/-- Definition unfolding for the endpoint logarithmic-shift error. -/
theorem Complex.binetAbelPlanaEndpointLogShiftError_unfold
    (w : ℂ)
    (M : ℕ) :
    Complex.binetAbelPlanaEndpointLogShiftError w M =
      ((w + (M : ℂ) + (1 / 2 : ℂ)) *
          (Complex.log (M : ℂ) - Complex.log (w + (M : ℂ)))) +
        w := rfl

/-- The positive-real scaling factor in the endpoint logarithm. -/
noncomputable def Complex.binetEndpointScale
    (M : ℕ) : ℂ :=
  (M : ℂ)

/-- Definition unfolding for the endpoint scale. -/
theorem Complex.binetEndpointScale_unfold
    (M : ℕ) :
    Complex.binetEndpointScale M = (M : ℂ) := rfl

/-- The small logarithmic endpoint variable `w / M`. -/
noncomputable def Complex.binetEndpointSmallVariable
    (w : ℂ)
    (M : ℕ) : ℂ :=
  w / Complex.binetEndpointScale M

/-- Definition unfolding for the small endpoint variable. -/
theorem Complex.binetEndpointSmallVariable_unfold
    (w : ℂ)
    (M : ℕ) :
    Complex.binetEndpointSmallVariable w M = w / (M : ℂ) := by
  exact congrArg (fun z : ℂ => w / z)
    (Complex.binetEndpointScale_unfold M)

/-- Norm of division by the positive natural endpoint scale. -/
theorem Complex.norm_div_natCast
    (z : ℂ)
    (M : ℕ) :
    ‖z / (M : ℂ)‖ = ‖z‖ / (M : ℝ) := by
  calc
    ‖z / (M : ℂ)‖ = ‖z‖ / ‖(M : ℂ)‖ := norm_div z (M : ℂ)
    _ = ‖z‖ / (M : ℝ) := by
      exact congrArg (fun x : ℝ => ‖z‖ / x)
        (Complex.norm_natCast M)

/-- Norm of the endpoint small variable after unfolding the endpoint scale. -/
theorem Complex.norm_binetEndpointSmallVariable_eq
    (w : ℂ)
    (M : ℕ) :
    ‖Complex.binetEndpointSmallVariable w M‖ = ‖w‖ / (M : ℝ) := by
  exact
    Eq.trans
      (congrArg norm (Complex.binetEndpointSmallVariable_unfold w M))
      (Complex.norm_div_natCast w M)

/-- The endpoint logarithmic Taylor error `log (1 + z) - z`. -/
noncomputable def Complex.binetEndpointLogTaylorError
    (w : ℂ)
    (M : ℕ) : ℂ :=
  Complex.log (1 + Complex.binetEndpointSmallVariable w M) -
    Complex.binetEndpointSmallVariable w M

/-- Definition unfolding for the endpoint logarithmic Taylor error. -/
theorem Complex.binetEndpointLogTaylorError_unfold
    (w : ℂ)
    (M : ℕ) :
    Complex.binetEndpointLogTaylorError w M =
      Complex.log (1 + Complex.binetEndpointSmallVariable w M) -
        Complex.binetEndpointSmallVariable w M := rfl

/-- The endpoint logarithmic branch identity in the open right half-plane. -/
theorem Complex.binetEndpoint_log_nat_add_eq_log_nat_add_log_one_add
    {w : ℂ}
    {M : ℕ}
    (hM : M ≠ 0)
    (hw : 0 < w.re) :
    Complex.log (w + (M : ℂ)) =
      Complex.log (M : ℂ) +
        Complex.log (1 + Complex.binetEndpointSmallVariable w M) := by
  have hMpos_nat : 0 < M := Nat.pos_of_ne_zero hM
  have hMpos_real : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos_nat
  have hprod :
      ((M : ℂ) *
          (1 + Complex.binetEndpointSmallVariable w M)) =
        w + (M : ℂ) := by
    have hM_ne : (M : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hM
    have hcancel : (M : ℂ) * (M : ℂ)⁻¹ = 1 :=
      mul_inv_cancel₀ hM_ne
    calc
      (M : ℂ) * (1 + Complex.binetEndpointSmallVariable w M) =
          (M : ℂ) * (1 + w / (M : ℂ)) := by
        exact congrArg (fun z : ℂ => (M : ℂ) * (1 + z))
          (Complex.binetEndpointSmallVariable_unfold w M)
      _ = (M : ℂ) * 1 + (M : ℂ) * (w / (M : ℂ)) := by
        exact mul_add (M : ℂ) 1 (w / (M : ℂ))
      _ = (M : ℂ) + (M : ℂ) * (w / (M : ℂ)) := by
        exact congrArg
          (fun x : ℂ => x + (M : ℂ) * (w / (M : ℂ)))
          (mul_one (M : ℂ))
      _ = (M : ℂ) + (M : ℂ) * (w * (M : ℂ)⁻¹) := by
        exact congrArg
          (fun x : ℂ => (M : ℂ) + (M : ℂ) * x)
          (div_eq_mul_inv w (M : ℂ))
      _ = (M : ℂ) + (M : ℂ) * ((M : ℂ)⁻¹ * w) := by
        exact congrArg
          (fun x : ℂ => (M : ℂ) + (M : ℂ) * x)
          (mul_comm w (M : ℂ)⁻¹)
      _ = (M : ℂ) + ((M : ℂ) * (M : ℂ)⁻¹) * w := by
        exact congrArg
          (fun x : ℂ => (M : ℂ) + x)
          ((mul_assoc (M : ℂ) (M : ℂ)⁻¹ w).symm)
      _ = (M : ℂ) + 1 * w := by
        exact congrArg
          (fun x : ℂ => (M : ℂ) + x * w)
          hcancel
      _ = (M : ℂ) + w := by
        exact congrArg (fun x : ℂ => (M : ℂ) + x) (one_mul w)
      _ = w + (M : ℂ) := by
        exact add_comm (M : ℂ) w
  have hsmall_ne :
      (1 + Complex.binetEndpointSmallVariable w M) ≠ 0 := by
    exact fun hzero => by
      have hmul_zero :
        (M : ℂ) * (1 + Complex.binetEndpointSmallVariable w M) = 0 := by
        calc
          (M : ℂ) * (1 + Complex.binetEndpointSmallVariable w M) =
              (M : ℂ) * 0 := by
            exact congrArg (fun z : ℂ => (M : ℂ) * z) hzero
          _ = 0 :=
            mul_zero (M : ℂ)
      have hsum_zero : w + (M : ℂ) = 0 := by
        exact hprod.symm ▸ hmul_zero
      have hre_zero : (w + (M : ℂ)).re = 0 := by
        exact congrArg Complex.re hsum_zero
      have hre_eq : (w + (M : ℂ)).re = w.re + (M : ℝ) := by
        calc
          (w + (M : ℂ)).re = w.re + (M : ℂ).re :=
            Complex.add_re w (M : ℂ)
          _ = w.re + (M : ℝ) := by
            exact congrArg (fun r : ℝ => w.re + r)
              (Complex.ofReal_re (M : ℝ))
      have hre_pos : 0 < (w + (M : ℂ)).re := by
        exact hre_eq.symm ▸ add_pos hw hMpos_real
      exact (ne_of_gt hre_pos) hre_zero
  calc
    Complex.log (w + (M : ℂ))
        = Complex.log ((M : ℂ) *
            (1 + Complex.binetEndpointSmallVariable w M)) := by
          exact congrArg Complex.log hprod.symm
    _ = Real.log (M : ℝ) +
        Complex.log (1 + Complex.binetEndpointSmallVariable w M) := by
      exact
        Complex.log_ofReal_mul hMpos_real hsmall_ne
    _ = Complex.log (M : ℂ) +
        Complex.log (1 + Complex.binetEndpointSmallVariable w M) := by
      exact congrArg
        (fun z : ℂ =>
          z + Complex.log (1 + Complex.binetEndpointSmallVariable w M))
        (Complex.ofReal_log hMpos_real.le)

/-- Branch-safe endpoint log-shift error in Taylor-remainder normal form. -/
theorem Complex.binetAbelPlanaEndpointLogShiftError_eq_taylor_normal_form
    {w : ℂ}
    {M : ℕ}
    (hM : M ≠ 0)
    (hw : 0 < w.re) :
    Complex.binetAbelPlanaEndpointLogShiftError w M =
      -((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) -
        (w + (M : ℂ) + (1 / 2 : ℂ)) *
          Complex.binetEndpointLogTaylorError w M := by
  have hlog :
      Complex.log (w + (M : ℂ)) =
        Complex.log (M : ℂ) +
          Complex.log (1 + Complex.binetEndpointSmallVariable w M) :=
    Complex.binetEndpoint_log_nat_add_eq_log_nat_add_log_one_add hM hw
  have hshift :
      Complex.binetAbelPlanaEndpointLogShiftError w M =
        ((w + (M : ℂ) + (1 / 2 : ℂ)) *
          (Complex.log (M : ℂ) - Complex.log (w + (M : ℂ)))) + w :=
    Complex.binetAbelPlanaEndpointLogShiftError_unfold w M
  have htaylor :
      Complex.binetEndpointLogTaylorError w M =
        Complex.log (1 + Complex.binetEndpointSmallVariable w M) -
          Complex.binetEndpointSmallVariable w M :=
    Complex.binetEndpointLogTaylorError_unfold w M
  have hsmall :
      Complex.binetEndpointSmallVariable w M = w / (M : ℂ) :=
    Complex.binetEndpointSmallVariable_unfold w M
  exact
    Eq.trans hshift
      (Eq.trans
        (congrArg
          (fun z : ℂ =>
            ((w + (M : ℂ) + (1 / 2 : ℂ)) *
              (Complex.log (M : ℂ) - z)) + w)
          hlog)
        (Eq.trans
          (Complex.binetEndpointLogShiftError_taylor_algebra
            (w := w)
            (L := Complex.log (1 + w / (M : ℂ)))
            hM)
          (congrArg
            (fun z : ℂ =>
              -((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) -
                (w + (M : ℂ) + (1 / 2 : ℂ)) * z)
            (Eq.trans htaylor
              (congrArg
                (fun z : ℂ => Complex.log (1 + z) - z)
                hsmall)).symm)))

/-- Eventually the endpoint small variable lies in the Taylor disk
`‖z‖ ≤ 1 / 2`. -/
theorem Complex.eventually_norm_binetEndpointSmallVariable_le_half
    (w : ℂ) :
    ∀ᶠ M : ℕ in Filter.atTop,
      ‖Complex.binetEndpointSmallVariable w M‖ ≤ (1 / 2 : ℝ) := by
  have hbound :
      ∀ᶠ M : ℕ in Filter.atTop, 2 * ‖w‖ ≤ (M : ℝ) := by
    exact
      (Filter.eventually_ge_atTop (Nat.ceil (2 * ‖w‖))).mono
        (fun M hM =>
          by
            have hceil :
                2 * ‖w‖ ≤ ((Nat.ceil (2 * ‖w‖)) : ℝ) :=
              Nat.le_ceil (2 * ‖w‖)
            have hcast :
                ((Nat.ceil (2 * ‖w‖)) : ℝ) ≤ (M : ℝ) :=
              Nat.cast_le.mpr hM
            exact hceil.trans hcast)
  exact
    hbound.mono
      (fun M hM =>
        match M with
        | 0 =>
          calc
            ‖Complex.binetEndpointSmallVariable w 0‖ = ‖w / (0 : ℂ)‖ := by
              have hcast_zero : ((0 : ℕ) : ℂ) = 0 :=
                Nat.cast_zero
              exact congrArg norm
                (Eq.trans
                  (Complex.binetEndpointSmallVariable_unfold w 0)
                  (congrArg (fun z : ℂ => w / z) hcast_zero))
            _ = 0 := by
              exact Eq.trans (congrArg norm (div_zero w)) norm_zero
            _ ≤ (1 / 2 : ℝ) :=
              div_nonneg zero_le_one zero_le_two
        | Nat.succ M' =>
          by
            have hMpos_nat : 0 < Nat.succ M' := Nat.succ_pos M'
            have hMpos_real : 0 < ((Nat.succ M' : ℕ) : ℝ) :=
              Nat.cast_pos.mpr hMpos_nat
            have htwo_ne : (2 : ℝ) ≠ 0 :=
              two_ne_zero
            have hdiv_bound :
                (2 * ‖w‖) / (2 : ℝ) ≤
                  ((Nat.succ M' : ℕ) : ℝ) / (2 : ℝ) :=
              div_le_div_of_nonneg_right hM zero_le_two
            have hleft :
                (2 * ‖w‖) / (2 : ℝ) = ‖w‖ := by
              calc
                (2 * ‖w‖) / (2 : ℝ) = (‖w‖ * 2) / (2 : ℝ) := by
                  exact congrArg (fun x : ℝ => x / (2 : ℝ))
                    (mul_comm (2 : ℝ) ‖w‖)
                _ = ‖w‖ :=
                  mul_div_cancel_right₀ ‖w‖ htwo_ne
            have hright :
                ((Nat.succ M' : ℕ) : ℝ) / (2 : ℝ) =
                  (1 / 2 : ℝ) * ((Nat.succ M' : ℕ) : ℝ) := by
              calc
                ((Nat.succ M' : ℕ) : ℝ) / (2 : ℝ) =
                    ((Nat.succ M' : ℕ) : ℝ) * (2 : ℝ)⁻¹ := by
                  exact div_eq_mul_inv ((Nat.succ M' : ℕ) : ℝ) (2 : ℝ)
                _ = (2 : ℝ)⁻¹ * ((Nat.succ M' : ℕ) : ℝ) := by
                  exact mul_comm ((Nat.succ M' : ℕ) : ℝ) (2 : ℝ)⁻¹
                _ = (1 / 2 : ℝ) * ((Nat.succ M' : ℕ) : ℝ) := by
                  exact congrArg
                    (fun x : ℝ => x * ((Nat.succ M' : ℕ) : ℝ))
                    (inv_eq_one_div (2 : ℝ))
            have hhalf :
                ‖w‖ ≤ (1 / 2 : ℝ) * ((Nat.succ M' : ℕ) : ℝ) := by
              calc
                ‖w‖ = (2 * ‖w‖) / (2 : ℝ) := hleft.symm
                _ ≤ ((Nat.succ M' : ℕ) : ℝ) / (2 : ℝ) := hdiv_bound
                _ = (1 / 2 : ℝ) * ((Nat.succ M' : ℕ) : ℝ) := hright
            have hnorm_div :
                ‖w / (((Nat.succ M' : ℕ) : ℂ))‖ =
                  ‖w‖ / ((Nat.succ M' : ℕ) : ℝ) := by
              calc
                ‖w / (((Nat.succ M' : ℕ) : ℂ))‖ =
                    ‖w‖ / ‖(((Nat.succ M' : ℕ) : ℂ))‖ :=
                  norm_div w (((Nat.succ M' : ℕ) : ℂ))
                _ = ‖w‖ / ((Nat.succ M' : ℕ) : ℝ) := by
                  exact congrArg (fun x : ℝ => ‖w‖ / x)
                    (Complex.norm_natCast (Nat.succ M'))
            calc
              ‖Complex.binetEndpointSmallVariable w (Nat.succ M')‖ =
                  ‖w / (((Nat.succ M' : ℕ) : ℂ))‖ := by
                exact congrArg norm
                  (Complex.binetEndpointSmallVariable_unfold w (Nat.succ M'))
              _ = ‖w‖ / ((Nat.succ M' : ℕ) : ℝ) := hnorm_div
              _ ≤ (1 / 2 : ℝ) :=
                (div_le_iff₀ hMpos_real).mpr hhalf)

/-- A number bounded by `1 / 2` leaves a positive distance from `1`. -/
theorem Real.one_sub_pos_of_le_half
    {x : ℝ}
    (hx : x ≤ (1 / 2 : ℝ)) :
    0 < 1 - x := by
  have hhalf_lt_one : (1 / 2 : ℝ) < 1 :=
    one_half_lt_one
  have hx_lt_one : x < 1 :=
    lt_of_le_of_lt hx hhalf_lt_one
  exact sub_pos.mpr hx_lt_one

/-- A number bounded by `1 / 2` leaves at least `1 / 2` distance from `1`. -/
theorem Real.half_le_one_sub_of_le_half
    {x : ℝ}
    (hx : x ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ 1 - x := by
  have hsum_right : x + (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) :=
    add_le_add_right hx (1 / 2 : ℝ)
  have hhalf_sum : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 :=
    add_halves (1 : ℝ)
  have hx_plus : x + (1 / 2 : ℝ) ≤ 1 :=
    hsum_right.trans_eq hhalf_sum
  have hsum_le_one : (1 / 2 : ℝ) + x ≤ 1 :=
    Eq.trans_le (add_comm (1 / 2 : ℝ) x) hx_plus
  exact le_sub_iff_add_le.mpr hsum_le_one

/-- Inverse form of the endpoint Taylor denominator bound. -/
theorem Real.inv_one_sub_le_two_of_le_half
    {x : ℝ}
    (hx : x ≤ (1 / 2 : ℝ)) :
    (1 - x)⁻¹ ≤ (2 : ℝ) := by
  have hhalf : (1 / 2 : ℝ) ≤ 1 - x :=
    Real.half_le_one_sub_of_le_half hx
  have hinv : (1 - x)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ :=
    inv_anti₀ one_half_pos hhalf
  have hhalf_inv : ((1 / 2 : ℝ))⁻¹ = (2 : ℝ) :=
    inv_eq_of_mul_eq_one_right
      (by exact div_mul_cancel₀ (1 : ℝ) two_ne_zero)
  exact hhalf_inv ▸ hinv

/-- Cancelling the harmless factor `2 / 2` in the Taylor majorant. -/
theorem Real.mul_two_div_two
    (x : ℝ) :
    x * (2 : ℝ) / (2 : ℝ) = x := by
  exact mul_div_cancel_right₀ x two_ne_zero

/-- Cancelling `(1 / 2) * (2 * x)`. -/
theorem Real.half_mul_two_mul
    (x : ℝ) :
    (1 / 2 : ℝ) * (2 * x) = x := by
  calc
    (1 / 2 : ℝ) * (2 * x) = ((1 / 2 : ℝ) * 2) * x := by
      exact (mul_assoc (1 / 2 : ℝ) 2 x).symm
    _ = 1 * x := by
      exact congrArg (fun y : ℝ => y * x)
        (div_mul_cancel₀ (1 : ℝ) two_ne_zero)
    _ = x :=
      one_mul x

/-- The zero limit scalar expression used in squeeze arguments. -/
theorem Real.mul_zero_add_zero
    (C : ℝ) :
    C * 0 + 0 = 0 := by
  calc
    C * 0 + 0 = 0 + 0 := by
      exact congrArg (fun y : ℝ => y + 0) (mul_zero C)
    _ = 0 :=
      zero_add 0

/-- The complex norm of the real scalar `1 / 2`. -/
theorem Complex.norm_one_div_two :
    ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
  have hnonneg : 0 ≤ (1 / 2 : ℝ) :=
    div_nonneg zero_le_one zero_le_two
  calc
    ‖(1 / 2 : ℂ)‖ = ‖((1 / 2 : ℝ) : ℂ)‖ := by
      exact congrArg norm (Complex.ofReal_div (1 : ℝ) (2 : ℝ)).symm
    _ = ‖(1 / 2 : ℝ)‖ :=
      Complex.norm_real (1 / 2 : ℝ)
    _ = (1 / 2 : ℝ) :=
      Real.norm_of_nonneg hnonneg

/-- Quadratic envelope for the endpoint product numerator. -/
theorem Real.mul_add_half_le_one_add_sq
    {x : ℝ}
    (hx : 0 ≤ x) :
    x * (x + (1 / 2 : ℝ)) ≤ (1 + x) ^ 2 := by
  have hhalf_le_one : (1 / 2 : ℝ) ≤ 1 := by
    have hone_le_two : (1 : ℝ) ≤ 2 :=
      one_le_two
    calc
      (1 / 2 : ℝ) ≤ 1 / (1 : ℝ) :=
        one_div_le_one_div_of_le zero_lt_one hone_le_two
      _ = 1 := one_div_one
  have hadd : x + (1 / 2 : ℝ) ≤ x + 1 :=
    add_le_add_left hhalf_le_one x
  have hleft : x * (x + (1 / 2 : ℝ)) ≤ x * (x + 1) :=
    mul_le_mul_of_nonneg_left hadd hx
  have hx_le_one_add : x ≤ 1 + x :=
    le_add_of_nonneg_left zero_le_one
  have hx_add_one_nonneg : 0 ≤ x + 1 :=
    add_nonneg hx zero_le_one
  have hmiddle : x * (x + 1) ≤ (1 + x) * (x + 1) :=
    mul_le_mul_of_nonneg_right hx_le_one_add hx_add_one_nonneg
  have hright : (1 + x) * (x + 1) = (1 + x) ^ 2 := by
    calc
      (1 + x) * (x + 1) = (1 + x) * (1 + x) := by
        exact congrArg (fun y : ℝ => (1 + x) * y) (add_comm x 1)
      _ = (1 + x) ^ 2 := by
        exact (pow_two (1 + x)).symm
  calc
    x * (x + (1 / 2 : ℝ)) ≤ x * (x + 1) := hleft
    _ ≤ (1 + x) * (x + 1) := hmiddle
    _ = (1 + x) ^ 2 := hright

/-- Large endpoint control implies the small-variable half-disk condition. -/
theorem Real.le_half_mul_of_two_mul_one_add_le
    {x M : ℝ}
    (_hx : 0 ≤ x)
    (hlarge : 2 * (1 + x) ≤ M) :
    x ≤ (1 / 2 : ℝ) * M := by
  have htwo_nonneg : (0 : ℝ) ≤ 2 :=
    zero_le_two
  have hdiv :
      (2 * (1 + x)) / (2 : ℝ) ≤ M / (2 : ℝ) :=
    div_le_div_of_nonneg_right hlarge htwo_nonneg
  have hleft :
      (2 * (1 + x)) / (2 : ℝ) = 1 + x := by
    calc
      (2 * (1 + x)) / (2 : ℝ) = ((1 + x) * 2) / (2 : ℝ) := by
        exact congrArg (fun y : ℝ => y / (2 : ℝ))
          (mul_comm (2 : ℝ) (1 + x))
      _ = 1 + x :=
        mul_div_cancel_right₀ (1 + x) two_ne_zero
  have hright :
      M / (2 : ℝ) = (1 / 2 : ℝ) * M := by
    calc
      M / (2 : ℝ) = M * (2 : ℝ)⁻¹ := div_eq_mul_inv M (2 : ℝ)
      _ = (2 : ℝ)⁻¹ * M := mul_comm M (2 : ℝ)⁻¹
      _ = (1 / 2 : ℝ) * M := by
        exact congrArg (fun y : ℝ => y * M) (inv_eq_one_div (2 : ℝ))
  have hone_add_le : 1 + x ≤ (1 / 2 : ℝ) * M := by
    calc
      1 + x = (2 * (1 + x)) / (2 : ℝ) := hleft.symm
      _ ≤ M / (2 : ℝ) := hdiv
      _ = (1 / 2 : ℝ) * M := hright
  have hx_le_one_add : x ≤ 1 + x :=
    le_add_of_nonneg_left zero_le_one
  exact le_trans hx_le_one_add hone_add_le

/-- The scalar identity `2 + 1 = 3` over the reals, without arithmetic automation. -/
theorem Real.two_add_one_eq_three_asymptotics :
    (2 : ℝ) + 1 = 3 := by
  have htwo : ((2 : ℕ) : ℝ) = 2 :=
    Nat.cast_ofNat
  have hone : ((1 : ℕ) : ℝ) = 1 :=
    Nat.cast_one
  calc
    (2 : ℝ) + 1 = ((2 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) := by
      exact (congrArg₂ HAdd.hAdd htwo hone).symm
    _ = ((2 + 1 : ℕ) : ℝ) :=
      (Nat.cast_add 2 1).symm
    _ = (3 : ℝ) :=
      Nat.cast_ofNat

/-- The scalar inequality `1 / 2 ≤ 1` over the reals. -/
theorem Real.one_half_le_one_asymptotics :
    (1 / 2 : ℝ) ≤ 1 := by
  have hone_le_two : (1 : ℝ) ≤ 2 :=
    one_le_two
  calc
    (1 / 2 : ℝ) ≤ 1 / (1 : ℝ) :=
      one_div_le_one_div_of_le zero_lt_one hone_le_two
    _ = 1 := one_div_one

/-- The scalar inequality `2 ≤ 3` over the reals. -/
theorem Real.two_le_three_asymptotics :
    (2 : ℝ) ≤ 3 := by
  have hthree_eq : (2 : ℝ) + 1 = 3 :=
    Real.two_add_one_eq_three_asymptotics
  calc
    (2 : ℝ) ≤ 2 + 1 :=
      le_add_of_nonneg_right zero_le_one
    _ = 3 := hthree_eq

/-- The scalar inequality `2 ≤ 4` over the reals. -/
theorem Real.two_le_four :
    (2 : ℝ) ≤ 4 := by
  have htwo_nonneg : (0 : ℝ) ≤ 2 :=
    zero_le_two
  have hfour_eq : (2 : ℝ) + 2 = 4 := by
    have htwo : ((2 : ℕ) : ℝ) = 2 :=
      Nat.cast_ofNat
    have hfour : ((4 : ℕ) : ℝ) = 4 :=
      Nat.cast_ofNat
    calc
      (2 : ℝ) + 2 = ((2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) := by
        exact (congrArg₂ HAdd.hAdd htwo htwo).symm
      _ = ((2 + 2 : ℕ) : ℝ) :=
        (Nat.cast_add 2 2).symm
      _ = (4 : ℝ) :=
        hfour
  calc
    (2 : ℝ) ≤ 2 + 2 :=
      le_add_of_nonneg_right htwo_nonneg
    _ = 4 :=
      hfour_eq

/-- The scalar inequality `4 ≤ 8` over the reals. -/
theorem Real.four_le_eight :
    (4 : ℝ) ≤ 8 := by
  have hfour_nonneg : (0 : ℝ) ≤ 4 :=
    le_trans zero_le_two Real.two_le_four
  have height_eq : (4 : ℝ) + 4 = 8 := by
    have hfour : ((4 : ℕ) : ℝ) = 4 :=
      Nat.cast_ofNat
    have height : ((8 : ℕ) : ℝ) = 8 :=
      Nat.cast_ofNat
    calc
      (4 : ℝ) + 4 = ((4 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) := by
        exact (congrArg₂ HAdd.hAdd hfour hfour).symm
      _ = ((4 + 4 : ℕ) : ℝ) :=
        (Nat.cast_add 4 4).symm
      _ = (8 : ℝ) :=
        height
  calc
    (4 : ℝ) ≤ 4 + 4 :=
      le_add_of_nonneg_right hfour_nonneg
    _ = 8 :=
      height_eq

/-- If `1 ≤ a`, then `2 ≤ 4 * a`. -/
theorem Real.two_le_four_mul_of_one_le
    {a : ℝ}
    (ha : 1 ≤ a) :
    (2 : ℝ) ≤ 4 * a := by
  have hfour_nonneg : (0 : ℝ) ≤ 4 :=
    le_trans zero_le_two Real.two_le_four
  have hfour_le_four_mul : (4 : ℝ) ≤ 4 * a := by
    calc
      (4 : ℝ) = 4 * 1 := (mul_one 4).symm
      _ ≤ 4 * a :=
        mul_le_mul_of_nonneg_left ha hfour_nonneg
  exact le_trans Real.two_le_four hfour_le_four_mul

/-- If `1 ≤ a`, then `4a ≤ 8a²`. -/
theorem Real.four_mul_le_eight_mul_sq_of_one_le
    {a : ℝ}
    (ha : 1 ≤ a) :
    4 * a ≤ 8 * a ^ 2 := by
  have ha_nonneg : 0 ≤ a :=
    le_trans zero_le_one ha
  have hfour_nonneg : (0 : ℝ) ≤ 4 :=
    le_trans zero_le_two Real.two_le_four
  have hfirst : 4 * a ≤ 4 * a ^ 2 := by
    have ha_le_sq : a ≤ a ^ 2 := by
      calc
        a = a * 1 := (mul_one a).symm
        _ ≤ a * a :=
          mul_le_mul_of_nonneg_left ha ha_nonneg
        _ = a ^ 2 := by
          exact (pow_two a).symm
    exact mul_le_mul_of_nonneg_left ha_le_sq hfour_nonneg
  have hsecond : 4 * a ^ 2 ≤ 8 * a ^ 2 :=
    mul_le_mul_of_nonneg_right Real.four_le_eight (sq_nonneg a)
  exact le_trans hfirst hsecond

/-- A number at least one has square bounded by cube. -/
theorem Real.square_le_cube_of_one_le
    {a : ℝ}
    (ha : 1 ≤ a) :
    a ^ 2 ≤ a ^ 3 := by
  have ha_nonneg : 0 ≤ a :=
    le_trans zero_le_one ha
  calc
    a ^ 2 = a ^ 2 * 1 := (mul_one (a ^ 2)).symm
    _ ≤ a ^ 2 * a :=
      mul_le_mul_of_nonneg_left ha (sq_nonneg a)
    _ = a ^ 3 := by
      exact (pow_succ a 2).symm

/-- The scalar identity `1 + 3 = 4` over the reals. -/
theorem Real.one_add_three_eq_four :
    (1 : ℝ) + 3 = 4 := by
  have hone : ((1 : ℕ) : ℝ) = 1 :=
    Nat.cast_one
  have hthree : ((3 : ℕ) : ℝ) = 3 :=
    Nat.cast_ofNat
  have hfour : ((4 : ℕ) : ℝ) = 4 :=
    Nat.cast_ofNat
  calc
    (1 : ℝ) + 3 = ((1 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) := by
      exact (congrArg₂ HAdd.hAdd hone hthree).symm
    _ = ((1 + 3 : ℕ) : ℝ) :=
      (Nat.cast_add 1 3).symm
    _ = (4 : ℝ) :=
      hfour

/-- Collect `x + 3x` as `4x`. -/
theorem Real.add_three_mul_eq_four_mul
    (x : ℝ) :
    x + 3 * x = 4 * x := by
  calc
    x + 3 * x = 1 * x + 3 * x := by
      exact congrArg (fun y : ℝ => y + 3 * x) (one_mul x).symm
    _ = ((1 : ℝ) + 3) * x :=
      (add_mul 1 3 x).symm
    _ = 4 * x := by
      exact congrArg (fun y : ℝ => y * x) Real.one_add_three_eq_four

/-- Summing endpoint majorant pieces after the square-cube comparison. -/
theorem Real.endpoint_square_cube_sum_le_four_cube
    {a M : ℝ}
    (hM_nonneg : 0 ≤ M)
    (ha : 1 ≤ a) :
    a ^ 2 / M + 3 * a ^ 3 / M ≤ 4 * a ^ 3 / M := by
  have hsquare_le_cube : a ^ 2 ≤ a ^ 3 :=
    Real.square_le_cube_of_one_le ha
  have hdiv : a ^ 2 / M ≤ a ^ 3 / M :=
    div_le_div_of_nonneg_right hsquare_le_cube hM_nonneg
  calc
    a ^ 2 / M + 3 * a ^ 3 / M ≤
        a ^ 3 / M + 3 * a ^ 3 / M := by
      exact add_le_add_right hdiv (3 * a ^ 3 / M)
    _ = a ^ 3 / M + 3 * (a ^ 3 / M) := by
      exact congrArg (fun x : ℝ => a ^ 3 / M + x)
        (mul_div_assoc 3 (a ^ 3) M)
    _ = 4 * (a ^ 3 / M) :=
      Real.add_three_mul_eq_four_mul (a ^ 3 / M)
    _ = 4 * a ^ 3 / M := by
      exact (mul_div_assoc 4 (a ^ 3) M).symm

/-- The scalar identity `(1 + 1 / 2) * 2 = 3` over the reals. -/
theorem Real.one_add_half_mul_two_eq_three :
    (1 + (1 / 2 : ℝ)) * 2 = 3 := by
  calc
    (1 + (1 / 2 : ℝ)) * 2 =
        1 * 2 + (1 / 2 : ℝ) * 2 := by
      exact add_mul 1 (1 / 2 : ℝ) 2
    _ = 2 + (1 / 2 : ℝ) * 2 := by
      exact congrArg
        (fun y : ℝ => y + (1 / 2 : ℝ) * 2)
        (one_mul 2)
    _ = 2 + 1 := by
      exact congrArg
        (fun y : ℝ => 2 + y)
        (div_mul_cancel₀ (1 : ℝ) two_ne_zero)
    _ = 3 :=
      Real.two_add_one_eq_three

/-- The real identity `3 / 2 = 1 + 1 / 2`. -/
theorem Real.three_div_two_eq_one_add_half :
    ((3 : ℝ) / 2) = 1 + (1 / 2 : ℝ) := by
  exact
    (div_eq_iff two_ne_zero).mpr
      Real.one_add_half_mul_two_eq_three.symm

/-- Rewriting `(3 / 2) * M` as `M + (1 / 2) * M`. -/
theorem Real.three_div_two_mul
    (M : ℝ) :
    ((3 : ℝ) / 2) * M = M + (1 / 2 : ℝ) * M := by
  calc
    ((3 : ℝ) / 2) * M = (1 + (1 / 2 : ℝ)) * M := by
      exact congrArg (fun y : ℝ => y * M)
        Real.three_div_two_eq_one_add_half
    _ = 1 * M + (1 / 2 : ℝ) * M := by
      exact add_mul 1 (1 / 2 : ℝ) M
    _ = M + (1 / 2 : ℝ) * M := by
      exact congrArg
        (fun y : ℝ => y + (1 / 2 : ℝ) * M)
        (one_mul M)

/-- Endpoint norm scalar bound used in the large endpoint estimate. -/
theorem Real.endpoint_add_half_le_three_halves
    {x M : ℝ}
    (_hx : 0 ≤ x)
    (hlarge : 2 * (1 + x) ≤ M) :
    x + M + (1 / 2 : ℝ) ≤ (3 / 2 : ℝ) * M := by
  have hone_add_le_halfM : 1 + x ≤ (1 / 2 : ℝ) * M := by
    have htwo_nonneg : (0 : ℝ) ≤ 2 :=
      zero_le_two
    have hdiv :
        (2 * (1 + x)) / (2 : ℝ) ≤ M / (2 : ℝ) :=
      div_le_div_of_nonneg_right hlarge htwo_nonneg
    have hleft :
        (2 * (1 + x)) / (2 : ℝ) = 1 + x := by
      calc
        (2 * (1 + x)) / (2 : ℝ) = ((1 + x) * 2) / (2 : ℝ) := by
          exact congrArg (fun y : ℝ => y / (2 : ℝ))
            (mul_comm (2 : ℝ) (1 + x))
        _ = 1 + x :=
          mul_div_cancel_right₀ (1 + x) two_ne_zero
    have hright :
        M / (2 : ℝ) = (1 / 2 : ℝ) * M := by
      calc
        M / (2 : ℝ) = M * (2 : ℝ)⁻¹ := div_eq_mul_inv M (2 : ℝ)
        _ = (2 : ℝ)⁻¹ * M := mul_comm M (2 : ℝ)⁻¹
        _ = (1 / 2 : ℝ) * M := by
          exact congrArg (fun y : ℝ => y * M) (inv_eq_one_div (2 : ℝ))
    calc
      1 + x = (2 * (1 + x)) / (2 : ℝ) := hleft.symm
      _ ≤ M / (2 : ℝ) := hdiv
      _ = (1 / 2 : ℝ) * M := hright
  have hx_half_le : x + (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) * M := by
    have hhalf_le_one : (1 / 2 : ℝ) ≤ 1 :=
      Real.one_half_le_one_asymptotics
    have hadd : x + (1 / 2 : ℝ) ≤ x + 1 :=
      add_le_add_left hhalf_le_one x
    have hcomm : x + 1 = 1 + x :=
      add_comm x 1
    exact le_trans hadd (hcomm ▸ hone_add_le_halfM)
  calc
    x + M + (1 / 2 : ℝ) = M + (x + (1 / 2 : ℝ)) := by
      calc
        x + M + (1 / 2 : ℝ) = (x + M) + (1 / 2 : ℝ) := rfl
        _ = (M + x) + (1 / 2 : ℝ) := by
          exact congrArg (fun y : ℝ => y + (1 / 2 : ℝ))
            (add_comm x M)
        _ = M + (x + (1 / 2 : ℝ)) := add_assoc M x (1 / 2 : ℝ)
    _ ≤ M + (1 / 2 : ℝ) * M :=
      add_le_add_left hx_half_le M
    _ = (3 / 2 : ℝ) * M :=
      (Real.three_div_two_mul M).symm

/-- Multiplication reassociation used to expose the denominator cancellation in
the endpoint Taylor second term. -/
theorem Real.endpoint_denominator_mul_reassociate
    (a M r : ℝ) :
    (a * M) * ((r * M⁻¹) * (r * M⁻¹)) =
      a * ((M * M⁻¹) * (r * (r * M⁻¹))) := by
  calc
    (a * M) * ((r * M⁻¹) * (r * M⁻¹)) =
        a * (M * ((r * M⁻¹) * (r * M⁻¹))) :=
      mul_assoc a M ((r * M⁻¹) * (r * M⁻¹))
    _ = a * ((M * (r * M⁻¹)) * (r * M⁻¹)) := by
      exact congrArg (fun x : ℝ => a * x)
        (mul_assoc M (r * M⁻¹) (r * M⁻¹)).symm
    _ = a * (((M * r) * M⁻¹) * (r * M⁻¹)) := by
      exact congrArg
        (fun x : ℝ => a * (x * (r * M⁻¹)))
        (mul_assoc M r M⁻¹).symm
    _ = a * (((r * M) * M⁻¹) * (r * M⁻¹)) := by
      exact congrArg
        (fun x : ℝ => a * ((x * M⁻¹) * (r * M⁻¹)))
        (mul_comm M r)
    _ = a * ((r * (M * M⁻¹)) * (r * M⁻¹)) := by
      exact congrArg
        (fun x : ℝ => a * (x * (r * M⁻¹)))
        (mul_assoc r M M⁻¹)
    _ = a * (((M * M⁻¹) * r) * (r * M⁻¹)) := by
      exact congrArg
        (fun x : ℝ => a * (x * (r * M⁻¹)))
        (mul_comm r (M * M⁻¹))
    _ = a * ((M * M⁻¹) * (r * (r * M⁻¹))) := by
      exact congrArg (fun x : ℝ => a * x)
        (mul_assoc (M * M⁻¹) r (r * M⁻¹))

/-- Scalar denominator normalization for the endpoint Taylor second term. -/
theorem Real.endpoint_second_term_le_cubic_over_endpoint
    {r M : ℝ}
    (hMpos : 0 < M)
    (hr_nonneg : 0 ≤ r) :
    ((3 / 2 : ℝ) * M) * ((r / M) ^ 2) ≤
      3 * (1 + r) ^ 3 / M := by
  have hM_nonneg : 0 ≤ M := hMpos.le
  have hleft_eq :
      ((3 / 2 : ℝ) * M) * ((r / M) ^ 2) =
        ((3 / 2 : ℝ) * r ^ 2) / M := by
    have hM_ne : M ≠ 0 := hMpos.ne'
    calc
      ((3 / 2 : ℝ) * M) * ((r / M) ^ 2) =
          ((3 / 2 : ℝ) * M) * ((r / M) * (r / M)) := by
        exact congrArg (fun x : ℝ => ((3 / 2 : ℝ) * M) * x)
          (pow_two (r / M))
      _ = ((3 / 2 : ℝ) * M) * ((r * M⁻¹) * (r * M⁻¹)) := by
        exact congrArg
          (fun x : ℝ => ((3 / 2 : ℝ) * M) * (x * x))
          (div_eq_mul_inv r M)
      _ = (3 / 2 : ℝ) * ((M * M⁻¹) * (r * (r * M⁻¹))) := by
        exact Real.endpoint_denominator_mul_reassociate (3 / 2 : ℝ) M r
      _ = (3 / 2 : ℝ) * (1 * (r * (r * M⁻¹))) := by
        exact congrArg
          (fun x : ℝ => (3 / 2 : ℝ) * (x * (r * (r * M⁻¹))))
          (mul_inv_cancel₀ hM_ne)
      _ = (3 / 2 : ℝ) * (r * (r * M⁻¹)) := by
        exact congrArg (fun x : ℝ => (3 / 2 : ℝ) * x)
          (one_mul (r * (r * M⁻¹)))
      _ = (3 / 2 : ℝ) * ((r * r) * M⁻¹) := by
        exact congrArg (fun x : ℝ => (3 / 2 : ℝ) * x)
          (mul_assoc r r M⁻¹).symm
      _ = (3 / 2 : ℝ) * (r ^ 2 * M⁻¹) := by
        exact congrArg (fun x : ℝ => (3 / 2 : ℝ) * (x * M⁻¹))
          (pow_two r).symm
      _ = ((3 / 2 : ℝ) * r ^ 2) * M⁻¹ :=
        (mul_assoc (3 / 2 : ℝ) (r ^ 2) M⁻¹).symm
      _ = ((3 / 2 : ℝ) * r ^ 2) / M :=
        (div_eq_mul_inv ((3 / 2 : ℝ) * r ^ 2) M).symm
  have hcoef_le : (3 / 2 : ℝ) ≤ 3 := by
    calc
      (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) :=
        Real.three_div_two_eq_one_add_half
      _ ≤ 1 + 1 :=
        add_le_add_left Real.one_half_le_one_asymptotics 1
      _ = (2 : ℝ) := by
        exact one_add_one_eq_two
      _ ≤ 3 := by
        exact Real.two_le_three_asymptotics
  have hcoef :
      (3 / 2 : ℝ) * r ^ 2 ≤ 3 * r ^ 2 := by
    exact mul_le_mul_of_nonneg_right hcoef_le (sq_nonneg r)
  have hone_add_nonneg : 0 ≤ 1 + r :=
    add_nonneg zero_le_one hr_nonneg
  have habs_bound : |r| ≤ 1 + r := by
    exact abs_le.mpr
      ⟨le_trans (neg_nonpos.mpr hone_add_nonneg) hr_nonneg,
        le_add_of_nonneg_left zero_le_one⟩
  have hsquare_le_one_add_square :
      r ^ 2 ≤ (1 + r) ^ 2 := by
    have hone_abs : |1 + r| = 1 + r :=
      abs_of_nonneg hone_add_nonneg
    exact sq_le_sq.mpr (hone_abs.symm ▸ habs_bound)
  have hone_le : 1 ≤ 1 + r :=
    le_add_of_nonneg_right hr_nonneg
  have hsquare_le_cube :
      r ^ 2 ≤ (1 + r) ^ 3 :=
    le_trans hsquare_le_one_add_square
      (Real.square_le_cube_of_one_le hone_le)
  have hthree_nonneg : (0 : ℝ) ≤ 3 :=
    le_trans zero_le_two Real.two_le_three_asymptotics
  calc
    ((3 / 2 : ℝ) * M) * ((r / M) ^ 2) =
        ((3 / 2 : ℝ) * r ^ 2) / M := hleft_eq
    _ ≤ (3 * r ^ 2) / M :=
      div_le_div_of_nonneg_right hcoef hM_nonneg
    _ ≤ (3 * (1 + r) ^ 3) / M := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsquare_le_cube hthree_nonneg)
        hM_nonneg
    _ = 3 * (1 + r) ^ 3 / M :=
      rfl

/-- Subtracting the shared first two summands leaves the third summand. -/
theorem Complex.add_add_sub_add_eq_right
    (a b c : ℂ) :
    (a + b + c) - (a + b) = c := by
  calc
    (a + b + c) - (a + b) = ((a + b) + c) - (a + b) := rfl
    _ = c :=
      add_sub_cancel_left (a + b) c

/-- Triangle estimate for a difference of two negated complex terms. -/
theorem Complex.norm_neg_sub_le_add_norm
    (a b : ℂ) :
    ‖-a - b‖ ≤ ‖a‖ + ‖b‖ := by
  calc
    ‖-a - b‖ = ‖(-a) + (-b)‖ := by
      exact congrArg norm (sub_eq_add_neg (-a) b)
    _ ≤ ‖-a‖ + ‖-b‖ :=
      norm_add_le (-a) (-b)
    _ = ‖a‖ + ‖-b‖ := by
      exact congrArg (fun r : ℝ => r + ‖-b‖) (norm_neg a)
    _ = ‖a‖ + ‖b‖ := by
      exact congrArg (fun r : ℝ => ‖a‖ + r) (norm_neg b)

/-- The real part of a real multiple of `I` is zero. -/
theorem Complex.real_cast_mul_I_re
    (s : ℝ) :
    ((s : ℂ) * Complex.I).re = 0 := by
  calc
    ((s : ℂ) * Complex.I).re =
        (s : ℂ).re * Complex.I.re - (s : ℂ).im * Complex.I.im := by
      exact Complex.mul_re (s : ℂ) Complex.I
    _ = s * Complex.I.re - (s : ℂ).im * Complex.I.im := by
      exact congrArg
        (fun r : ℝ => r * Complex.I.re - (s : ℂ).im * Complex.I.im)
        (Complex.ofReal_re s)
    _ = s * 0 - (s : ℂ).im * Complex.I.im := by
      exact congrArg
        (fun r : ℝ => s * r - (s : ℂ).im * Complex.I.im)
        Complex.I_re
    _ = s * 0 - 0 * Complex.I.im := by
      exact congrArg
        (fun r : ℝ => s * 0 - r * Complex.I.im)
        (Complex.ofReal_im s)
    _ = s * 0 - 0 * 1 := by
      exact congrArg
        (fun r : ℝ => s * 0 - 0 * r)
        Complex.I_im
    _ = 0 - 0 * 1 := by
      exact congrArg (fun r : ℝ => r - 0 * 1) (mul_zero s)
    _ = 0 - 0 := by
      exact congrArg (fun r : ℝ => 0 - r) (zero_mul (1 : ℝ))
    _ = 0 :=
      sub_self 0

/-- Replace a final zero summand after proving it is zero. -/
theorem Real.add_right_zero_after_eq_zero
    (a b c : ℝ)
    (h : c = 0) :
    a + b + c = a + b := by
  calc
    a + b + c = a + b + 0 := by
      exact congrArg (fun r : ℝ => a + b + r) h
    _ = a + b :=
      add_zero (a + b)

/-- Norm of `I / z` expressed as the inverse norm of `z`. -/
theorem Complex.norm_I_div_eq_inv_norm
    (z : ℂ) :
    ‖Complex.I‖ / ‖z‖ = ‖z‖⁻¹ := by
  calc
    ‖Complex.I‖ / ‖z‖ = (1 : ℝ) / ‖z‖ := by
      exact congrArg (fun r : ℝ => r / ‖z‖) Complex.norm_I
    _ = ‖z‖⁻¹ :=
      (inv_eq_one_div ‖z‖).symm

/-- Coercing a real negative before multiplying by `I`. -/
theorem Complex.ofReal_neg_mul_I
    (t : ℝ) :
    ((-t : ℝ) : ℂ) * Complex.I = -((t : ℂ) * Complex.I) := by
  calc
    ((-t : ℝ) : ℂ) * Complex.I = (-(t : ℂ)) * Complex.I := by
      exact congrArg (fun z : ℂ => z * Complex.I) (Complex.ofReal_neg t)
    _ = -((t : ℂ) * Complex.I) :=
      neg_mul (t : ℂ) Complex.I

/-- Normalize `t - (-t)` to `2 * t`. -/
theorem Real.sub_neg_eq_two_mul
    (t : ℝ) :
    t - (-t) = 2 * t := by
  calc
    t - (-t) = t + t :=
      sub_neg_eq_add t t
    _ = (1 : ℝ) * t + 1 * t := by
      exact congrArg₂ HAdd.hAdd (one_mul t).symm (one_mul t).symm
    _ = ((1 : ℝ) + 1) * t :=
      (add_mul 1 1 t).symm
    _ = 2 * t := by
      exact congrArg (fun r : ℝ => r * t) one_add_one_eq_two

/-- Move the denominator of `(2 * t) / d` into the coefficient of `t`. -/
theorem Real.two_mul_div_eq_div_mul
    (t d : ℝ) :
    (2 * t) / d = ((2 : ℝ) / d) * t := by
  calc
    (2 * t) / d = (2 * t) * d⁻¹ := div_eq_mul_inv (2 * t) d
    _ = 2 * (t * d⁻¹) := mul_assoc 2 t d⁻¹
    _ = 2 * (d⁻¹ * t) := by
      exact congrArg (fun y : ℝ => 2 * y) (mul_comm t d⁻¹)
    _ = (2 * d⁻¹) * t := (mul_assoc 2 d⁻¹ t).symm
    _ = ((2 : ℝ) / d) * t := by
      exact congrArg (fun y : ℝ => y * t) (div_eq_mul_inv 2 d).symm

/-- Move a denominator inside the second factor. -/
theorem Real.mul_mul_div_eq_mul_div
    (A t d : ℝ) :
    (A * t) / d = A * (t / d) :=
  mul_div_assoc A t d

/-- Reassociate `2 * (C * K)` as `(2 * C) * K`. -/
theorem Real.two_mul_assoc
    (C K : ℝ) :
    2 * (C * K) = (2 * C) * K :=
  (mul_assoc 2 C K).symm

/-- The norm of the complex natural `2`, in nat-cast normal form. -/
theorem Complex.norm_two_natCast :
    ‖(2 : ℂ)‖ = (2 : ℝ) :=
  Complex.norm_natCast 2

end

end LFunctions
end Boundary
