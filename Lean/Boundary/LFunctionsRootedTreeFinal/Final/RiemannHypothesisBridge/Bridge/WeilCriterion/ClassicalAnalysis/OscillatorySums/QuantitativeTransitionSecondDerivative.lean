import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionDenominator

/-!
# Explicit second derivative of the smooth transition

The first derivative is normalized as `N / D²`, where
`N = g'(x)g(1-x) + g(x)g'(1-x)` and `D = g(x)+g(1-x)`.
This owner differentiates `N` and `D` separately and assembles the quotient
derivative.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.expNegInvGlueGlobalSecondDerivative
    (x : ℝ) : ℝ :=
  deriv Real.expNegInvGlueDerivative x

def Real.smoothTransitionDerivativeNumerator
    (x : ℝ) : ℝ :=
  Real.expNegInvGlueDerivative x * expNegInvGlue (1 - x) +
    expNegInvGlue x * Real.expNegInvGlueDerivative (1 - x)

def Real.smoothTransitionDerivativeDenominator
    (x : ℝ) : ℝ :=
  expNegInvGlue x + expNegInvGlue (1 - x)

def Real.smoothTransitionDerivativeNumeratorDerivative
    (x : ℝ) : ℝ :=
  Real.expNegInvGlueGlobalSecondDerivative x * expNegInvGlue (1 - x) -
    expNegInvGlue x *
      Real.expNegInvGlueGlobalSecondDerivative (1 - x)

def Real.smoothTransitionDerivativeDenominatorDerivative
    (x : ℝ) : ℝ :=
  Real.expNegInvGlueDerivative x -
    Real.expNegInvGlueDerivative (1 - x)

def Real.smoothTransitionSecondDerivative
    (x : ℝ) : ℝ :=
  (Real.smoothTransitionDerivativeNumeratorDerivative x *
      Real.smoothTransitionDerivativeDenominator x ^ 2 -
    Real.smoothTransitionDerivativeNumerator x *
      (2 * Real.smoothTransitionDerivativeDenominator x *
        Real.smoothTransitionDerivativeDenominatorDerivative x)) /
    (Real.smoothTransitionDerivativeDenominator x ^ 2) ^ 2

theorem Real.transitionSecondDerivative_natCast_add
    (a b c : ℕ)
    (hvalue : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  (Nat.cast_add a b).symm.trans
    (congrArg (fun value : ℕ => (value : ℝ)) hvalue)

theorem Real.transitionSecondDerivative_natCast_mul
    (a b c : ℕ)
    (hvalue : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  (Nat.cast_mul a b).symm.trans
    (congrArg (fun value : ℕ => (value : ℝ)) hvalue)

theorem Real.transitionSecondDerivative_cross_cancel
    (first cross last : ℝ) :
    first + (-cross) + (cross + (-last)) = first - last := by
  calc
    first + (-cross) + (cross + (-last)) =
        first + ((-cross + cross) + (-last)) :=
      (add_assoc first (-cross) (cross + (-last))).trans
        (congrArg (fun value : ℝ => first + value)
          (add_assoc (-cross) cross (-last)).symm)
    _ = first + (0 + (-last)) :=
      congrArg (fun value : ℝ => first + (value + (-last)))
        (neg_add_cancel cross)
    _ = first + (-last) :=
      congrArg (fun value : ℝ => first + value) (zero_add (-last))
    _ = first - last := (sub_eq_add_neg first last).symm

theorem Real.contDiff_expNegInvGlueDerivative :
    ContDiff ℝ (⊤ : ℕ∞) Real.expNegInvGlueDerivative := by
  have hglue : ContDiff ℝ (⊤ : ℕ∞) expNegInvGlue := expNegInvGlue.contDiff
  have hderivative : ContDiff ℝ (⊤ : ℕ∞) (deriv expNegInvGlue) :=
    (contDiff_infty_iff_deriv.mp hglue).2
  have hfunction : deriv expNegInvGlue = Real.expNegInvGlueDerivative := by
    funext x
    exact Real.deriv_expNegInvGlue_exact x
  exact Eq.subst
    (motive := fun function : ℝ → ℝ => ContDiff ℝ (⊤ : ℕ∞) function)
    hfunction hderivative

theorem Real.hasDerivAt_expNegInvGlueDerivative_global
    (x : ℝ) :
    HasDerivAt
      Real.expNegInvGlueDerivative
      (Real.expNegInvGlueGlobalSecondDerivative x)
      x := by
  have honeTop :
      (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  have hdifferentiable :
      Differentiable ℝ Real.expNegInvGlueDerivative :=
    Real.contDiff_expNegInvGlueDerivative.differentiable honeTop
  unfold Real.expNegInvGlueGlobalSecondDerivative
  exact hdifferentiable.differentiableAt.hasDerivAt

theorem Real.expNegInvGlueGlobalSecondDerivative_eq_explicit_of_pos
    {x : ℝ}
    (hx : 0 < x) :
    Real.expNegInvGlueGlobalSecondDerivative x =
      Real.expNegInvGlueSecondDerivative x := by
  unfold Real.expNegInvGlueGlobalSecondDerivative
  exact
    (Real.hasDerivAt_expNegInvGlueDerivative_positive hx).deriv

theorem Real.expNegInvGlueDerivative_eq_zero_of_neg
    {x : ℝ}
    (hx : x < 0) :
    Real.expNegInvGlueDerivative x = 0 := by
  have hglue : expNegInvGlue x = 0 := expNegInvGlue.zero_of_nonpos hx.le
  exact
    (Real.expNegInvGlueDerivative_eq_inv_sq_mul x).trans
      ((congrArg (fun value : ℝ => x⁻¹ ^ 2 * value) hglue).trans
        (mul_zero (x⁻¹ ^ 2)))

theorem Real.expNegInvGlueGlobalSecondDerivative_eq_zero_of_neg
    {x : ℝ}
    (hx : x < 0) :
    Real.expNegInvGlueGlobalSecondDerivative x = 0 := by
  have heventual : Real.expNegInvGlueDerivative =ᶠ[nhds x]
      (fun _y : ℝ => (0 : ℝ)) := by
    exact Filter.mem_of_superset
      (Iio_mem_nhds hx)
      (fun y hy => Real.expNegInvGlueDerivative_eq_zero_of_neg hy)
  unfold Real.expNegInvGlueGlobalSecondDerivative
  exact heventual.deriv_eq.trans (deriv_const x 0)

theorem Real.expNegInvGlueGlobalSecondDerivative_zero :
    Real.expNegInvGlueGlobalSecondDerivative 0 = 0 := by
  unfold Real.expNegInvGlueGlobalSecondDerivative
  have hderivative :=
    Real.hasDerivAt_expNegInvGlueDerivative_global 0
  have hflat : HasDerivAt Real.expNegInvGlueDerivative 0 0 := by
    have hfunction :
        (fun x : ℝ => Polynomial.eval x⁻¹ (Polynomial.X ^ 2) *
          expNegInvGlue x) =
        (fun x : ℝ => x⁻¹ ^ 2 * expNegInvGlue x) := by
      funext x
      have heval : Polynomial.eval x⁻¹ (Polynomial.X ^ 2) = x⁻¹ ^ 2 :=
        (Polynomial.eval_pow (p := Polynomial.X) (x := x⁻¹) 2).trans
          (congrArg (fun value : ℝ => value ^ 2)
            (Polynomial.eval_X (x := x⁻¹)))
      exact congrArg (fun value : ℝ => value * expNegInvGlue x) heval
    have hraw := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
      (Polynomial.X ^ 2) 0
    have hrawValue :
        Polynomial.eval 0⁻¹
            (Polynomial.X ^ 2 *
              (Polynomial.X ^ 2 - Polynomial.derivative (Polynomial.X ^ 2))) *
            expNegInvGlue 0 = 0 := by
      have hglue : expNegInvGlue 0 = 0 := expNegInvGlue.zero
      exact (congrArg
        (fun value : ℝ =>
          Polynomial.eval 0⁻¹
              (Polynomial.X ^ 2 *
                (Polynomial.X ^ 2 - Polynomial.derivative (Polynomial.X ^ 2))) *
            value)
        hglue).trans (mul_zero _)
    have hrawZero : HasDerivAt
        (fun x : ℝ => Polynomial.eval x⁻¹ (Polynomial.X ^ 2) *
          expNegInvGlue x) 0 0 :=
      Eq.subst
        (motive := fun value : ℝ =>
          HasDerivAt
            (fun x : ℝ => Polynomial.eval x⁻¹ (Polynomial.X ^ 2) *
              expNegInvGlue x) value 0)
        hrawValue hraw
    have hweighted : HasDerivAt
        (fun x : ℝ => x⁻¹ ^ 2 * expNegInvGlue x) 0 0 :=
      Eq.subst
        (motive := fun function : ℝ → ℝ => HasDerivAt function 0 0)
        hfunction hrawZero
    have hderivativeFunction : Real.expNegInvGlueDerivative =
        (fun x : ℝ => x⁻¹ ^ 2 * expNegInvGlue x) := by
      funext x
      exact Real.expNegInvGlueDerivative_eq_inv_sq_mul x
    exact Eq.subst
      (motive := fun function : ℝ → ℝ => HasDerivAt function 0 0)
      hderivativeFunction.symm hweighted
  exact hflat.deriv

theorem Real.abs_expNegInvGlueGlobalSecondDerivative_le_seven_sixty_eight
    (x : ℝ) :
    |Real.expNegInvGlueGlobalSecondDerivative x| ≤ 768 := by
  match lt_trichotomy x 0 with
  | Or.inl hx =>
      exact le_trans
        (le_of_eq
          (congrArg abs
            (Real.expNegInvGlueGlobalSecondDerivative_eq_zero_of_neg hx)))
        (by
          exact le_trans (le_of_eq (abs_zero))
            (Nat.cast_nonneg 768))
  | Or.inr hremaining =>
      match hremaining with
      | Or.inl hx =>
          exact Eq.subst
            (motive := fun value : ℝ =>
              |Real.expNegInvGlueGlobalSecondDerivative value| ≤ 768)
            hx.symm
            (le_trans
              (le_of_eq
                (congrArg abs Real.expNegInvGlueGlobalSecondDerivative_zero))
              (le_trans (le_of_eq abs_zero) (Nat.cast_nonneg 768)))
      | Or.inr hx =>
          exact le_trans
            (le_of_eq
              (congrArg abs
                (Real.expNegInvGlueGlobalSecondDerivative_eq_explicit_of_pos hx)))
            (Real.abs_expNegInvGlueSecondDerivative_le_seven_sixty_eight hx)

theorem Real.hasDerivAt_expNegInvGlue_one_sub_globalSecond
    (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => Real.expNegInvGlueDerivative (1 - y))
      (-Real.expNegInvGlueGlobalSecondDerivative (1 - x))
      x := by
  have houter :=
    Real.hasDerivAt_expNegInvGlueDerivative_global (1 - x)
  have hinner := (hasDerivAt_const x 1).sub (hasDerivAt_id x)
  have hcomposition := houter.comp x hinner
  have hfunction :
      Real.expNegInvGlueDerivative ∘ (fun y : ℝ => 1 - y) =
        (fun y : ℝ => Real.expNegInvGlueDerivative (1 - y)) := rfl
  have hzeroSubOne : (0 : ℝ) - 1 = -1 := zero_sub 1
  have hcoefficient :
      Real.expNegInvGlueGlobalSecondDerivative (1 - x) * (0 - 1) =
        -Real.expNegInvGlueGlobalSecondDerivative (1 - x) :=
    (congrArg
      (fun value : ℝ =>
        Real.expNegInvGlueGlobalSecondDerivative (1 - x) * value)
      hzeroSubOne).trans
      (mul_neg_one (Real.expNegInvGlueGlobalSecondDerivative (1 - x)))
  have hcomposed : HasDerivAt
      (fun y : ℝ => Real.expNegInvGlueDerivative (1 - y))
      (Real.expNegInvGlueGlobalSecondDerivative (1 - x) * (0 - 1)) x :=
    Eq.subst
      (motive := fun function : ℝ → ℝ => HasDerivAt function
        (Real.expNegInvGlueGlobalSecondDerivative (1 - x) * (0 - 1)) x)
      hfunction hcomposition
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt
        (fun y : ℝ => Real.expNegInvGlueDerivative (1 - y))
        value x)
    hcoefficient hcomposed

theorem Real.hasDerivAt_smoothTransitionDerivativeDenominator
    (x : ℝ) :
    HasDerivAt
      Real.smoothTransitionDerivativeDenominator
      (Real.smoothTransitionDerivativeDenominatorDerivative x)
      x := by
  unfold Real.smoothTransitionDerivativeDenominator
  unfold Real.smoothTransitionDerivativeDenominatorDerivative
  exact
    (Real.hasDerivAt_expNegInvGlue_exact x).add
      (Real.hasDerivAt_expNegInvGlue_one_sub x)

theorem Real.hasDerivAt_smoothTransitionDerivativeNumerator
    (x : ℝ) :
    HasDerivAt
      Real.smoothTransitionDerivativeNumerator
      (Real.smoothTransitionDerivativeNumeratorDerivative x)
      x := by
  unfold Real.smoothTransitionDerivativeNumerator
  unfold Real.smoothTransitionDerivativeNumeratorDerivative
  have hdx := Real.hasDerivAt_expNegInvGlueDerivative_global x
  have hgy := Real.hasDerivAt_expNegInvGlue_one_sub x
  have hgx := Real.hasDerivAt_expNegInvGlue_exact x
  have hdy := Real.hasDerivAt_expNegInvGlue_one_sub_globalSecond x
  have hfirst := hdx.mul hgy
  have hsecond := hgx.mul hdy
  have hsum := hfirst.add hsecond
  have hvalue :
      Real.expNegInvGlueGlobalSecondDerivative x * expNegInvGlue (1 - x) +
          Real.expNegInvGlueDerivative x *
            (-Real.expNegInvGlueDerivative (1 - x)) +
        (Real.expNegInvGlueDerivative x *
            Real.expNegInvGlueDerivative (1 - x) +
          expNegInvGlue x *
            (-Real.expNegInvGlueGlobalSecondDerivative (1 - x))) =
        Real.expNegInvGlueGlobalSecondDerivative x * expNegInvGlue (1 - x) -
          expNegInvGlue x *
            Real.expNegInvGlueGlobalSecondDerivative (1 - x) := by
    calc
      Real.expNegInvGlueGlobalSecondDerivative x * expNegInvGlue (1 - x) +
            Real.expNegInvGlueDerivative x *
              (-Real.expNegInvGlueDerivative (1 - x)) +
          (Real.expNegInvGlueDerivative x *
              Real.expNegInvGlueDerivative (1 - x) +
            expNegInvGlue x *
              (-Real.expNegInvGlueGlobalSecondDerivative (1 - x))) =
          Real.expNegInvGlueGlobalSecondDerivative x * expNegInvGlue (1 - x) +
              (-(Real.expNegInvGlueDerivative x *
                Real.expNegInvGlueDerivative (1 - x))) +
            (Real.expNegInvGlueDerivative x *
                Real.expNegInvGlueDerivative (1 - x) +
              (-(expNegInvGlue x *
                Real.expNegInvGlueGlobalSecondDerivative (1 - x)))) :=
        congrArg₂ (fun firstValue secondValue : ℝ => firstValue + secondValue)
          (congrArg
            (fun value : ℝ =>
              Real.expNegInvGlueGlobalSecondDerivative x *
                expNegInvGlue (1 - x) + value)
            (mul_neg _ _))
          (congrArg
            (fun value : ℝ =>
              Real.expNegInvGlueDerivative x *
                Real.expNegInvGlueDerivative (1 - x) + value)
            (mul_neg _ _))
      _ = Real.expNegInvGlueGlobalSecondDerivative x * expNegInvGlue (1 - x) -
            expNegInvGlue x *
              Real.expNegInvGlueGlobalSecondDerivative (1 - x) :=
        Real.transitionSecondDerivative_cross_cancel _ _ _
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt Real.smoothTransitionDerivativeNumerator value x)
    hvalue hsum

theorem Real.smoothTransitionDerivative_eq_normalized
    (x : ℝ) :
    Real.smoothTransitionDerivative x =
      Real.smoothTransitionDerivativeNumerator x /
        Real.smoothTransitionDerivativeDenominator x ^ 2 := by
  unfold Real.smoothTransitionDerivative
  unfold Real.smoothTransitionDerivativeNumerator
  unfold Real.smoothTransitionDerivativeDenominator
  exact congrArg
    (fun numerator : ℝ => numerator /
      (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2)
    (Real.smoothTransitionDerivative_numerator_eq x)

theorem Real.hasDerivAt_smoothTransitionDerivativeDenominator_sq
    (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => Real.smoothTransitionDerivativeDenominator y ^ 2)
      (2 * Real.smoothTransitionDerivativeDenominator x *
        Real.smoothTransitionDerivativeDenominatorDerivative x)
      x := by
  have hdenominator :=
    Real.hasDerivAt_smoothTransitionDerivativeDenominator x
  have hsquare := hdenominator.pow 2
  have hcoefficient :
      (2 : ℝ) * Real.smoothTransitionDerivativeDenominator x ^ (2 - 1) *
          Real.smoothTransitionDerivativeDenominatorDerivative x =
        2 * Real.smoothTransitionDerivativeDenominator x *
          Real.smoothTransitionDerivativeDenominatorDerivative x :=
    congrArg
      (fun value : ℝ =>
        2 * value * Real.smoothTransitionDerivativeDenominatorDerivative x)
      (pow_one (Real.smoothTransitionDerivativeDenominator x))
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt
        (fun y : ℝ => Real.smoothTransitionDerivativeDenominator y ^ 2)
        value x)
    hcoefficient hsquare

theorem Real.hasDerivAt_smoothTransitionDerivative_normalized
    (x : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        Real.smoothTransitionDerivativeNumerator y /
          Real.smoothTransitionDerivativeDenominator y ^ 2)
      (Real.smoothTransitionSecondDerivative x)
      x := by
  have hnumerator :=
    Real.hasDerivAt_smoothTransitionDerivativeNumerator x
  have hdenominator :=
    Real.hasDerivAt_smoothTransitionDerivativeDenominator_sq x
  have hdenominatorNe :
      Real.smoothTransitionDerivativeDenominator x ^ 2 ≠ 0 := by
    unfold Real.smoothTransitionDerivativeDenominator
    exact pow_ne_zero 2
      (ne_of_gt (Real.smoothTransitionDenominator_pos x))
  have hquotient := hnumerator.div hdenominator hdenominatorNe
  exact hquotient

theorem Real.hasDerivAt_smoothTransitionDerivative
    (x : ℝ) :
    HasDerivAt
      Real.smoothTransitionDerivative
      (Real.smoothTransitionSecondDerivative x)
      x := by
  have hfunction :
      Real.smoothTransitionDerivative =
        fun y : ℝ =>
          Real.smoothTransitionDerivativeNumerator y /
            Real.smoothTransitionDerivativeDenominator y ^ 2 := by
    funext y
    exact Real.smoothTransitionDerivative_eq_normalized y
  exact Eq.subst
    (motive := fun function : ℝ → ℝ =>
      HasDerivAt function (Real.smoothTransitionSecondDerivative x) x)
    hfunction.symm
    (Real.hasDerivAt_smoothTransitionDerivative_normalized x)

theorem Real.deriv_smoothTransitionDerivative
    (x : ℝ) :
    deriv Real.smoothTransitionDerivative x =
      Real.smoothTransitionSecondDerivative x :=
  (Real.hasDerivAt_smoothTransitionDerivative x).deriv

theorem Real.expNegInvGlue_le_one
    (x : ℝ) :
    expNegInvGlue x ≤ 1 := by
  match le_or_gt x 0 with
  | Or.inl hx =>
      exact le_trans
        (le_of_eq (expNegInvGlue.zero_of_nonpos hx)) zero_le_one
  | Or.inr hx =>
      have hvalue := Real.expNegInvGlue_eq_exp_neg_inv_of_pos hx
      have hnegative : -x⁻¹ ≤ 0 :=
        neg_nonpos.mpr (inv_nonneg.mpr hx.le)
      have hexp := Real.exp_le_one_iff.mpr hnegative
      exact le_trans (le_of_eq hvalue) hexp

theorem Real.expNegInvGlueDerivative_le_four_global
    (x : ℝ) :
    Real.expNegInvGlueDerivative x ≤ 4 := by
  match lt_trichotomy x 0 with
  | Or.inl hx =>
      exact le_trans
        (le_of_eq (Real.expNegInvGlueDerivative_eq_zero_of_neg hx))
        (Nat.cast_nonneg 4)
  | Or.inr hremaining =>
      match hremaining with
      | Or.inl hx =>
          exact Eq.subst
            (motive := fun value : ℝ =>
              Real.expNegInvGlueDerivative value ≤ 4)
            hx.symm
            (le_trans (le_of_eq Real.expNegInvGlueDerivative_zero)
              (Nat.cast_nonneg 4))
      | Or.inr hx => exact Real.expNegInvGlueDerivative_le_four hx

theorem Real.abs_expNegInvGlueDerivative_le_four
    (x : ℝ) :
    |Real.expNegInvGlueDerivative x| ≤ 4 := by
  have hnonneg := Real.expNegInvGlueDerivative_nonneg x
  exact le_trans (le_of_eq (abs_of_nonneg hnonneg))
    (Real.expNegInvGlueDerivative_le_four_global x)

theorem Real.abs_smoothTransitionDerivativeNumerator_le_eight
    (x : ℝ) :
    |Real.smoothTransitionDerivativeNumerator x| ≤ 8 := by
  unfold Real.smoothTransitionDerivativeNumerator
  have htriangle := abs_add
    (Real.expNegInvGlueDerivative x * expNegInvGlue (1 - x))
    (expNegInvGlue x * Real.expNegInvGlueDerivative (1 - x))
  have hfirst :
      |Real.expNegInvGlueDerivative x * expNegInvGlue (1 - x)| ≤ 4 := by
    have hproduct := abs_mul
      (Real.expNegInvGlueDerivative x) (expNegInvGlue (1 - x))
    have hglueAbs : |expNegInvGlue (1 - x)| ≤ 1 := by
      exact le_trans
        (le_of_eq (abs_of_nonneg (expNegInvGlue.nonneg (1 - x))))
        (Real.expNegInvGlue_le_one (1 - x))
    exact le_trans (le_of_eq hproduct)
      (le_trans
        (mul_le_mul
          (Real.abs_expNegInvGlueDerivative_le_four x)
          hglueAbs (abs_nonneg _) (Nat.cast_nonneg 4))
        (le_of_eq (mul_one 4)))
  have hsecond :
      |expNegInvGlue x * Real.expNegInvGlueDerivative (1 - x)| ≤ 4 := by
    have hproduct := abs_mul
      (expNegInvGlue x) (Real.expNegInvGlueDerivative (1 - x))
    have hglueAbs : |expNegInvGlue x| ≤ 1 := by
      exact le_trans
        (le_of_eq (abs_of_nonneg (expNegInvGlue.nonneg x)))
        (Real.expNegInvGlue_le_one x)
    exact le_trans (le_of_eq hproduct)
      (le_trans
        (mul_le_mul hglueAbs
          (Real.abs_expNegInvGlueDerivative_le_four (1 - x))
          (abs_nonneg _) zero_le_one)
        (le_of_eq (one_mul 4)))
  have hsum := add_le_add hfirst hsecond
  exact le_trans htriangle
    (le_trans hsum (le_of_eq
      (Real.transitionSecondDerivative_natCast_add 4 4 8 (by decide))))

theorem Real.abs_smoothTransitionDerivativeNumeratorDerivative_le_one_five_three_six
    (x : ℝ) :
    |Real.smoothTransitionDerivativeNumeratorDerivative x| ≤ 1536 := by
  unfold Real.smoothTransitionDerivativeNumeratorDerivative
  have htriangle := abs_sub
    (Real.expNegInvGlueGlobalSecondDerivative x * expNegInvGlue (1 - x))
    (expNegInvGlue x * Real.expNegInvGlueGlobalSecondDerivative (1 - x))
  have hfirst :
      |Real.expNegInvGlueGlobalSecondDerivative x * expNegInvGlue (1 - x)| ≤
        768 := by
    have hproduct := abs_mul
      (Real.expNegInvGlueGlobalSecondDerivative x)
      (expNegInvGlue (1 - x))
    have hglue : |expNegInvGlue (1 - x)| ≤ 1 :=
      le_trans
        (le_of_eq (abs_of_nonneg (expNegInvGlue.nonneg (1 - x))))
        (Real.expNegInvGlue_le_one (1 - x))
    exact le_trans (le_of_eq hproduct)
      (le_trans
        (mul_le_mul
          (Real.abs_expNegInvGlueGlobalSecondDerivative_le_seven_sixty_eight x)
          hglue (abs_nonneg _) (Nat.cast_nonneg 768))
        (le_of_eq (mul_one 768)))
  have hsecond :
      |expNegInvGlue x * Real.expNegInvGlueGlobalSecondDerivative (1 - x)| ≤
        768 := by
    have hproduct := abs_mul
      (expNegInvGlue x)
      (Real.expNegInvGlueGlobalSecondDerivative (1 - x))
    have hglue : |expNegInvGlue x| ≤ 1 :=
      le_trans
        (le_of_eq (abs_of_nonneg (expNegInvGlue.nonneg x)))
        (Real.expNegInvGlue_le_one x)
    exact le_trans (le_of_eq hproduct)
      (le_trans
        (mul_le_mul hglue
          (Real.abs_expNegInvGlueGlobalSecondDerivative_le_seven_sixty_eight
            (1 - x))
          (abs_nonneg _) zero_le_one)
        (le_of_eq (one_mul 768)))
  exact le_trans htriangle
    (le_trans (add_le_add hfirst hsecond)
      (le_of_eq
        (Real.transitionSecondDerivative_natCast_add 768 768 1536
          (by decide))))

theorem Real.abs_smoothTransitionDerivativeDenominatorDerivative_le_eight
    (x : ℝ) :
    |Real.smoothTransitionDerivativeDenominatorDerivative x| ≤ 8 := by
  unfold Real.smoothTransitionDerivativeDenominatorDerivative
  exact le_trans (abs_sub _ _)
    (le_trans
      (add_le_add
        (Real.abs_expNegInvGlueDerivative_le_four x)
        (Real.abs_expNegInvGlueDerivative_le_four (1 - x)))
      (le_of_eq
        (Real.transitionSecondDerivative_natCast_add 4 4 8 (by decide))))

theorem Real.smoothTransitionDerivativeDenominator_le_two
    (x : ℝ) :
    Real.smoothTransitionDerivativeDenominator x ≤ 2 := by
  unfold Real.smoothTransitionDerivativeDenominator
  exact le_trans
    (add_le_add
      (Real.expNegInvGlue_le_one x)
      (Real.expNegInvGlue_le_one (1 - x)))
    (le_of_eq one_add_one_eq_two)

theorem Real.abs_smoothTransitionSecondDerivative_le_explicit
    (x : ℝ) :
    |Real.smoothTransitionSecondDerivative x| ≤
      6400 * (Real.exp 2) ^ 4 := by
  unfold Real.smoothTransitionSecondDerivative
  let N := Real.smoothTransitionDerivativeNumerator x
  let N' := Real.smoothTransitionDerivativeNumeratorDerivative x
  let D := Real.smoothTransitionDerivativeDenominator x
  let D' := Real.smoothTransitionDerivativeDenominatorDerivative x
  have hDNonneg : 0 ≤ D :=
    (Real.smoothTransitionDenominator_pos x).le
  have hDTwo : D ≤ 2 :=
    Real.smoothTransitionDerivativeDenominator_le_two x
  have hNumerator :
      |N' * D ^ 2 - N * (2 * D * D')| ≤ 6400 := by
    have htriangle := abs_sub (N' * D ^ 2) (N * (2 * D * D'))
    have hfirst : |N' * D ^ 2| ≤ 6144 := by
      have hDsq : D ^ 2 ≤ 4 := by
        have hmul := mul_self_le_mul_self hDNonneg hDTwo
        exact le_trans (le_of_eq (pow_two D))
          (le_trans hmul (le_of_eq
            (Real.transitionSecondDerivative_natCast_mul 2 2 4 (by decide))))
      exact le_trans (le_of_eq (abs_mul N' (D ^ 2)))
        (le_trans
          (mul_le_mul
            (Real.abs_smoothTransitionDerivativeNumeratorDerivative_le_one_five_three_six x)
            (le_trans (le_of_eq (abs_of_nonneg (sq_nonneg D))) hDsq)
            (abs_nonneg _) (Nat.cast_nonneg 1536))
          (le_of_eq
            (Real.transitionSecondDerivative_natCast_mul 1536 4 6144
              (by decide))))
    have hsecond : |N * (2 * D * D')| ≤ 256 := by
      have hfactor : |2 * D * D'| ≤ 32 := by
        have hproduct := abs_mul (2 * D) D'
        have hleftAbs : |2 * D| ≤ 4 := by
          exact le_trans (le_of_eq (abs_mul 2 D))
            (le_trans
              (mul_le_mul
                (le_of_eq (abs_of_nonneg (Nat.cast_nonneg 2)))
                (le_trans (le_of_eq (abs_of_nonneg hDNonneg)) hDTwo)
                (abs_nonneg D) (Nat.cast_nonneg 2))
              (le_of_eq
                (Real.transitionSecondDerivative_natCast_mul 2 2 4
                  (by decide))))
        exact le_trans (le_of_eq hproduct)
          (le_trans
            (mul_le_mul hleftAbs
              (Real.abs_smoothTransitionDerivativeDenominatorDerivative_le_eight x)
              (abs_nonneg _) (Nat.cast_nonneg 4))
            (le_of_eq
              (Real.transitionSecondDerivative_natCast_mul 4 8 32
                (by decide))))
      exact le_trans (le_of_eq (abs_mul N (2 * D * D')))
        (le_trans
          (mul_le_mul
            (Real.abs_smoothTransitionDerivativeNumerator_le_eight x)
            hfactor (abs_nonneg _) (Nat.cast_nonneg 8))
          (le_of_eq
            (Real.transitionSecondDerivative_natCast_mul 8 32 256
              (by decide))))
    exact le_trans htriangle
      (le_trans (add_le_add hfirst hsecond)
        (le_of_eq
          (Real.transitionSecondDerivative_natCast_add 6144 256 6400
            (by decide))))
  have hdenominatorInv :
      ((D ^ 2) ^ 2)⁻¹ ≤ (Real.exp 2) ^ 4 := by
    have hpower : ((D ^ 2) ^ 2)⁻¹ = D⁻¹ ^ 4 := by
      have hexponent : 2 * 2 = 4 := by decide
      have hnested : (D ^ 2) ^ 2 = D ^ 4 :=
        (pow_mul D 2 2).symm.trans
          (congrArg (fun exponent : ℕ => D ^ exponent) hexponent)
      exact (congrArg Inv.inv hnested).trans (inv_pow D 4).symm
    exact le_trans (le_of_eq hpower)
      (Real.inv_pow_four_smoothTransitionDenominator_le_exp_two_pow_four x)
  have hdivision :
      |(N' * D ^ 2 - N * (2 * D * D')) / (D ^ 2) ^ 2| =
        |N' * D ^ 2 - N * (2 * D * D')| * ((D ^ 2) ^ 2)⁻¹ := by
    exact (abs_div _ _).trans
      ((congrArg₂ (fun first second : ℝ => first / second)
        rfl (abs_of_pos (pow_pos (pow_pos
          (Real.smoothTransitionDenominator_pos x) 2) 2))).trans
        (div_eq_mul_inv _ _))
  exact le_trans (le_of_eq hdivision)
    (mul_le_mul hNumerator hdenominatorInv
      (inv_nonneg.mpr (sq_nonneg (D ^ 2))) (Nat.cast_nonneg 6400))

end
end LFunctions
end Boundary
