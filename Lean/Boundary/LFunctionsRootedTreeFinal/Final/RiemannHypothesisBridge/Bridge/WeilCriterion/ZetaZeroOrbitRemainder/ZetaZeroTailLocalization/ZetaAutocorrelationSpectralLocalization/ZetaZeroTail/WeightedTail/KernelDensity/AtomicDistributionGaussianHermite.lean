import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianProbe
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
# Hermite calculus for the physical Gaussian

The physical Gaussian is the complexification of the real Gaussian at the
`sqrt 2` spatial scale.  This file records that normalization before using
Mathlib's Hermite derivative formula.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

open scoped ContDiff

/-- The real-valued physical Gaussian. -/
noncomputable def realPhysicalGaussian (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2))

/-- The complex physical Gaussian is the complexification of its real-valued
counterpart. -/
theorem physicalGaussian_eq_ofReal_realPhysicalGaussian
    (t : ℝ) :
    physicalGaussian t = (realPhysicalGaussian t : ℂ) := by
  have hofRealExponential :
      ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) =
        Complex.exp (((-(t ^ 2) : ℝ) : ℂ)) :=
    Complex.ofReal_exp (-(t ^ 2))
  exact hofRealExponential.symm

/-- Squaring the `sqrt 2` scaling doubles the real square. -/
theorem sqrtTwo_mul_square
    (t : ℝ) :
    (Real.sqrt 2 * t) ^ 2 = 2 * t ^ 2 := by
  have hsqrtSquare : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt zero_le_two
  exact Eq.trans
    (mul_pow (Real.sqrt 2) t 2)
    (congrArg (fun value : ℝ => value * t ^ 2) hsqrtSquare)

/-- The physical Gaussian is Mathlib's Hermite Gaussian after `sqrt 2`
spatial scaling. -/
theorem realPhysicalGaussian_eq_hermiteGaussian_scaled
    (t : ℝ) :
    realPhysicalGaussian t =
      Real.exp (-((Real.sqrt 2 * t) ^ 2 / 2)) := by
  have htwoNonzero : (2 : ℝ) ≠ 0 :=
    two_ne_zero
  have hquadratic : (Real.sqrt 2 * t) ^ 2 / 2 = t ^ 2 :=
    Eq.trans
      (congrArg (fun value : ℝ => value / 2) (sqrtTwo_mul_square t))
      (mul_div_cancel_left₀ (t ^ 2) htwoNonzero)
  exact congrArg Real.exp (congrArg Neg.neg hquadratic).symm

/-- The real physical Gaussian is smooth. -/
theorem realPhysicalGaussian_contDiff :
    ContDiff ℝ ∞ realPhysicalGaussian := by
  have hsquare : ContDiff ℝ ∞ (fun t : ℝ => t ^ 2) :=
    contDiff_id.pow 2
  have hnegative : ContDiff ℝ ∞ (fun t : ℝ => -(t ^ 2)) :=
    hsquare.neg
  exact Real.contDiff_exp.comp hnegative

/-- The standard real Gaussian used by Mathlib's Hermite theorem. -/
noncomputable def hermiteStandardGaussian (u : ℝ) : ℝ :=
  Real.exp (-(u ^ 2 / 2))

/-- The standard Hermite Gaussian is smooth. -/
theorem hermiteStandardGaussian_contDiff :
    ContDiff ℝ ∞ hermiteStandardGaussian := by
  have hsquare : ContDiff ℝ ∞ (fun u : ℝ => u ^ 2) :=
    contDiff_id.pow 2
  have hdivision : ContDiff ℝ ∞ (fun u : ℝ => u ^ 2 / 2) :=
    hsquare.div_const 2
  have hnegative : ContDiff ℝ ∞ (fun u : ℝ => -(u ^ 2 / 2)) :=
    hdivision.neg
  exact Real.contDiff_exp.comp hnegative

/-- Exact Hermite-polynomial formula for every iterated derivative of the
real physical Gaussian. -/
theorem iteratedDeriv_realPhysicalGaussian_eq_hermite
    (order : ℕ)
    (t : ℝ) :
    iteratedDeriv order realPhysicalGaussian t =
      (Real.sqrt 2) ^ order *
        (((-1 : ℝ) ^ order *
            Polynomial.aeval (Real.sqrt 2 * t)
              (Polynomial.hermite order)) *
          Real.exp (-((Real.sqrt 2 * t) ^ 2 / 2))) := by
  have hfiniteSmooth :
      ContDiff ℝ order hermiteStandardGaussian :=
    hermiteStandardGaussian_contDiff.of_le
      (naturalOrder_le_contDiffInfinity order)
  have hfunction :
      realPhysicalGaussian =
        (fun t : ℝ =>
          hermiteStandardGaussian (Real.sqrt 2 * t)) := by
    funext t
    exact realPhysicalGaussian_eq_hermiteGaussian_scaled t
  have hscaled :=
    congrFun
      (iteratedDeriv_const_mul
        hfiniteSmooth
        (Real.sqrt 2))
      t
  have hhermite :
      iteratedDeriv order hermiteStandardGaussian
          (Real.sqrt 2 * t) =
        ((-1 : ℝ) ^ order *
            Polynomial.aeval (Real.sqrt 2 * t)
              (Polynomial.hermite order)) *
          Real.exp (-((Real.sqrt 2 * t) ^ 2 / 2)) := by
    have hmathlib :=
      Polynomial.deriv_gaussian_eq_hermite_mul_gaussian
        order
        (Real.sqrt 2 * t)
    exact Eq.trans
      (congrFun
        (iteratedDeriv_eq_iterate
          (n := order)
          (f := hermiteStandardGaussian))
        (Real.sqrt 2 * t))
      hmathlib
  exact Eq.subst
    (motive := fun function : ℝ → ℝ =>
      iteratedDeriv order function t =
        (Real.sqrt 2) ^ order *
          (((-1 : ℝ) ^ order *
              Polynomial.aeval (Real.sqrt 2 * t)
                (Polynomial.hermite order)) *
            Real.exp (-((Real.sqrt 2 * t) ^ 2 / 2))))
    hfunction.symm
    (Eq.trans hscaled
      (congrArg
        (fun value : ℝ => (Real.sqrt 2) ^ order * value)
        hhermite))

/-- The finite sum of absolute coefficients used to bound a real polynomial. -/
noncomputable def realPolynomialCoefficientNormSum
    (polynomial : Polynomial ℝ) : ℝ :=
  ∑ index ∈ Finset.range (polynomial.natDegree + 1),
    |polynomial.coeff index|

/-- The coefficient norm sum is nonnegative. -/
theorem realPolynomialCoefficientNormSum_nonnegative
    (polynomial : Polynomial ℝ) :
    0 ≤ realPolynomialCoefficientNormSum polynomial := by
  exact Finset.sum_nonneg
    (fun index hindex => abs_nonneg (polynomial.coeff index))

/-- A real polynomial is bounded by its coefficient norm sum times the
canonical polynomial height to its natural degree. -/
theorem abs_polynomial_eval_le_coefficientNormSum_mul_height
    (polynomial : Polynomial ℝ)
    (x : ℝ) :
    |polynomial.eval x| ≤
      realPolynomialCoefficientNormSum polynomial *
        (1 + |x|) ^ polynomial.natDegree := by
  let height : ℝ := 1 + |x|
  have hheightAtLeastOne : 1 ≤ height :=
    le_add_of_nonneg_right (abs_nonneg x)
  have habsoluteLeHeight : |x| ≤ height :=
    le_add_of_nonneg_left zero_le_one
  have hexpansion :
      polynomial.eval x =
        ∑ index ∈ Finset.range (polynomial.natDegree + 1),
          polynomial.coeff index * x ^ index :=
    Polynomial.eval_eq_sum_range x
  have htriangle :
      |∑ index ∈ Finset.range (polynomial.natDegree + 1),
          polynomial.coeff index * x ^ index| ≤
        ∑ index ∈ Finset.range (polynomial.natDegree + 1),
          |polynomial.coeff index * x ^ index| := by
    exact Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          ∑ index ∈ Finset.range (polynomial.natDegree + 1),
            |polynomial.coeff index * x ^ index|)
      (Real.norm_eq_abs
        (∑ index ∈ Finset.range (polynomial.natDegree + 1),
          polynomial.coeff index * x ^ index))
      (Eq.subst
        (motive := fun right : ℝ =>
          ‖∑ index ∈ Finset.range (polynomial.natDegree + 1),
              polynomial.coeff index * x ^ index‖ ≤ right)
        (congrArg
          (fun function : ℕ → ℝ =>
            ∑ index ∈ Finset.range (polynomial.natDegree + 1),
              function index)
          (funext (fun index =>
            Real.norm_eq_abs
              (polynomial.coeff index * x ^ index)))).symm
        (norm_sum_le
          (Finset.range (polynomial.natDegree + 1))
          (fun index => polynomial.coeff index * x ^ index)))
  have htermBound :
      ∀ index ∈ Finset.range (polynomial.natDegree + 1),
        |polynomial.coeff index * x ^ index| ≤
          |polynomial.coeff index| *
            height ^ polynomial.natDegree := by
    intro index hindex
    have hindexLeDegree : index ≤ polynomial.natDegree :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hindex)
    have habsolutePowerLeHeightPower :
        |x| ^ index ≤ height ^ index :=
      pow_le_pow_left₀ (abs_nonneg x) habsoluteLeHeight index
    have hheightPowerMonotone :
        height ^ index ≤ height ^ polynomial.natDegree :=
      pow_le_pow_right₀ hheightAtLeastOne hindexLeDegree
    have hxPower : |x ^ index| = |x| ^ index :=
      abs_pow x index
    have hproductAbsolute :
        |polynomial.coeff index * x ^ index| =
          |polynomial.coeff index| * |x| ^ index :=
      Eq.trans
        (abs_mul (polynomial.coeff index) (x ^ index))
        (congrArg
          (fun value : ℝ => |polynomial.coeff index| * value)
          hxPower)
    have hcoefficientNonnegative :
        0 ≤ |polynomial.coeff index| :=
      abs_nonneg (polynomial.coeff index)
    exact Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          |polynomial.coeff index| *
            height ^ polynomial.natDegree)
      hproductAbsolute.symm
      (mul_le_mul_of_nonneg_left
        (le_trans habsolutePowerLeHeightPower hheightPowerMonotone)
        hcoefficientNonnegative)
  have hsumBound :
      (∑ index ∈ Finset.range (polynomial.natDegree + 1),
          |polynomial.coeff index * x ^ index|) ≤
        ∑ index ∈ Finset.range (polynomial.natDegree + 1),
          |polynomial.coeff index| *
            height ^ polynomial.natDegree :=
    Finset.sum_le_sum
      (fun index hindex => htermBound index hindex)
  have hfactor :
      (∑ index ∈ Finset.range (polynomial.natDegree + 1),
          |polynomial.coeff index| *
            height ^ polynomial.natDegree) =
        realPolynomialCoefficientNormSum polynomial *
          height ^ polynomial.natDegree :=
    (Finset.sum_mul
      (Finset.range (polynomial.natDegree + 1))
      (fun index => |polynomial.coeff index|)
      (height ^ polynomial.natDegree)).symm
  exact Eq.subst
    (motive := fun left : ℝ =>
      left ≤
        realPolynomialCoefficientNormSum polynomial *
          height ^ polynomial.natDegree)
    (congrArg abs hexpansion).symm
    (le_trans htriangle
      (Eq.mp
        (congrArg
          (fun right : ℝ =>
            (∑ index ∈ Finset.range (polynomial.natDegree + 1),
              |polynomial.coeff index * x ^ index|) ≤ right)
          hfactor)
        hsumBound))

/-- The real scalar extension of the integer Hermite polynomial. -/
noncomputable def realHermitePolynomial (order : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite order).map (Int.castRingHom ℝ)

/-- Real Hermite evaluation is ordinary evaluation of the scalar-extended
Hermite polynomial. -/
theorem aeval_hermite_eq_realHermitePolynomial_eval
    (order : ℕ)
    (x : ℝ) :
    Polynomial.aeval x (Polynomial.hermite order) =
      (realHermitePolynomial order).eval x := by
  exact Eq.trans
    (Polynomial.aeval_def (x := x) (Polynomial.hermite order))
    (Polynomial.eval₂_eq_eval_map (f := Int.castRingHom ℝ))

/-- Hermite evaluation has an explicit polynomial-height bound. -/
theorem abs_aeval_hermite_le_coefficientNormSum_mul_height
    (order : ℕ)
    (x : ℝ) :
    |Polynomial.aeval x (Polynomial.hermite order)| ≤
      realPolynomialCoefficientNormSum (realHermitePolynomial order) *
        (1 + |x|) ^ (realHermitePolynomial order).natDegree := by
  exact Eq.subst
    (motive := fun value : ℝ =>
      |value| ≤
        realPolynomialCoefficientNormSum (realHermitePolynomial order) *
          (1 + |x|) ^ (realHermitePolynomial order).natDegree)
    (aeval_hermite_eq_realHermitePolynomial_eval order x).symm
    (abs_polynomial_eval_le_coefficientNormSum_mul_height
      (realHermitePolynomial order)
      x)

/-- A canonical polynomial height is bounded by a constant times the sum of
its zero-th and top-degree monomials. -/
theorem one_add_abs_pow_le_two_pow_mul_one_add_abs_pow
    (degree : ℕ)
    (x : ℝ) :
    (1 + |x|) ^ degree ≤
      (2 : ℝ) ^ degree * (1 + |x| ^ degree) := by
  have htwoNonnegative : 0 ≤ (2 : ℝ) :=
    zero_le_two
  have htwoPowerNonnegative : 0 ≤ (2 : ℝ) ^ degree :=
    pow_nonneg htwoNonnegative degree
  have habsolutePowerNonnegative : 0 ≤ |x| ^ degree :=
    pow_nonneg (abs_nonneg x) degree
  by_cases habsoluteLeOne : |x| ≤ 1
  ·
      have hheightLeTwo : 1 + |x| ≤ (2 : ℝ) :=
        Eq.mp
          (congrArg
            (fun right : ℝ => 1 + |x| ≤ right)
            one_add_one_eq_two)
          (add_le_add_left habsoluteLeOne 1)
      have hheightPowerLeTwoPower :
          (1 + |x|) ^ degree ≤ (2 : ℝ) ^ degree :=
        pow_le_pow_left₀
          (add_nonneg zero_le_one (abs_nonneg x))
          hheightLeTwo
          degree
      have honeLeFactor : 1 ≤ 1 + |x| ^ degree :=
        le_add_of_nonneg_right habsolutePowerNonnegative
      have htwoPowerLeProduct :
          (2 : ℝ) ^ degree ≤
            (2 : ℝ) ^ degree * (1 + |x| ^ degree) :=
        Eq.mp
          (congrArg
            (fun left : ℝ =>
              left ≤ (2 : ℝ) ^ degree * (1 + |x| ^ degree))
            (mul_one ((2 : ℝ) ^ degree)))
          (mul_le_mul_of_nonneg_left
            honeLeFactor
            htwoPowerNonnegative)
      exact le_trans hheightPowerLeTwoPower htwoPowerLeProduct
  ·
      have honeLeAbsolute : 1 ≤ |x| :=
        le_of_not_ge habsoluteLeOne
      have hheightLeDouble :
          1 + |x| ≤ 2 * |x| := by
        have hadd : 1 + |x| ≤ |x| + |x| :=
          add_le_add_right honeLeAbsolute |x|
        have hdouble : |x| + |x| = 2 * |x| :=
          (two_mul |x|).symm
        exact Eq.mp
          (congrArg (fun right : ℝ => 1 + |x| ≤ right) hdouble)
          hadd
      have hheightPowerLeDoublePower :
          (1 + |x|) ^ degree ≤ (2 * |x|) ^ degree :=
        pow_le_pow_left₀
          (add_nonneg zero_le_one (abs_nonneg x))
          hheightLeDouble
          degree
      have hdoublePower :
          (2 * |x|) ^ degree =
            (2 : ℝ) ^ degree * |x| ^ degree :=
        mul_pow 2 |x| degree
      have habsolutePowerLeOneAdded :
          |x| ^ degree ≤ 1 + |x| ^ degree :=
        le_add_of_nonneg_left zero_le_one
      have hproductIncrease :
          (2 : ℝ) ^ degree * |x| ^ degree ≤
            (2 : ℝ) ^ degree * (1 + |x| ^ degree) :=
        mul_le_mul_of_nonneg_left
          habsolutePowerLeOneAdded
          htwoPowerNonnegative
      exact le_trans hheightPowerLeDoublePower
        (Eq.subst
          (motive := fun left : ℝ =>
            left ≤ (2 : ℝ) ^ degree * (1 + |x| ^ degree))
          hdoublePower.symm
          hproductIncrease)

/-- Multiplicative scaling of the real variable is controlled by the product
of the two canonical heights. -/
theorem one_add_abs_mul_le_height_product
    (scale t : ℝ) :
    1 + |scale * t| ≤
      (1 + |scale|) * (1 + |t|) := by
  have habsoluteProduct : |scale * t| = |scale| * |t| :=
    abs_mul scale t
  have hscaleNonnegative : 0 ≤ |scale| :=
    abs_nonneg scale
  have htermIncrease :
      1 + |scale| * |t| ≤
        (1 + |scale|) + |scale| * |t| := by
    have hraw :
        1 + |scale| * |t| ≤
          (1 + |scale| * |t|) + |scale| :=
      le_add_of_nonneg_right hscaleNonnegative
    have hreorder :
        (1 + |scale| * |t|) + |scale| =
          (1 + |scale|) + |scale| * |t| :=
      Eq.trans
        (add_assoc 1 (|scale| * |t|) |scale|)
        (Eq.trans
          (congrArg
            (fun value : ℝ => 1 + value)
            (add_comm (|scale| * |t|) |scale|))
          (add_assoc 1 |scale| (|scale| * |t|)).symm)
    exact Eq.mp
      (congrArg
        (fun right : ℝ => 1 + |scale| * |t| ≤ right)
        hreorder)
      hraw
  have hexpand :
      (1 + |scale|) * (1 + |t|) =
        (1 + |scale|) + |scale| * |t| + |t| := by
    have hdistribute :
        (1 + |scale|) * (1 + |t|) =
          1 * (1 + |t|) + |scale| * (1 + |t|) :=
      add_mul 1 |scale| (1 + |t|)
    have honeProduct : 1 * (1 + |t|) = 1 + |t| :=
      one_mul (1 + |t|)
    have hscaleProduct :
        |scale| * (1 + |t|) = |scale| + |scale| * |t| :=
      Eq.trans
        (mul_add |scale| 1 |t|)
        (congrArg
          (fun value : ℝ => value + |scale| * |t|)
          (mul_one |scale|))
    have hreorder :
        (1 + |t|) + (|scale| + |scale| * |t|) =
          (1 + |scale|) + |scale| * |t| + |t| := by
      calc
        (1 + |t|) + (|scale| + |scale| * |t|) =
            1 + (|t| + |scale|) + |scale| * |t| :=
          Eq.trans
            (add_assoc 1 |t| (|scale| + |scale| * |t|))
            (Eq.trans
              (congrArg
                (fun value : ℝ => 1 + value)
                (add_assoc |t| |scale| (|scale| * |t|)).symm)
              (add_assoc 1 (|t| + |scale|) (|scale| * |t|)).symm)
        _ = 1 + (|scale| + |t|) + |scale| * |t| :=
          congrArg
            (fun value : ℝ => 1 + value + |scale| * |t|)
            (add_comm |t| |scale|)
        _ = (1 + |scale|) + |scale| * |t| + |t| := by
          have hfirst : 1 + (|scale| + |t|) = (1 + |scale|) + |t| :=
            (add_assoc 1 |scale| |t|).symm
          have hswap :
              ((1 + |scale|) + |t|) + |scale| * |t| =
                (1 + |scale|) + |scale| * |t| + |t| :=
            Eq.trans
              (add_assoc (1 + |scale|) |t| (|scale| * |t|))
              (Eq.trans
                (congrArg
                  (fun value : ℝ => (1 + |scale|) + value)
                  (add_comm |t| (|scale| * |t|)))
                (add_assoc
                  (1 + |scale|)
                  (|scale| * |t|)
                  |t|).symm)
          exact Eq.trans
            (congrArg
              (fun value : ℝ => value + |scale| * |t|)
              hfirst)
            hswap
    exact Eq.trans hdistribute
      (Eq.trans
        (congrArg₂ Add.add honeProduct hscaleProduct)
        hreorder)
  have hnonnegativeTail : 0 ≤ |t| :=
    abs_nonneg t
  have hwithTail :
      (1 + |scale|) + |scale| * |t| ≤
        (1 + |scale|) + |scale| * |t| + |t| :=
    le_add_of_nonneg_right hnonnegativeTail
  exact Eq.subst
    (motive := fun left : ℝ =>
      left ≤ (1 + |scale|) * (1 + |t|))
    (congrArg (fun value : ℝ => 1 + value) habsoluteProduct).symm
    (Eq.subst
      (motive := fun right : ℝ => 1 + |scale| * |t| ≤ right)
      hexpand.symm
      (le_trans htermIncrease hwithTail))

/-- Natural powers of the scaled canonical height are bounded by separate
scale and variable height powers. -/
theorem one_add_abs_mul_pow_le_height_product_pow
    (scale t : ℝ)
    (degree : ℕ) :
    (1 + |scale * t|) ^ degree ≤
      (1 + |scale|) ^ degree * (1 + |t|) ^ degree := by
  have hbase := one_add_abs_mul_le_height_product scale t
  have hpower :
      (1 + |scale * t|) ^ degree ≤
        ((1 + |scale|) * (1 + |t|)) ^ degree :=
    pow_le_pow_left₀
      (add_nonneg zero_le_one (abs_nonneg (scale * t)))
      hbase
      degree
  exact Eq.mp
    (congrArg
      (fun right : ℝ => (1 + |scale * t|) ^ degree ≤ right)
      (mul_pow (1 + |scale|) (1 + |t|) degree))
    hpower

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
