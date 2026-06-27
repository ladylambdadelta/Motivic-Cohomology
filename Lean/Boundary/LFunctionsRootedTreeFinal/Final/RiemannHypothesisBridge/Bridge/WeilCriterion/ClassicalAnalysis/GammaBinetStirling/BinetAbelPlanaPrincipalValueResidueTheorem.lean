import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaEndpointIndentationLimits

/-!
# Principal-value residue theorem for the finite-height Abel-Plana rectangle

This file owns the transport from punctured-rectangle Cauchy-Goursat plus
small-circle/indentation limits to the finite-height principal-value residue
identity.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Multiplication distributes over a lower-half-plane cotangent split. -/
theorem Complex.mul_eq_mul_add_mul_sub
    (a b c : ℂ) :
    a * b = a * c + a * (b - c) := by
  have hbc : c + (b - c) = b := by
    calc
      c + (b - c) = c + (b + -c) := by
        exact congrArg (fun z : ℂ => c + z) (sub_eq_add_neg b c)
      _ = c + b + -c := by
        exact (add_assoc c b (-c)).symm
      _ = b + c + -c := by
        exact congrArg (fun z : ℂ => z + -c) (add_comm c b)
      _ = b + (c + -c) := by
        exact add_assoc b c (-c)
      _ = b + 0 := by
        exact congrArg (fun z : ℂ => b + z) (add_neg_cancel c)
      _ = b := by
        exact add_zero b
  calc
    a * b = a * (c + (b - c)) := by
      exact congrArg (fun z : ℂ => a * z) hbc.symm
    _ = a * c + a * (b - c) := by
      exact mul_add a c (b - c)

/-- A right cancellation identity used by the upper-half-plane cotangent split. -/
theorem Complex.neg_add_add_cancel_right
    (x y : ℂ) :
    -x + (y + x) = y := by
  calc
    -x + (y + x) = y + (-x + x) := by
      exact
        Eq.trans
          (add_assoc (-x) y x).symm
          (Eq.trans
            (congrArg (fun z : ℂ => z + x) (add_comm (-x) y))
            (add_assoc y (-x) x))
    _ = y + 0 := by
      exact congrArg (fun z : ℂ => y + z) (neg_add_cancel x)
    _ = y := by
      exact add_zero y

/-- Multiplication distributes over an upper-half-plane cotangent split. -/
theorem Complex.mul_eq_mul_neg_add_mul_add
    (a b c : ℂ) :
    a * b = a * (-c) + a * (b + c) := by
  exact Eq.symm
    (Eq.trans
      (congrArg₂
        HAdd.hAdd
        (mul_neg a c)
        (mul_add a b c))
      (Complex.neg_add_add_cancel_right (a * c) (a * b)))

/-- Normalize a negated product in the constant term of an upper-half-plane
cotangent split. -/
theorem Complex.mul_neg_product_constant_add_normalize
    (a p q r : ℂ) :
    a * (-(p * q)) + r = a * ((-p) * q) + r := by
  exact congrArg (fun z : ℂ => a * z + r) (neg_mul p q).symm

/-- Four-term regrouping for splitting a lower and upper vertical side into
constant and exponential-remainder pieces. -/
theorem Complex.verticalSide_split_collect
    (lowerConstant upperConstant lowerRemainder upperRemainder : ℂ) :
    (lowerConstant + lowerRemainder) + (upperConstant + upperRemainder) =
      (lowerConstant + upperConstant) + (lowerRemainder + upperRemainder) := by
  calc
    (lowerConstant + lowerRemainder) + (upperConstant + upperRemainder)
        = lowerConstant + (lowerRemainder + (upperConstant + upperRemainder)) := by
      exact add_assoc lowerConstant lowerRemainder (upperConstant + upperRemainder)
    _ = lowerConstant + ((lowerRemainder + upperConstant) + upperRemainder) := by
      exact congrArg
        (fun z : ℂ => lowerConstant + z)
        (add_assoc lowerRemainder upperConstant upperRemainder).symm
    _ = lowerConstant + ((upperConstant + lowerRemainder) + upperRemainder) := by
      exact congrArg
        (fun z : ℂ => lowerConstant + (z + upperRemainder))
        (add_comm lowerRemainder upperConstant)
    _ = lowerConstant + (upperConstant + (lowerRemainder + upperRemainder)) := by
      exact congrArg
        (fun z : ℂ => lowerConstant + z)
        (add_assoc upperConstant lowerRemainder upperRemainder)
    _ = (lowerConstant + upperConstant) + (lowerRemainder + upperRemainder) := by
      exact Eq.symm
        (add_assoc lowerConstant upperConstant (lowerRemainder + upperRemainder))

/-- Cancellation of an adjacent horizontal constant in the left oriented
side assembly. -/
theorem Complex.leftOrientedVertical_assembly_collect
    (horizontal constant remainder : ℂ) :
    -Complex.I * (constant + remainder) =
      horizontal + ((-horizontal - Complex.I * constant) +
        (-Complex.I * remainder)) := by
  have hcancel :
      horizontal + -horizontal = (0 : ℂ) :=
    add_neg_cancel horizontal
  have hneg_const :
      -Complex.I * constant = -(Complex.I * constant) :=
    neg_mul Complex.I constant
  calc
    -Complex.I * (constant + remainder) =
        (-Complex.I * constant) + (-Complex.I * remainder) := by
      exact mul_add (-Complex.I) constant remainder
    _ = horizontal + ((-horizontal - Complex.I * constant) +
        (-Complex.I * remainder)) := by
      calc
        (-Complex.I * constant) + (-Complex.I * remainder) =
            -(Complex.I * constant) + (-Complex.I * remainder) := by
          exact congrArg
            (fun z : ℂ => z + (-Complex.I * remainder))
            hneg_const
        _ = (0 : ℂ) + (-(Complex.I * constant) + (-Complex.I * remainder)) := by
          exact (zero_add (-(Complex.I * constant) + (-Complex.I * remainder))).symm
        _ = (horizontal + -horizontal) +
            (-(Complex.I * constant) + (-Complex.I * remainder)) := by
          exact congrArg
            (fun z : ℂ =>
              z + (-(Complex.I * constant) + (-Complex.I * remainder)))
            hcancel.symm
        _ = horizontal + (-horizontal +
            (-(Complex.I * constant) + (-Complex.I * remainder))) := by
          exact add_assoc horizontal (-horizontal)
            (-(Complex.I * constant) + (-Complex.I * remainder))
        _ = horizontal + ((-horizontal + -(Complex.I * constant)) +
            (-Complex.I * remainder)) := by
          exact congrArg
            (fun z : ℂ => horizontal + z)
            (add_assoc (-horizontal) (-(Complex.I * constant))
              (-Complex.I * remainder)).symm
        _ = horizontal + ((-horizontal - Complex.I * constant) +
            (-Complex.I * remainder)) := by
          exact congrArg
            (fun z : ℂ => horizontal + (z + (-Complex.I * remainder)))
            (sub_eq_add_neg (-horizontal) (Complex.I * constant)).symm

/-- Cancellation of an adjacent horizontal constant in the right oriented
side assembly. -/
theorem Complex.rightOrientedVertical_assembly_collect
    (horizontal constant remainder : ℂ) :
    Complex.I * (constant + remainder) =
      (horizontal + Complex.I * constant) +
        (Complex.I * remainder) - horizontal := by
  calc
    Complex.I * (constant + remainder) =
        Complex.I * constant + Complex.I * remainder := by
      exact mul_add Complex.I constant remainder
    _ =
      (horizontal + Complex.I * constant) +
        (Complex.I * remainder) - horizontal := by
      have htarget :
          (horizontal + Complex.I * constant) +
              (Complex.I * remainder) - horizontal =
            Complex.I * constant + Complex.I * remainder := by
        calc
          (horizontal + Complex.I * constant) +
              (Complex.I * remainder) - horizontal =
              ((horizontal + Complex.I * constant) +
                (Complex.I * remainder)) + -horizontal := by
            exact sub_eq_add_neg
              ((horizontal + Complex.I * constant) + Complex.I * remainder)
              horizontal
          _ = (horizontal + -horizontal) +
              (Complex.I * constant + Complex.I * remainder) := by
            calc
              ((horizontal + Complex.I * constant) +
                    (Complex.I * remainder)) + -horizontal =
                  (horizontal + Complex.I * constant) +
                    (Complex.I * remainder + -horizontal) := by
                exact add_assoc (horizontal + Complex.I * constant)
                  (Complex.I * remainder) (-horizontal)
              _ = (horizontal + Complex.I * constant) +
                    (-horizontal + Complex.I * remainder) := by
                exact congrArg
                  (fun z : ℂ => (horizontal + Complex.I * constant) + z)
                  (add_comm (Complex.I * remainder) (-horizontal))
              _ = horizontal +
                    (Complex.I * constant +
                      (-horizontal + Complex.I * remainder)) := by
                exact add_assoc horizontal (Complex.I * constant)
                  (-horizontal + Complex.I * remainder)
              _ = horizontal +
                    ((Complex.I * constant + -horizontal) +
                      Complex.I * remainder) := by
                exact congrArg
                  (fun z : ℂ => horizontal + z)
                  (add_assoc (Complex.I * constant) (-horizontal)
                    (Complex.I * remainder)).symm
              _ = horizontal +
                    ((-horizontal + Complex.I * constant) +
                      Complex.I * remainder) := by
                exact congrArg
                  (fun z : ℂ => horizontal + (z + Complex.I * remainder))
                  (add_comm (Complex.I * constant) (-horizontal))
              _ = horizontal +
                    (-horizontal +
                      (Complex.I * constant + Complex.I * remainder)) := by
                exact congrArg
                  (fun z : ℂ => horizontal + z)
                  (add_assoc (-horizontal) (Complex.I * constant)
                    (Complex.I * remainder))
              _ = (horizontal + -horizontal) +
                    (Complex.I * constant + Complex.I * remainder) := by
                exact (add_assoc horizontal (-horizontal)
                  (Complex.I * constant + Complex.I * remainder)).symm
          _ = 0 + (Complex.I * constant + Complex.I * remainder) := by
            exact congrArg
              (fun z : ℂ => z + (Complex.I * constant + Complex.I * remainder))
              (add_neg_cancel horizontal)
          _ = Complex.I * constant + Complex.I * remainder := by
            exact zero_add (Complex.I * constant + Complex.I * remainder)
      exact htarget.symm

/-- Replacing the constant and remainder identities in the left oriented
assembly gives the named lower side. -/
theorem Complex.leftOrientedVertical_after_substitution
    (endpoint lower : ℂ) :
    endpoint + (-lower) = endpoint - lower := by
  exact Eq.symm (sub_eq_add_neg endpoint lower)

/-- Replacing the constant and remainder identities in the right oriented
assembly removes the zero constant part. -/
theorem Complex.rightOrientedVertical_after_substitution
    (upper lowerHorizontal : ℂ) :
    0 + (-upper) - lowerHorizontal =
      -upper - lowerHorizontal := by
  exact
    Eq.trans
      (congrArg
        (fun z : ℂ => z - lowerHorizontal)
        (zero_add (-upper)))
      (Eq.refl (-upper - lowerHorizontal))

/-- The left boundary face cancels its adjacent upper horizontal constant. -/
theorem Complex.leftHalfContour_cancel_horizontal
    (upper lowerFace : ℂ) :
    -upper + (upper + lowerFace) = lowerFace :=
  neg_add_cancel_left upper lowerFace

/-- The right boundary face cancels its adjacent lower horizontal constant. -/
theorem Complex.rightHalfContour_cancel_horizontal
    (lower upperFace : ℂ) :
    lower + (upperFace - lower) = upperFace :=
  by
    calc
      lower + (upperFace - lower) = (upperFace - lower) + lower := by
        exact add_comm lower (upperFace - lower)
      _ = upperFace := by
        exact sub_add_cancel upperFace lower

/-- Boundary-face algebra: left and right raw faces collect into constant
horizontal and raw vertical contributions. -/
theorem Complex.finiteAbelPlana_boundaryFace_collect
    (lower upper right left : ℂ) :
    (-upper - Complex.I * left) + (lower + Complex.I * right) =
      lower - upper + (Complex.I * right - Complex.I * left) := by
  calc
    (-upper - Complex.I * left) + (lower + Complex.I * right) =
        (-upper + -(Complex.I * left)) + (lower + Complex.I * right) := by
      exact congrArg
        (fun z : ℂ => z + (lower + Complex.I * right))
        (sub_eq_add_neg (-upper) (Complex.I * left))
    _ = (lower + -upper) + (Complex.I * right + -(Complex.I * left)) := by
      calc
        (-upper + -(Complex.I * left)) + (lower + Complex.I * right) =
            -upper + (-(Complex.I * left) + (lower + Complex.I * right)) := by
          exact add_assoc (-upper) (-(Complex.I * left)) (lower + Complex.I * right)
        _ = -upper + ((-(Complex.I * left) + lower) + Complex.I * right) := by
          exact congrArg (fun z : ℂ => -upper + z)
            (add_assoc (-(Complex.I * left)) lower (Complex.I * right)).symm
        _ = -upper + ((lower + -(Complex.I * left)) + Complex.I * right) := by
          exact congrArg
            (fun z : ℂ => -upper + (z + Complex.I * right))
            (add_comm (-(Complex.I * left)) lower)
        _ = (-upper + (lower + -(Complex.I * left))) + Complex.I * right := by
          exact (add_assoc (-upper) (lower + -(Complex.I * left))
            (Complex.I * right)).symm
        _ = ((-upper + lower) + -(Complex.I * left)) + Complex.I * right := by
          exact congrArg
            (fun z : ℂ => z + Complex.I * right)
            (add_assoc (-upper) lower (-(Complex.I * left))).symm
        _ = ((lower + -upper) + -(Complex.I * left)) + Complex.I * right := by
          exact congrArg
            (fun z : ℂ => (z + -(Complex.I * left)) + Complex.I * right)
            (add_comm (-upper) lower)
        _ = (lower + -upper) + (-(Complex.I * left) + Complex.I * right) := by
          exact add_assoc (lower + -upper) (-(Complex.I * left)) (Complex.I * right)
        _ = (lower + -upper) + (Complex.I * right + -(Complex.I * left)) := by
          exact congrArg (fun z : ℂ => (lower + -upper) + z)
            (add_comm (-(Complex.I * left)) (Complex.I * right))
    _ = lower - upper + (Complex.I * right - Complex.I * left) := by
      exact congrArg₂ HAdd.hAdd
        (sub_eq_add_neg lower upper).symm
        (sub_eq_add_neg (Complex.I * right) (Complex.I * left)).symm

/-- Named-boundary algebra: lower face plus upper face equals real endpoint
plus the combined named vertical side. -/
theorem Complex.finiteAbelPlana_namedBoundary_collect
    (endpoint lower upper : ℂ) :
    (endpoint - lower) + (-upper) =
      endpoint + (-lower - upper) := by
  calc
    (endpoint - lower) + (-upper) =
        endpoint + (-lower) + (-upper) := by
      exact congrArg (fun z : ℂ => z + (-upper)) (sub_eq_add_neg endpoint lower)
    _ = endpoint + (-lower - upper) := by
      exact Eq.trans
        (add_assoc endpoint (-lower) (-upper))
        (congrArg (fun z : ℂ => endpoint + z)
          (sub_eq_add_neg (-lower) upper).symm)

/-- Principal-value finite punctured-rectangle residue accounting obtained by
combining the Cauchy-Goursat punctured-boundary limit with the small-circle
residue limits. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangleResidueAccountingPV
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)))
    (T : ℝ)
    (hT : 0 < T) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) := by
  have hcauchy :
      Filter.Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (0 : ℂ)) :=
    Complex.finiteAbelPlana_log_puncturedRectangleCauchyGoursat_pvSmallCircles
      hw N T hT
  have hcircles :
      Filter.Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ)
        (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) :=
    Complex.finiteAbelPlana_log_pvDeletedBoundaryIntegralContribution_tendsto_pvResidues
      hw N hdecInteriorPole
  have hsum :
      Filter.Tendsto
        (fun ρ : ℝ =>
          (Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ) +
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (0 +
            Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) :=
    hcauchy.add hcircles
  have hpoint :
      (fun ρ : ℝ =>
        (Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ) +
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ) :=
    Filter.Eventually.of_forall
      (fun ρ =>
        sub_add_cancel
          (Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
          (Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ))
  have htarget :
      (0 +
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w :=
    zero_add (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)
  exact (htarget ▸ hsum).congr' hpoint

/-- Principal-value punctured finite-rectangle boundary accounting for the
Abel-Plana cotangent kernel.

This is the direct Cauchy-Goursat step on the rectangle with small circles
around the integer cotangent poles removed.  After the endpoint
principal-value indentations are normalized, the PV outer rectangle side tends
to the small-circle residue contribution. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPuncturedRectangleBoundary_tendsto_residues
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)))
    (T : ℝ)
    (hT : 0 < T) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) := by
  exact
    Complex.finiteAbelPlana_log_puncturedRectangleResidueAccountingPV
      hw N hdecInteriorPole T hT

/-- Principal-value residue theorem for the finite Abel-Plana logarithmic
rectangle.

The intended proof is the standard Abel-Plana contour argument:

1. use the rectangle Cauchy theorem to
   `finiteAbelPlanaLogRectangleIntegrand w` on the finite rectangle with small
   circles excised around the integer poles;
2. use
   `finiteAbelPlana_log_rectangleIntegrand_shrinkingCircleResidues` to identify
   each shrinking circle with the local residue `log (w+n)`;
3. let the endpoint indentations tend to the half-endpoint principal-value
   terms and collect the oriented rectangle sides.

The local analytic residue input is already owned by `BinetAbelPlanaCore`; this
lemma owns only the global finite-rectangle residue accounting. -/
theorem Complex.finiteAbelPlana_log_finiteHeightRectangle_principalValueResidueTheorem
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)))
    (T : ℝ)
    (hT : 0 < T) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝
        (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) := by
  have hlim :
      Filter.Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) :=
    Complex.finiteAbelPlana_log_finiteHeightPuncturedRectangleBoundary_tendsto_residues
      hw N hdecInteriorPole T hT
  exact hlim

/-- Real segment plus endpoint-principal-value contribution in the
finite-height Abel-Plana side decomposition. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression
    (N : ℕ)
    (w : ℂ) : ℂ :=
  let M : ℕ := N + 1
  (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
    Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w

/-- Endpoint principal-value indentation normalization to the half-endpoint
term in the finite Abel-Plana formula. -/
theorem Complex.finiteAbelPlana_log_endpointPVIndentationContribution_eq_halfEndpoints
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w =
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w := by
  exact Eq.refl (Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w)

/-- The finite-height named side expression is the real/endpoints part plus
the named lower and upper vertical Abel-Plana jump integrals. -/
theorem Complex.finiteAbelPlana_log_finiteHeightNamedSideExpression_eq_realEndpoint_add_vertical
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
      Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
        Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T := by
  exact Eq.refl (Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T)

/-- Lower horizontal cotangent constant part after the lower-half-plane
cotangent expansion. -/
noncomputable def Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  let M : ℕ := N + 1
  ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
    Complex.finiteAbelPlanaLogSummand w
      ((x : ℂ) - (T : ℂ) * Complex.I) *
      ((Real.pi : ℂ) * Complex.I)

/-- Upper horizontal cotangent constant part after the upper-half-plane
cotangent expansion. -/
noncomputable def Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  let M : ℕ := N + 1
  ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
    Complex.finiteAbelPlanaLogSummand w
      ((x : ℂ) + (T : ℂ) * Complex.I) *
      (-(Real.pi : ℂ) * Complex.I)

/-- Multiplication by a cotangent kernel split into a chosen constant part and
its subtractive remainder. -/
theorem Complex.mul_kernel_eq_constant_add_subtractiveRemainder
    (a K C : ℂ) :
    a * K = a * C + a * (K - C) := by
  have hsplit : C + (K - C) = K := by
    calc
      C + (K - C) = (K - C) + C := by
        exact add_comm C (K - C)
      _ = K := by
        exact sub_add_cancel K C
  calc
    a * K = a * (C + (K - C)) := by
      exact congrArg (fun z : ℂ => a * z) hsplit.symm
    _ = a * C + a * (K - C) :=
      mul_add a C (K - C)

/-- Multiplication by a cotangent kernel split into a chosen negative constant
part and its additive remainder. -/
theorem Complex.mul_kernel_eq_negConstant_add_additiveRemainder
    (a K C : ℂ) :
    a * K = a * (-C) + a * (K + C) := by
  have hsum : (-C) + (K + C) = K := by
    calc
      (-C) + (K + C) = K + ((-C) + C) := by
        exact add_left_comm (-C) K C
      _ = K + 0 := by
        exact congrArg (fun z : ℂ => K + z) (neg_add_cancel C)
      _ = K :=
        add_zero K
  calc
    a * K = a * ((-C) + (K + C)) := by
      exact congrArg (fun z : ℂ => a * z) hsum.symm
    _ = a * (-C) + a * (K + C) :=
      mul_add a (-C) (K + C)

/-- Horizontal lower contour parametrization uses `-T * I`, not `-I * T`,
after commuting scalar factors. -/
theorem Complex.finiteAbelPlana_lowerHorizontal_path_eq
    (x T : ℝ) :
    ((x : ℂ) - Complex.I * (T : ℂ)) =
      ((x : ℂ) - (T : ℂ) * Complex.I) := by
  exact congrArg (fun z : ℂ => (x : ℂ) - z) (mul_comm Complex.I (T : ℂ))

/-- Horizontal upper contour parametrization uses `T * I`, not `I * T`,
after commuting scalar factors. -/
theorem Complex.finiteAbelPlana_upperHorizontal_path_eq
    (x T : ℝ) :
    ((x : ℂ) + Complex.I * (T : ℂ)) =
      ((x : ℂ) + (T : ℂ) * Complex.I) := by
  exact congrArg (fun z : ℂ => (x : ℂ) + z) (mul_comm Complex.I (T : ℂ))

/-- Pointwise lower-horizontal cotangent splitting:
`K = πi + (K - πi)`. -/
theorem Complex.finiteAbelPlana_lowerHorizontal_integrand_split
    (w : ℂ)
    (x T : ℝ) :
    Complex.finiteAbelPlanaLogRectangleIntegrand w
        ((x : ℂ) - Complex.I * (T : ℂ)) =
      Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) - (T : ℂ) * Complex.I) *
          ((Real.pi : ℂ) * Complex.I) +
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) - (T : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) - (T : ℂ) * Complex.I) -
            (Real.pi : ℂ) * Complex.I) := by
  have harg :
      ((x : ℂ) - Complex.I * (T : ℂ)) =
        ((x : ℂ) - (T : ℂ) * Complex.I) :=
    Complex.finiteAbelPlana_lowerHorizontal_path_eq x T
  have hunfold :
      Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((x : ℂ) - (T : ℂ) * Complex.I) =
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) - (T : ℂ) * Complex.I) *
          Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) - (T : ℂ) * Complex.I) :=
    Complex.finiteAbelPlanaLogRectangleIntegrand_unfold
      w ((x : ℂ) - (T : ℂ) * Complex.I)
  exact
    Eq.trans
      (congrArg
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        harg)
      (Eq.trans hunfold
        (Complex.mul_kernel_eq_constant_add_subtractiveRemainder
          (Complex.finiteAbelPlanaLogSummand w ((x : ℂ) - (T : ℂ) * Complex.I))
          (Complex.finiteAbelPlanaCotangentKernel ((x : ℂ) - (T : ℂ) * Complex.I))
          ((Real.pi : ℂ) * Complex.I)))

/-- Pointwise upper-horizontal cotangent splitting:
`K = -πi + (K + πi)`. -/
theorem Complex.finiteAbelPlana_upperHorizontal_integrand_split
    (w : ℂ)
    (x T : ℝ) :
    Complex.finiteAbelPlanaLogRectangleIntegrand w
        ((x : ℂ) + Complex.I * (T : ℂ)) =
      Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) + (T : ℂ) * Complex.I) *
          (-(Real.pi : ℂ) * Complex.I) +
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) + (T : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) + (T : ℂ) * Complex.I) +
            (Real.pi : ℂ) * Complex.I) := by
  have harg :
      ((x : ℂ) + Complex.I * (T : ℂ)) =
        ((x : ℂ) + (T : ℂ) * Complex.I) :=
    Complex.finiteAbelPlana_upperHorizontal_path_eq x T
  have hunfold :
      Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((x : ℂ) + (T : ℂ) * Complex.I) =
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) + (T : ℂ) * Complex.I) *
          Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) + (T : ℂ) * Complex.I) :=
    Complex.finiteAbelPlanaLogRectangleIntegrand_unfold
      w ((x : ℂ) + (T : ℂ) * Complex.I)
  exact
    Eq.trans
      (congrArg
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        harg)
      (Eq.trans hunfold
        (Eq.trans
          (Complex.mul_kernel_eq_negConstant_add_additiveRemainder
            (Complex.finiteAbelPlanaLogSummand w ((x : ℂ) + (T : ℂ) * Complex.I))
            (Complex.finiteAbelPlanaCotangentKernel ((x : ℂ) + (T : ℂ) * Complex.I))
            ((Real.pi : ℂ) * Complex.I))
          (Complex.mul_neg_product_constant_add_normalize
            (Complex.finiteAbelPlanaLogSummand w ((x : ℂ) + (T : ℂ) * Complex.I))
            (Real.pi : ℂ)
            Complex.I
            (Complex.finiteAbelPlanaLogSummand w ((x : ℂ) + (T : ℂ) * Complex.I) *
              (Complex.finiteAbelPlanaCotangentKernel ((x : ℂ) + (T : ℂ) * Complex.I) +
                (Real.pi : ℂ) * Complex.I)))))

/-- The lower horizontal logarithmic path lies in the principal slit plane on
the finite Abel-Plana interval. -/
theorem Complex.finiteAbelPlana_log_lowerHorizontalPath_mem_slitPlane
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    {x : ℝ}
    (hx : x ∈ Set.uIcc (0 : ℝ) ((N + 1 : ℕ) : ℝ)) :
    w + ((x : ℂ) - (T : ℂ) * Complex.I) ∈ Complex.slitPlane := by
  have hN : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) :=
    Nat.cast_nonneg (N + 1)
  have hxIcc : x ∈ Set.Icc (0 : ℝ) ((N + 1 : ℕ) : ℝ) :=
    (Set.uIcc_of_le hN).symm ▸ hx
  have hx_nonneg : 0 ≤ x :=
    hxIcc.1
  have hmul_re : (((T : ℂ) * Complex.I).re) = 0 := by
    calc
      (((T : ℂ) * Complex.I).re) = -((T : ℂ).im) := by
        exact Complex.mul_I_re (T : ℂ)
      _ = -0 := by
        exact congrArg Neg.neg (Complex.ofReal_im T)
      _ = 0 := by
        exact neg_zero
  have hpath_re :
      (w + ((x : ℂ) - (T : ℂ) * Complex.I)).re = w.re + x := by
    calc
      (w + ((x : ℂ) - (T : ℂ) * Complex.I)).re =
          w.re + ((x : ℂ) - (T : ℂ) * Complex.I).re := by
        exact Complex.add_re w ((x : ℂ) - (T : ℂ) * Complex.I)
      _ = w.re + ((x : ℂ).re - ((T : ℂ) * Complex.I).re) := by
        exact congrArg (fun r : ℝ => w.re + r)
          (Complex.sub_re (x : ℂ) ((T : ℂ) * Complex.I))
      _ = w.re + ((x : ℂ).re - 0) := by
        exact congrArg (fun r : ℝ => w.re + ((x : ℂ).re - r)) hmul_re
      _ = w.re + (x - 0) := by
        exact congrArg (fun r : ℝ => w.re + (r - 0)) (Complex.ofReal_re x)
      _ = w.re + x := by
        exact congrArg (fun r : ℝ => w.re + r) (sub_zero x)
  have hre : 0 < (w + ((x : ℂ) - (T : ℂ) * Complex.I)).re :=
    hpath_re.symm ▸ add_pos_of_pos_of_nonneg hw hx_nonneg
  exact Complex.mem_slitPlane_iff.mpr (Or.inl hre)

/-- The upper horizontal logarithmic path lies in the principal slit plane on
the finite Abel-Plana interval. -/
theorem Complex.finiteAbelPlana_log_upperHorizontalPath_mem_slitPlane
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    {x : ℝ}
    (hx : x ∈ Set.uIcc (0 : ℝ) ((N + 1 : ℕ) : ℝ)) :
    w + ((x : ℂ) + (T : ℂ) * Complex.I) ∈ Complex.slitPlane := by
  have hN : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) :=
    Nat.cast_nonneg (N + 1)
  have hxIcc : x ∈ Set.Icc (0 : ℝ) ((N + 1 : ℕ) : ℝ) :=
    (Set.uIcc_of_le hN).symm ▸ hx
  have hx_nonneg : 0 ≤ x :=
    hxIcc.1
  have hmul_re : (((T : ℂ) * Complex.I).re) = 0 := by
    calc
      (((T : ℂ) * Complex.I).re) = -((T : ℂ).im) := by
        exact Complex.mul_I_re (T : ℂ)
      _ = -0 := by
        exact congrArg Neg.neg (Complex.ofReal_im T)
      _ = 0 := by
        exact neg_zero
  have hpath_re :
      (w + ((x : ℂ) + (T : ℂ) * Complex.I)).re = w.re + x := by
    calc
      (w + ((x : ℂ) + (T : ℂ) * Complex.I)).re =
          w.re + ((x : ℂ) + (T : ℂ) * Complex.I).re := by
        exact Complex.add_re w ((x : ℂ) + (T : ℂ) * Complex.I)
      _ = w.re + ((x : ℂ).re + ((T : ℂ) * Complex.I).re) := by
        exact congrArg (fun r : ℝ => w.re + r)
          (Complex.add_re (x : ℂ) ((T : ℂ) * Complex.I))
      _ = w.re + ((x : ℂ).re + 0) := by
        exact congrArg (fun r : ℝ => w.re + ((x : ℂ).re + r)) hmul_re
      _ = w.re + (x + 0) := by
        exact congrArg (fun r : ℝ => w.re + (r + 0)) (Complex.ofReal_re x)
      _ = w.re + x := by
        exact congrArg (fun r : ℝ => w.re + r) (add_zero x)
  have hre : 0 < (w + ((x : ℂ) + (T : ℂ) * Complex.I)).re :=
    hpath_re.symm ▸ add_pos_of_pos_of_nonneg hw hx_nonneg
  exact Complex.mem_slitPlane_iff.mpr (Or.inl hre)

/-- Complex primitive for the logarithmic Abel-Plana summand on arbitrary
straight line segments. -/
noncomputable def Complex.finiteAbelPlanaLogComplexPrimitive
    (w u : ℂ) : ℂ :=
  (w + u) * Complex.log (w + u) - (w + u)

/-- Unfolding of the complex logarithmic primitive. -/
theorem Complex.finiteAbelPlanaLogComplexPrimitive_unfold
    (w u : ℂ) :
    Complex.finiteAbelPlanaLogComplexPrimitive w u =
      (w + u) * Complex.log (w + u) - (w + u) :=
  Eq.refl (Complex.finiteAbelPlanaLogComplexPrimitive w u)

/-- The complex logarithmic primitive restricted to the real endpoints is the
endpoint primitive used by the finite Abel-Plana formula. -/
theorem Complex.finiteAbelPlana_log_complexPrimitive_realEndpoint_sub_eq_endpointPrimitive
    (N : ℕ)
    (w : ℂ) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogComplexPrimitive w (M : ℂ) -
        Complex.finiteAbelPlanaLogComplexPrimitive w (0 : ℂ) =
      Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w := by
  intro M
  have hleft_zero :
      Complex.finiteAbelPlanaLogComplexPrimitive w (0 : ℂ) =
        w * Complex.log w - w := by
    calc
      Complex.finiteAbelPlanaLogComplexPrimitive w (0 : ℂ) =
          (w + (0 : ℂ)) * Complex.log (w + (0 : ℂ)) - (w + (0 : ℂ)) := by
        exact Complex.finiteAbelPlanaLogComplexPrimitive_unfold w 0
      _ = w * Complex.log w - w := by
        exact congrArg₂ Sub.sub
          (congrArg₂ HMul.hMul
            (add_zero w)
            (congrArg Complex.log (add_zero w)))
          (add_zero w)
  have hright :
      Complex.finiteAbelPlanaLogComplexPrimitive w (M : ℂ) =
        (w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
          (w + (M : ℂ)) := by
    exact Complex.finiteAbelPlanaLogComplexPrimitive_unfold w (M : ℂ)
  calc
    Complex.finiteAbelPlanaLogComplexPrimitive w (M : ℂ) -
        Complex.finiteAbelPlanaLogComplexPrimitive w (0 : ℂ) =
      ((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
          (w + (M : ℂ))) -
        (w * Complex.log w - w) := by
      exact congrArg₂ Sub.sub hright hleft_zero
    _ = Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w := by
      exact (Complex.finiteAbelPlanaLogSummandEndpointPrimitive_unfold N w).symm

/-- The surviving real-endpoint primitive difference is exactly the finite
real-segment integral. -/
theorem Complex.finiteAbelPlana_log_complexPrimitive_realEndpoint_sub_eq_realSegmentIntegral
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogComplexPrimitive w (M : ℂ) -
        Complex.finiteAbelPlanaLogComplexPrimitive w (0 : ℂ) =
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ) := by
  intro M
  have hprimitive :
      Complex.finiteAbelPlanaLogComplexPrimitive w (M : ℂ) -
          Complex.finiteAbelPlanaLogComplexPrimitive w (0 : ℂ) =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w :=
    Complex.finiteAbelPlana_log_complexPrimitive_realEndpoint_sub_eq_endpointPrimitive
      N w
  have hintegral :
      (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w :=
    Complex.finiteAbelPlana_log_summand_realSegmentIntegral_eq_endpointPrimitive
      hw N
  exact hprimitive.trans hintegral.symm

/-- Derivative of the logarithmic primitive along a straight complex line. -/
theorem Complex.hasDerivAt_finiteAbelPlanaLogComplexPrimitive_line
    (w a v : ℂ)
    {t : ℝ}
    (hslit : w + ((t : ℂ) * v + a) ∈ Complex.slitPlane) :
    HasDerivAt
      (fun s : ℝ =>
        Complex.finiteAbelPlanaLogComplexPrimitive w ((s : ℂ) * v + a))
      (v * Complex.finiteAbelPlanaLogSummand w ((t : ℂ) * v + a))
      t := by
  let g : ℝ → ℂ := fun s : ℝ => w + ((s : ℂ) * v + a)
  have hg : HasDerivAt g v t := by
    have hcomplex :
        HasDerivAt
          (fun z : ℂ => w + (z * v + a))
          ((1 : ℂ) * v)
          (t : ℂ) :=
      (((hasDerivAt_id (t : ℂ)).mul_const v).const_add a).const_add w
    exact (one_mul v) ▸ hcomplex.comp_ofReal
  have hlog :
      HasDerivAt
        (fun s : ℝ => Complex.log (g s))
        (v / g t)
        t :=
    hg.clog_real hslit
  have hmul :
      HasDerivAt
        (fun s : ℝ => g s * Complex.log (g s))
        (v * Complex.log (g t) + g t * (v / g t))
        t :=
    hg.mul hlog
  have hsub :
      HasDerivAt
        (fun s : ℝ => g s * Complex.log (g s) - g s)
        ((v * Complex.log (g t) + g t * (v / g t)) - v)
        t :=
    hmul.sub hg
  have hg_ne : g t ≠ 0 :=
    Complex.slitPlane_ne_zero hslit
  have hcancel : g t * (v / g t) = v := by
    calc
      g t * (v / g t) = g t * (v * (g t)⁻¹) := by
        exact congrArg (fun z : ℂ => g t * z) (div_eq_mul_inv v (g t))
      _ = (g t * v) * (g t)⁻¹ := by
        exact mul_assoc (g t) v (g t)⁻¹
      _ = (v * g t) * (g t)⁻¹ := by
        exact congrArg (fun z : ℂ => z * (g t)⁻¹) (mul_comm (g t) v)
      _ = v * (g t * (g t)⁻¹) := by
        exact mul_assoc v (g t) (g t)⁻¹
      _ = v * 1 := by
        exact congrArg (fun z : ℂ => v * z) (mul_inv_cancel₀ hg_ne)
      _ = v := by
        exact mul_one v
  have hderiv :
      (v * Complex.log (g t) + g t * (v / g t)) - v =
        v * Complex.finiteAbelPlanaLogSummand w ((t : ℂ) * v + a) := by
    calc
      (v * Complex.log (g t) + g t * (v / g t)) - v =
          (v * Complex.log (g t) + v) - v := by
        exact congrArg
          (fun z : ℂ => (v * Complex.log (g t) + z) - v)
          hcancel
      _ = v * Complex.log (g t) := by
        exact add_sub_cancel_right (v * Complex.log (g t)) v
      _ = v * Complex.finiteAbelPlanaLogSummand w ((t : ℂ) * v + a) := by
        exact Eq.refl (v * Complex.finiteAbelPlanaLogSummand w ((t : ℂ) * v + a))
  exact hderiv ▸ hsub

/-- FTC for the top horizontal logarithmic primitive along the finite
Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlana_log_topHorizontalPrimitive_integral
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ) :
    let M : ℕ := N + 1
    ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) + (T : ℂ) * Complex.I) =
      Complex.finiteAbelPlanaLogComplexPrimitive w
          (((M : ℝ) : ℂ) + (T : ℂ) * Complex.I) -
        Complex.finiteAbelPlanaLogComplexPrimitive w
          ((0 : ℂ) + (T : ℂ) * Complex.I) := by
  intro M
  have hderiv :
      ∀ x ∈ Set.uIcc (0 : ℝ) (M : ℝ),
        HasDerivAt
          (fun y : ℝ =>
            Complex.finiteAbelPlanaLogComplexPrimitive w
              ((y : ℂ) * (1 : ℂ) + (T : ℂ) * Complex.I))
          (Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) + (T : ℂ) * Complex.I))
          x := by
    intro x hx
    have hx_cast :
        (x : ℂ) * (1 : ℂ) + (T : ℂ) * Complex.I =
          (x : ℂ) + (T : ℂ) * Complex.I := by
      exact congrArg (fun z : ℂ => z + (T : ℂ) * Complex.I) (mul_one (x : ℂ))
    have hslit :
        w + ((x : ℂ) * (1 : ℂ) + (T : ℂ) * Complex.I) ∈ Complex.slitPlane := by
      exact hx_cast ▸
        Complex.finiteAbelPlana_log_upperHorizontalPath_mem_slitPlane
          N hw T hx
    have hline :=
      Complex.hasDerivAt_finiteAbelPlanaLogComplexPrimitive_line
        w ((T : ℂ) * Complex.I) (1 : ℂ) hslit
    have hderiv_value :
        (1 : ℂ) *
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) * (1 : ℂ) + (T : ℂ) * Complex.I) =
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) + (T : ℂ) * Complex.I) := by
      calc
        (1 : ℂ) *
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) * (1 : ℂ) + (T : ℂ) * Complex.I) =
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) * (1 : ℂ) + (T : ℂ) * Complex.I) := by
          exact one_mul _
        _ =
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) + (T : ℂ) * Complex.I) := by
          exact congrArg (fun z : ℂ => Complex.finiteAbelPlanaLogSummand w z) hx_cast
    exact hderiv_value ▸ hline
  have hcont :
      ContinuousOn
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) + (T : ℂ) * Complex.I))
        (Set.uIcc (0 : ℝ) (M : ℝ)) := by
    intro x hx
    have hslit :
        w + ((x : ℂ) + (T : ℂ) * Complex.I) ∈ Complex.slitPlane :=
      Complex.finiteAbelPlana_log_upperHorizontalPath_mem_slitPlane
        N hw T hx
    exact
      (((continuous_const.add
        (Complex.continuous_ofReal.add continuous_const)).continuousAt).clog hslit).continuousWithinAt
  have hint :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) + (T : ℂ) * Complex.I))
        volume
        (0 : ℝ)
        (M : ℝ) :=
    hcont.intervalIntegrable
  have hFTC :
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) + (T : ℂ) * Complex.I) =
        Complex.finiteAbelPlanaLogComplexPrimitive w
            (((M : ℝ) : ℂ) * (1 : ℂ) + (T : ℂ) * Complex.I) -
          Complex.finiteAbelPlanaLogComplexPrimitive w
            (((0 : ℝ) : ℂ) * (1 : ℂ) + (T : ℂ) * Complex.I) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have htop :
      ((M : ℝ) : ℂ) * (1 : ℂ) + (T : ℂ) * Complex.I =
        ((M : ℝ) : ℂ) + (T : ℂ) * Complex.I := by
    exact congrArg (fun z : ℂ => z + (T : ℂ) * Complex.I)
      (mul_one (((M : ℝ) : ℂ)))
  have hbottom :
      ((0 : ℝ) : ℂ) * (1 : ℂ) + (T : ℂ) * Complex.I =
        (0 : ℂ) + (T : ℂ) * Complex.I := by
    exact congrArg (fun z : ℂ => z + (T : ℂ) * Complex.I)
      (mul_one (((0 : ℝ) : ℂ)))
  exact Eq.trans hFTC
    (congrArg₂ Sub.sub
      (congrArg (fun z : ℂ => Complex.finiteAbelPlanaLogComplexPrimitive w z) htop)
      (congrArg (fun z : ℂ => Complex.finiteAbelPlanaLogComplexPrimitive w z) hbottom))

/-- FTC for a left vertical constant-kernel segment of the logarithmic
primitive. -/
theorem Complex.finiteAbelPlana_log_leftVerticalConstantPrimitive_integral
    {w : ℂ}
    (hw : 0 < w.re)
    (a b : ℝ) :
    ∫ y : ℝ in a..b,
        Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
          ((Real.pi : ℂ) * Complex.I) =
      (Real.pi : ℂ) *
        (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (b : ℂ)) -
          Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (a : ℂ))) := by
  let P : ℂ := (Real.pi : ℂ)
  let F : ℝ → ℂ := fun y : ℝ =>
    P * Complex.finiteAbelPlanaLogComplexPrimitive w ((y : ℂ) * Complex.I + 0)
  have hderiv :
      ∀ y ∈ Set.uIcc a b,
        HasDerivAt F
          (Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            ((Real.pi : ℂ) * Complex.I))
          y := by
    intro y _hy
    have hy_comm :
        (y : ℂ) * Complex.I = Complex.I * (y : ℂ) :=
      mul_comm (y : ℂ) Complex.I
    have hslit :
        w + ((y : ℂ) * Complex.I + 0) ∈ Complex.slitPlane := by
      have harg :
          (y : ℂ) * Complex.I + 0 = Complex.I * (y : ℂ) := by
        exact Eq.trans (add_zero ((y : ℂ) * Complex.I)) hy_comm
      exact harg ▸
        Complex.finiteAbelPlana_log_leftVerticalPath_mem_slitPlane hw y
    have hline :
        HasDerivAt
          (fun s : ℝ =>
            Complex.finiteAbelPlanaLogComplexPrimitive w
              ((s : ℂ) * Complex.I + 0))
          (Complex.I *
            Complex.finiteAbelPlanaLogSummand w ((y : ℂ) * Complex.I + 0))
          y :=
      Complex.hasDerivAt_finiteAbelPlanaLogComplexPrimitive_line
        w 0 Complex.I hslit
    have hscaled :
        HasDerivAt F
          (P *
            (Complex.I *
              Complex.finiteAbelPlanaLogSummand w ((y : ℂ) * Complex.I + 0)))
          y :=
      hline.const_mul P
    have hvalue :
        P *
            (Complex.I *
              Complex.finiteAbelPlanaLogSummand w ((y : ℂ) * Complex.I + 0)) =
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            ((Real.pi : ℂ) * Complex.I) := by
      have hsummand :
          Complex.finiteAbelPlanaLogSummand w ((y : ℂ) * Complex.I + 0) =
            Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) := by
        have harg :
            (y : ℂ) * Complex.I + 0 = Complex.I * (y : ℂ) := by
          exact Eq.trans (add_zero ((y : ℂ) * Complex.I)) hy_comm
        exact congrArg (fun z : ℂ => Complex.finiteAbelPlanaLogSummand w z) harg
      calc
        P *
            (Complex.I *
              Complex.finiteAbelPlanaLogSummand w ((y : ℂ) * Complex.I + 0)) =
            P *
              (Complex.I *
                Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ))) := by
          exact congrArg
            (fun z : ℂ => P * (Complex.I * z))
            hsummand
        _ =
            (P * Complex.I) *
              Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) := by
          exact (mul_assoc P Complex.I
            (Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)))).symm
        _ =
            Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
              (P * Complex.I) := by
          exact mul_comm (P * Complex.I)
            (Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)))
        _ =
            Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
              ((Real.pi : ℂ) * Complex.I) := by
          exact Eq.refl _
    exact hvalue ▸ hscaled
  have hcont :
      ContinuousOn
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            ((Real.pi : ℂ) * Complex.I))
        (Set.uIcc a b) := by
    intro y _hy
    have hslit :
        w + Complex.I * (y : ℂ) ∈ Complex.slitPlane :=
      Complex.finiteAbelPlana_log_leftVerticalPath_mem_slitPlane hw y
    have harg_cont :
        ContinuousAt (fun s : ℝ => w + Complex.I * (s : ℂ)) y :=
      (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousAt
    exact ((harg_cont.clog hslit).mul continuousAt_const).continuousWithinAt
  have hint :
      IntervalIntegrable
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            ((Real.pi : ℂ) * Complex.I))
        volume a b :=
    hcont.intervalIntegrable
  have hFTC :
      ∫ y : ℝ in a..b,
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            ((Real.pi : ℂ) * Complex.I) =
        F b - F a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hendpoints :
      F b - F a =
        (Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (b : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (a : ℂ))) := by
    have hb :
        ((b : ℂ) * Complex.I + 0) = Complex.I * (b : ℂ) := by
      exact Eq.trans (add_zero ((b : ℂ) * Complex.I)) (mul_comm (b : ℂ) Complex.I)
    have ha :
        ((a : ℂ) * Complex.I + 0) = Complex.I * (a : ℂ) := by
      exact Eq.trans (add_zero ((a : ℂ) * Complex.I)) (mul_comm (a : ℂ) Complex.I)
    calc
      F b - F a =
          P * Complex.finiteAbelPlanaLogComplexPrimitive w ((b : ℂ) * Complex.I + 0) -
            P * Complex.finiteAbelPlanaLogComplexPrimitive w ((a : ℂ) * Complex.I + 0) := by
        exact Eq.refl _
      _ =
          P * Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (b : ℂ)) -
            P * Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (a : ℂ)) := by
        exact congrArg₂ Sub.sub
          (congrArg (fun z : ℂ => P * Complex.finiteAbelPlanaLogComplexPrimitive w z) hb)
          (congrArg (fun z : ℂ => P * Complex.finiteAbelPlanaLogComplexPrimitive w z) ha)
      _ =
          P *
            (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (b : ℂ)) -
              Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (a : ℂ))) := by
        exact (mul_sub P
          (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (b : ℂ)))
          (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (a : ℂ)))).symm
      _ =
          (Real.pi : ℂ) *
            (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (b : ℂ)) -
              Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (a : ℂ))) := by
        exact Eq.refl _
  exact Eq.trans hFTC hendpoints

/-- FTC for the bottom horizontal logarithmic primitive along the finite
Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlana_log_bottomHorizontalPrimitive_integral
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ) :
    let M : ℕ := N + 1
    ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) - (T : ℂ) * Complex.I) =
      Complex.finiteAbelPlanaLogComplexPrimitive w
          (((M : ℝ) : ℂ) - (T : ℂ) * Complex.I) -
        Complex.finiteAbelPlanaLogComplexPrimitive w
          ((0 : ℂ) - (T : ℂ) * Complex.I) := by
  intro M
  let a : ℂ := -((T : ℂ) * Complex.I)
  have hderiv :
      ∀ x ∈ Set.uIcc (0 : ℝ) (M : ℝ),
        HasDerivAt
          (fun y : ℝ =>
            Complex.finiteAbelPlanaLogComplexPrimitive w
              ((y : ℂ) * (1 : ℂ) + a))
          (Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) - (T : ℂ) * Complex.I))
          x := by
    intro x hx
    have hx_cast :
        (x : ℂ) * (1 : ℂ) + a =
          (x : ℂ) - (T : ℂ) * Complex.I := by
      calc
        (x : ℂ) * (1 : ℂ) + a =
            (x : ℂ) + a := by
          exact congrArg (fun z : ℂ => z + a) (mul_one (x : ℂ))
        _ = (x : ℂ) + -((T : ℂ) * Complex.I) := by
          exact Eq.refl _
        _ = (x : ℂ) - (T : ℂ) * Complex.I := by
          exact (sub_eq_add_neg (x : ℂ) ((T : ℂ) * Complex.I)).symm
    have hslit :
        w + ((x : ℂ) * (1 : ℂ) + a) ∈ Complex.slitPlane := by
      exact hx_cast ▸
        Complex.finiteAbelPlana_log_lowerHorizontalPath_mem_slitPlane
          N hw T hx
    have hline :=
      Complex.hasDerivAt_finiteAbelPlanaLogComplexPrimitive_line
        w a (1 : ℂ) hslit
    have hderiv_value :
        (1 : ℂ) *
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) * (1 : ℂ) + a) =
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) - (T : ℂ) * Complex.I) := by
      calc
        (1 : ℂ) *
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) * (1 : ℂ) + a) =
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) * (1 : ℂ) + a) := by
          exact one_mul _
        _ =
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) - (T : ℂ) * Complex.I) := by
          exact congrArg (fun z : ℂ => Complex.finiteAbelPlanaLogSummand w z) hx_cast
    exact hderiv_value ▸ hline
  have hcont :
      ContinuousOn
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) - (T : ℂ) * Complex.I))
        (Set.uIcc (0 : ℝ) (M : ℝ)) := by
    intro x hx
    have hslit :
        w + ((x : ℂ) - (T : ℂ) * Complex.I) ∈ Complex.slitPlane :=
      Complex.finiteAbelPlana_log_lowerHorizontalPath_mem_slitPlane
        N hw T hx
    exact
      (((continuous_const.add
        (Complex.continuous_ofReal.sub continuous_const)).continuousAt).clog hslit).continuousWithinAt
  have hint :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) - (T : ℂ) * Complex.I))
        volume
        (0 : ℝ)
        (M : ℝ) :=
    hcont.intervalIntegrable
  have hFTC :
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) - (T : ℂ) * Complex.I) =
        Complex.finiteAbelPlanaLogComplexPrimitive w
            (((M : ℝ) : ℂ) * (1 : ℂ) + a) -
          Complex.finiteAbelPlanaLogComplexPrimitive w
            (((0 : ℝ) : ℂ) * (1 : ℂ) + a) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have htop :
      ((M : ℝ) : ℂ) * (1 : ℂ) + a =
        ((M : ℝ) : ℂ) - (T : ℂ) * Complex.I := by
    calc
      ((M : ℝ) : ℂ) * (1 : ℂ) + a =
          ((M : ℝ) : ℂ) + a := by
        exact congrArg (fun z : ℂ => z + a)
          (mul_one (((M : ℝ) : ℂ)))
      _ = ((M : ℝ) : ℂ) + -((T : ℂ) * Complex.I) := by
        exact Eq.refl _
      _ = ((M : ℝ) : ℂ) - (T : ℂ) * Complex.I := by
        exact (sub_eq_add_neg (((M : ℝ) : ℂ)) ((T : ℂ) * Complex.I)).symm
  have hbottom :
      ((0 : ℝ) : ℂ) * (1 : ℂ) + a =
        (0 : ℂ) - (T : ℂ) * Complex.I := by
    calc
      ((0 : ℝ) : ℂ) * (1 : ℂ) + a =
          ((0 : ℝ) : ℂ) + a := by
        exact congrArg (fun z : ℂ => z + a)
          (mul_one (((0 : ℝ) : ℂ)))
      _ = (0 : ℂ) + -((T : ℂ) * Complex.I) := by
        exact Eq.refl _
      _ = (0 : ℂ) - (T : ℂ) * Complex.I := by
        exact (sub_eq_add_neg (0 : ℂ) ((T : ℂ) * Complex.I)).symm
  exact Eq.trans hFTC
    (congrArg₂ Sub.sub
      (congrArg (fun z : ℂ => Complex.finiteAbelPlanaLogComplexPrimitive w z) htop)
      (congrArg (fun z : ℂ => Complex.finiteAbelPlanaLogComplexPrimitive w z) hbottom))

/-- Lower horizontal constant side evaluated by the logarithmic primitive. -/
theorem Complex.finiteAbelPlana_log_lowerHorizontalCotangentConstantSide_eq_primitive
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T =
      (Complex.finiteAbelPlanaLogComplexPrimitive w
          (((M : ℝ) : ℂ) - (T : ℂ) * Complex.I) -
        Complex.finiteAbelPlanaLogComplexPrimitive w
          ((0 : ℂ) - (T : ℂ) * Complex.I)) *
        ((Real.pi : ℂ) * Complex.I) := by
  intro M
  let c : ℂ := (Real.pi : ℂ) * Complex.I
  let f : ℝ → ℂ := fun x : ℝ =>
    Complex.finiteAbelPlanaLogSummand w
      ((x : ℂ) - (T : ℂ) * Complex.I)
  have hmul :
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ), f x * c =
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ), f x) * c :=
    intervalIntegral.integral_mul_const c f
  have hprimitive :
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) - (T : ℂ) * Complex.I) =
        Complex.finiteAbelPlanaLogComplexPrimitive w
            (((M : ℝ) : ℂ) - (T : ℂ) * Complex.I) -
          Complex.finiteAbelPlanaLogComplexPrimitive w
            ((0 : ℂ) - (T : ℂ) * Complex.I) :=
    Complex.finiteAbelPlana_log_bottomHorizontalPrimitive_integral N hw T
  calc
    Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T =
        ∫ x : ℝ in (0 : ℝ)..(M : ℝ), f x * c := by
      rfl
    _ = (∫ x : ℝ in (0 : ℝ)..(M : ℝ), f x) * c :=
      hmul
    _ =
        (Complex.finiteAbelPlanaLogComplexPrimitive w
            (((M : ℝ) : ℂ) - (T : ℂ) * Complex.I) -
          Complex.finiteAbelPlanaLogComplexPrimitive w
            ((0 : ℂ) - (T : ℂ) * Complex.I)) *
          ((Real.pi : ℂ) * Complex.I) := by
      exact congrArg (fun z : ℂ => z * c) hprimitive

/-- Upper horizontal constant side evaluated by the logarithmic primitive. -/
theorem Complex.finiteAbelPlana_log_upperHorizontalCotangentConstantSide_eq_primitive
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T =
      (Complex.finiteAbelPlanaLogComplexPrimitive w
          (((M : ℝ) : ℂ) + (T : ℂ) * Complex.I) -
        Complex.finiteAbelPlanaLogComplexPrimitive w
          ((0 : ℂ) + (T : ℂ) * Complex.I)) *
        (-(Real.pi : ℂ) * Complex.I) := by
  intro M
  let c : ℂ := -(Real.pi : ℂ) * Complex.I
  let f : ℝ → ℂ := fun x : ℝ =>
    Complex.finiteAbelPlanaLogSummand w
      ((x : ℂ) + (T : ℂ) * Complex.I)
  have hmul :
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ), f x * c =
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ), f x) * c :=
    intervalIntegral.integral_mul_const c f
  have hprimitive :
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) + (T : ℂ) * Complex.I) =
        Complex.finiteAbelPlanaLogComplexPrimitive w
            (((M : ℝ) : ℂ) + (T : ℂ) * Complex.I) -
          Complex.finiteAbelPlanaLogComplexPrimitive w
            ((0 : ℂ) + (T : ℂ) * Complex.I) :=
    Complex.finiteAbelPlana_log_topHorizontalPrimitive_integral N hw T
  calc
    Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T =
        ∫ x : ℝ in (0 : ℝ)..(M : ℝ), f x * c := by
      rfl
    _ = (∫ x : ℝ in (0 : ℝ)..(M : ℝ), f x) * c :=
      hmul
    _ =
        (Complex.finiteAbelPlanaLogComplexPrimitive w
            (((M : ℝ) : ℂ) + (T : ℂ) * Complex.I) -
          Complex.finiteAbelPlanaLogComplexPrimitive w
            ((0 : ℂ) + (T : ℂ) * Complex.I)) *
          (-(Real.pi : ℂ) * Complex.I) := by
      exact congrArg (fun z : ℂ => z * c) hprimitive

/-- Nonzero height excludes cotangent poles on the lower horizontal side. -/
theorem Complex.finiteAbelPlana_log_lowerHorizontalPath_sin_ne_zero
    (T : ℝ)
    (hT : 0 < T)
    (x : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((x : ℂ) - (T : ℂ) * Complex.I)) ≠ 0 := by
  have him : (((x : ℂ) - (T : ℂ) * Complex.I).im) = -T := by
    calc
      (((x : ℂ) - (T : ℂ) * Complex.I).im) =
          (x : ℂ).im - ((T : ℂ) * Complex.I).im := by
        exact Complex.sub_im (x : ℂ) ((T : ℂ) * Complex.I)
      _ = 0 - ((T : ℂ) * Complex.I).im := by
        exact congrArg (fun r : ℝ => r - ((T : ℂ) * Complex.I).im)
          (Complex.ofReal_im x)
      _ = 0 - (T : ℂ).re := by
        exact congrArg (fun r : ℝ => 0 - r) (Complex.mul_I_im (T : ℂ))
      _ = 0 - T := by
        exact congrArg (fun r : ℝ => 0 - r) (Complex.ofReal_re T)
      _ = -T := by
        exact zero_sub T
  have hne_im : (((x : ℂ) - (T : ℂ) * Complex.I).im) ≠ 0 :=
    him.symm ▸ (neg_ne_zero.mpr hT.ne')
  exact Complex.sin_pi_mul_ne_zero_of_im_ne_zero hne_im

/-- Nonzero height excludes cotangent poles on the upper horizontal side. -/
theorem Complex.finiteAbelPlana_log_upperHorizontalPath_sin_ne_zero
    (T : ℝ)
    (hT : 0 < T)
    (x : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((x : ℂ) + (T : ℂ) * Complex.I)) ≠ 0 := by
  have him : (((x : ℂ) + (T : ℂ) * Complex.I).im) = T := by
    calc
      (((x : ℂ) + (T : ℂ) * Complex.I).im) =
          (x : ℂ).im + ((T : ℂ) * Complex.I).im := by
        exact Complex.add_im (x : ℂ) ((T : ℂ) * Complex.I)
      _ = 0 + ((T : ℂ) * Complex.I).im := by
        exact congrArg (fun r : ℝ => r + ((T : ℂ) * Complex.I).im)
          (Complex.ofReal_im x)
      _ = 0 + (T : ℂ).re := by
        exact congrArg (fun r : ℝ => 0 + r) (Complex.mul_I_im (T : ℂ))
      _ = 0 + T := by
        exact congrArg (fun r : ℝ => 0 + r) (Complex.ofReal_re T)
      _ = T := by
        exact zero_add T
  have hne_im : (((x : ℂ) + (T : ℂ) * Complex.I).im) ≠ 0 :=
    him.symm ▸ hT.ne'
  exact Complex.sin_pi_mul_ne_zero_of_im_ne_zero hne_im

/-- The lower horizontal side splits into its lower-half-plane constant
cotangent part plus the named decaying bottom horizontal edge. -/
theorem Complex.finiteAbelPlana_log_lowerHorizontalSide_eq_constant_add_bottomEdge
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hw : 0 < w.re)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
      Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
        Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T := by
  have hside :
      Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
        (let M : ℕ := N + 1
        ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) - Complex.I * (T : ℂ))) :=
    Complex.finiteAbelPlana_log_finiteHeightLowerSide_unfold N w T
  have hintegral :
      (let M : ℕ := N + 1
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((x : ℂ) - Complex.I * (T : ℂ))) =
      (let M : ℕ := N + 1
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) - (T : ℂ) * Complex.I) *
          ((Real.pi : ℂ) * Complex.I) +
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) - (T : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) - (T : ℂ) * Complex.I) -
            (Real.pi : ℂ) * Complex.I)) :=
    intervalIntegral.integral_congr
      (fun x _hx =>
        Complex.finiteAbelPlana_lowerHorizontal_integrand_split w x T)
  have hconstant :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) - (T : ℂ) * Complex.I) *
            ((Real.pi : ℂ) * Complex.I))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (0 : ℝ) ((N + 1 : ℕ) : ℝ) := by
    have hpath :
        ContinuousOn
          (fun x : ℝ => ((x : ℂ) - (T : ℂ) * Complex.I))
          (Set.uIcc (0 : ℝ) ((N + 1 : ℕ) : ℝ)) :=
      (Complex.continuous_ofReal.sub continuous_const).continuousOn
    have hsummand :
        ContinuousOn
          (fun x : ℝ =>
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) - (T : ℂ) * Complex.I))
          (Set.uIcc (0 : ℝ) ((N + 1 : ℕ) : ℝ)) := by
      change ContinuousOn
        (fun x : ℝ => Complex.log (w + ((x : ℂ) - (T : ℂ) * Complex.I)))
        (Set.uIcc (0 : ℝ) ((N + 1 : ℕ) : ℝ))
      exact
        (continuous_const.continuousOn.add hpath).clog
          (fun x hx =>
            Complex.finiteAbelPlana_log_lowerHorizontalPath_mem_slitPlane
              N hw T hx)
    exact (hsummand.mul continuousOn_const).intervalIntegrable
  have hremainder :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) - (T : ℂ) * Complex.I) *
            (Complex.finiteAbelPlanaCotangentKernel
                ((x : ℂ) - (T : ℂ) * Complex.I) -
              (Real.pi : ℂ) * Complex.I))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (0 : ℝ) ((N + 1 : ℕ) : ℝ) := by
    have hpath_global :
        Continuous (fun x : ℝ => ((x : ℂ) - (T : ℂ) * Complex.I)) :=
      Complex.continuous_ofReal.sub continuous_const
    have hpath :
        ContinuousOn
          (fun x : ℝ => ((x : ℂ) - (T : ℂ) * Complex.I))
          (Set.uIcc (0 : ℝ) ((N + 1 : ℕ) : ℝ)) :=
      hpath_global.continuousOn
    have hsummand :
        ContinuousOn
          (fun x : ℝ =>
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) - (T : ℂ) * Complex.I))
          (Set.uIcc (0 : ℝ) ((N + 1 : ℕ) : ℝ)) := by
      change ContinuousOn
        (fun x : ℝ => Complex.log (w + ((x : ℂ) - (T : ℂ) * Complex.I)))
        (Set.uIcc (0 : ℝ) ((N + 1 : ℕ) : ℝ))
      exact
        (continuous_const.continuousOn.add hpath).clog
          (fun x hx =>
            Complex.finiteAbelPlana_log_lowerHorizontalPath_mem_slitPlane
              N hw T hx)
    have hkernel :
        Continuous
          (fun x : ℝ =>
            Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) - (T : ℂ) * Complex.I)) := by
      exact continuous_iff_continuousAt.mpr
        (fun x =>
          have hpath_at :
              ContinuousAt
                (fun x : ℝ => ((x : ℂ) - (T : ℂ) * Complex.I)) x :=
            hpath_global.continuousAt (x := x)
          ContinuousAt.comp'
            (f := fun x : ℝ => ((x : ℂ) - (T : ℂ) * Complex.I))
            (g := Complex.finiteAbelPlanaCotangentKernel)
            (Complex.differentiableAt_finiteAbelPlanaCotangentKernel
              (Complex.finiteAbelPlana_log_lowerHorizontalPath_sin_ne_zero
                T hT x)).continuousAt
            hpath_at)
    exact
      (hsummand.mul
        (hkernel.continuousOn.sub continuousOn_const)).intervalIntegrable
  exact
    Eq.trans hside
      (Eq.trans hintegral
        (intervalIntegral.integral_add
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
          hconstant hremainder))

/-- The upper horizontal side splits into its upper-half-plane constant
cotangent part plus the named decaying top horizontal edge. -/
theorem Complex.finiteAbelPlana_log_upperHorizontalSide_eq_constant_add_topEdge
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hw : 0 < w.re)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
      Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
        Complex.finiteAbelPlanaLogTopHorizontalEdge N w T := by
  have hside :
      Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
        (let M : ℕ := N + 1
        ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) + Complex.I * (T : ℂ))) :=
    Complex.finiteAbelPlana_log_finiteHeightUpperSide_unfold N w T
  have hintegral :
      (let M : ℕ := N + 1
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((x : ℂ) + Complex.I * (T : ℂ))) =
      (let M : ℕ := N + 1
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) + (T : ℂ) * Complex.I) *
          (-(Real.pi : ℂ) * Complex.I) +
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) + (T : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) + (T : ℂ) * Complex.I) +
            (Real.pi : ℂ) * Complex.I)) :=
    intervalIntegral.integral_congr
      (fun x _hx =>
        Complex.finiteAbelPlana_upperHorizontal_integrand_split w x T)
  have hconstant :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) + (T : ℂ) * Complex.I) *
            (-(Real.pi : ℂ) * Complex.I))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (0 : ℝ) ((N + 1 : ℕ) : ℝ) := by
    have hpath :
        ContinuousOn
          (fun x : ℝ => ((x : ℂ) + (T : ℂ) * Complex.I))
          (Set.uIcc (0 : ℝ) ((N + 1 : ℕ) : ℝ)) :=
      (Complex.continuous_ofReal.add continuous_const).continuousOn
    have hsummand :
        ContinuousOn
          (fun x : ℝ =>
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) + (T : ℂ) * Complex.I))
          (Set.uIcc (0 : ℝ) ((N + 1 : ℕ) : ℝ)) := by
      change ContinuousOn
        (fun x : ℝ => Complex.log (w + ((x : ℂ) + (T : ℂ) * Complex.I)))
        (Set.uIcc (0 : ℝ) ((N + 1 : ℕ) : ℝ))
      exact
        (continuous_const.continuousOn.add hpath).clog
          (fun x hx =>
            Complex.finiteAbelPlana_log_upperHorizontalPath_mem_slitPlane
              N hw T hx)
    exact (hsummand.mul continuousOn_const).intervalIntegrable
  have hremainder :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) + (T : ℂ) * Complex.I) *
            (Complex.finiteAbelPlanaCotangentKernel
                ((x : ℂ) + (T : ℂ) * Complex.I) +
              (Real.pi : ℂ) * Complex.I))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (0 : ℝ) ((N + 1 : ℕ) : ℝ) := by
    have hpath_global :
        Continuous (fun x : ℝ => ((x : ℂ) + (T : ℂ) * Complex.I)) :=
      Complex.continuous_ofReal.add continuous_const
    have hpath :
        ContinuousOn
          (fun x : ℝ => ((x : ℂ) + (T : ℂ) * Complex.I))
          (Set.uIcc (0 : ℝ) ((N + 1 : ℕ) : ℝ)) :=
      hpath_global.continuousOn
    have hsummand :
        ContinuousOn
          (fun x : ℝ =>
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) + (T : ℂ) * Complex.I))
          (Set.uIcc (0 : ℝ) ((N + 1 : ℕ) : ℝ)) := by
      change ContinuousOn
        (fun x : ℝ => Complex.log (w + ((x : ℂ) + (T : ℂ) * Complex.I)))
        (Set.uIcc (0 : ℝ) ((N + 1 : ℕ) : ℝ))
      exact
        (continuous_const.continuousOn.add hpath).clog
          (fun x hx =>
            Complex.finiteAbelPlana_log_upperHorizontalPath_mem_slitPlane
              N hw T hx)
    have hkernel :
        Continuous
          (fun x : ℝ =>
            Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) + (T : ℂ) * Complex.I)) := by
      exact continuous_iff_continuousAt.mpr
        (fun x =>
          have hpath_at :
              ContinuousAt
                (fun x : ℝ => ((x : ℂ) + (T : ℂ) * Complex.I)) x :=
            hpath_global.continuousAt (x := x)
          ContinuousAt.comp'
            (f := fun x : ℝ => ((x : ℂ) + (T : ℂ) * Complex.I))
            (g := Complex.finiteAbelPlanaCotangentKernel)
            (Complex.differentiableAt_finiteAbelPlanaCotangentKernel
              (Complex.finiteAbelPlana_log_upperHorizontalPath_sin_ne_zero
                T hT x)).continuousAt
            hpath_at)
    exact
      (hsummand.mul
        (hkernel.continuousOn.add continuousOn_const)).intervalIntegrable
  exact
    Eq.trans hside
      (Eq.trans hintegral
        (intervalIntegral.integral_add
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
          hconstant hremainder))

/-- The raw left vertical face together with its adjacent upper horizontal
constant contribution.

This is not asserted to equal the whole real segment.  It is only the oriented
local face that participates in the global Abel-Plana boundary normalization. -/
noncomputable def Complex.finiteAbelPlanaLogLeftBoundaryFace
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
    Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T

/-- The raw right vertical face together with its adjacent lower horizontal
constant contribution. -/
noncomputable def Complex.finiteAbelPlanaLogRightBoundaryFace
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
    Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T

/-- The two raw boundary faces add up to the constant-horizontal plus raw
vertical side expression. -/
theorem Complex.finiteAbelPlana_log_boundaryFaces_sum_eq_constantHorizontal_rawVertical
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLeftBoundaryFace N w T +
        Complex.finiteAbelPlanaLogRightBoundaryFace N w T =
      Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
        Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T := by
  have hleft :
      Complex.finiteAbelPlanaLogLeftBoundaryFace N w T =
        -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T :=
    Eq.refl (Complex.finiteAbelPlanaLogLeftBoundaryFace N w T)
  have hright :
      Complex.finiteAbelPlanaLogRightBoundaryFace N w T =
        Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T :=
    Eq.refl (Complex.finiteAbelPlanaLogRightBoundaryFace N w T)
  have hraw :
      Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T =
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T -
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T :=
    Complex.finiteAbelPlana_log_finiteHeightRawVerticalSideExpression_unfold N w T
  calc
    Complex.finiteAbelPlanaLogLeftBoundaryFace N w T +
        Complex.finiteAbelPlanaLogRightBoundaryFace N w T =
      (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T) +
        (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T) := by
      exact congrArg₂ HAdd.hAdd hleft hright
    _ =
      Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
        Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
          (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T) := by
      exact Complex.finiteAbelPlana_boundaryFace_collect
        (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T)
        (Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T)
        (Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T)
        (Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T)
    _ =
      Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
        Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T := by
      exact congrArg
        (fun z : ℂ =>
          Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
            Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T + z)
        hraw.symm

/-- Unfolding of the raw left boundary face. -/
theorem Complex.finiteAbelPlana_log_leftBoundaryFace_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLeftBoundaryFace N w T =
      -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T := by
  exact Eq.refl (Complex.finiteAbelPlanaLogLeftBoundaryFace N w T)

/-- Unfolding of the raw right boundary face. -/
theorem Complex.finiteAbelPlana_log_rightBoundaryFace_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogRightBoundaryFace N w T =
      Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T := by
  exact Eq.refl (Complex.finiteAbelPlanaLogRightBoundaryFace N w T)

/-- Named lower boundary-face contribution in the coupled Abel-Plana
normalization. -/
noncomputable def Complex.finiteAbelPlanaLogLowerNamedBoundaryFace
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  let M : ℕ := N + 1
  (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
    Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w -
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T

/-- Named upper boundary-face contribution in the coupled Abel-Plana
normalization. -/
noncomputable def Complex.finiteAbelPlanaLogUpperNamedBoundaryFace
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  -Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T

/-- The named Abel-Plana boundary target for the two raw vertical faces. -/
noncomputable def Complex.finiteAbelPlanaLogNamedBoundaryFaceSum
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
    Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T

/-- The two named boundary faces add up to the named Abel-Plana boundary
target. -/
theorem Complex.finiteAbelPlana_log_namedBoundaryFaces_sum_eq_namedBoundary
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T +
        Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T =
      Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T := by
  have hlower :
      Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T =
        (let M : ℕ := N + 1;
          (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
            Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w -
            Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T) :=
    Eq.refl (Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T)
  have hupper :
      Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T =
        -Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T :=
    Eq.refl (Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T)
  have hreal :
      Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w =
        (let M : ℕ := N + 1;
          (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
            Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w) :=
    Eq.refl (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w)
  have hvertical :
      Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T =
        -Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
          Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T :=
    Complex.finiteAbelPlana_log_finiteHeightNamedVerticalSideExpression_unfold N w T
  have htarget :
      Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T =
        Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
          Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T :=
    Eq.refl (Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T)
  calc
    Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T +
        Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T =
      ((let M : ℕ := N + 1;
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w -
          Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T) +
        (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)) := by
      exact congrArg₂ HAdd.hAdd hlower hupper
    _ =
      (let M : ℕ := N + 1;
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w) +
        (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
          Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T) := by
      exact Complex.finiteAbelPlana_namedBoundary_collect
        (let M : ℕ := N + 1;
          (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
            Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w)
        (Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)
        (Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)
    _ =
      Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
        Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T := by
      exact congrArg₂ HAdd.hAdd hreal.symm hvertical.symm
    _ = Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T := by
      exact htarget.symm

/-- Constant-kernel part of the left vertical side after splitting at the real
axis.  On the lower half-plane the cotangent constant is `π i`; on the upper
half-plane it is `-π i`. -/
noncomputable def Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide
    (w : ℂ)
    (T : ℝ) : ℂ :=
  (∫ y : ℝ in (-T)..(0 : ℝ),
    Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
      ((Real.pi : ℂ) * Complex.I)) +
  (∫ y : ℝ in (0 : ℝ)..T,
    Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
      (-(Real.pi : ℂ) * Complex.I))

/-- Exponential-remainder part of the left vertical side after splitting at
the real axis. -/
noncomputable def Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSide
    (w : ℂ)
    (T : ℝ) : ℂ :=
  (∫ y : ℝ in (-T)..(0 : ℝ),
    Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
      (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) -
        (Real.pi : ℂ) * Complex.I)) +
  (∫ y : ℝ in (0 : ℝ)..T,
    Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
      (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) +
        (Real.pi : ℂ) * Complex.I))

/-- Constant-kernel part of the right vertical side after splitting at the
real axis. -/
noncomputable def Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  let M : ℕ := N + 1
  (∫ y : ℝ in (-T)..(0 : ℝ),
    Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
      ((Real.pi : ℂ) * Complex.I)) +
  (∫ y : ℝ in (0 : ℝ)..T,
    Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
      (-(Real.pi : ℂ) * Complex.I))

/-- Exponential-remainder part of the right vertical side after splitting at
the real axis. -/
noncomputable def Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSide
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  let M : ℕ := N + 1
  (∫ y : ℝ in (-T)..(0 : ℝ),
    Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
      (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (y : ℂ)) -
        (Real.pi : ℂ) * Complex.I)) +
  (∫ y : ℝ in (0 : ℝ)..T,
    Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
      (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (y : ℂ)) +
        (Real.pi : ℂ) * Complex.I))

/-- Principal-value constant-kernel part of the left vertical side. -/
noncomputable def Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  (∫ y : ℝ in (-T)..(-ε),
    Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
      ((Real.pi : ℂ) * Complex.I)) +
  ∫ y : ℝ in ε..T,
    Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
      (-(Real.pi : ℂ) * Complex.I)

/-- Principal-value exponential-remainder part of the left vertical side. -/
noncomputable def Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePV
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  (∫ y : ℝ in (-T)..(-ε),
    Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
      (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) -
        (Real.pi : ℂ) * Complex.I)) +
  ∫ y : ℝ in ε..T,
    Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
      (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) +
        (Real.pi : ℂ) * Complex.I)

/-- Principal-value constant-kernel part of the right vertical side. -/
noncomputable def Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  let M : ℕ := N + 1
  (∫ y : ℝ in (-T)..(-ε),
    Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
      ((Real.pi : ℂ) * Complex.I)) +
  ∫ y : ℝ in ε..T,
    Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
      (-(Real.pi : ℂ) * Complex.I)

/-- Principal-value exponential-remainder part of the right vertical side. -/
noncomputable def Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePV
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  let M : ℕ := N + 1
  (∫ y : ℝ in (-T)..(-ε),
    Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
      (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (y : ℂ)) -
        (Real.pi : ℂ) * Complex.I)) +
  ∫ y : ℝ in ε..T,
    Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
      (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (y : ℂ)) +
        (Real.pi : ℂ) * Complex.I)

/-- Residue-normalized principal-value exponential-remainder part of the left
vertical side.

The raw rectangle side is scaled by `(2πi)⁻¹` before it is compared with the
Abel-Plana logarithmic-jump integral.  This definition keeps that normalization
visible at the owner level. -/
noncomputable def Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioc ε T,
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (((-Complex.I) *
          (Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
            (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
              (Real.pi : ℂ) * Complex.I))) +
        ((-Complex.I) *
          (Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
              (Real.pi : ℂ) * Complex.I))))

/-- Residue-normalized principal-value exponential-remainder part of the right
endpoint vertical side. -/
noncomputable def Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  let M : ℕ := N + 1
  ∫ t : ℝ in Set.Ioc ε T,
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ((Complex.I *
          (Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
              (Real.pi : ℂ) * Complex.I))) +
        (Complex.I *
          (Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
              (Real.pi : ℂ) * Complex.I))))

/-- Principal-value left boundary face with indentation radius `ε`. -/
noncomputable def Complex.finiteAbelPlanaLogLeftBoundaryFacePV
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
    Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ε

/-- Principal-value right boundary face with indentation radius `ε`. -/
noncomputable def Complex.finiteAbelPlanaLogRightBoundaryFacePV
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
    Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ε

/-- Residue-normalized principal-value left endpoint boundary face after
splitting into the constant cotangent primitive and the normalized exponential
remainder. -/
noncomputable def Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
      Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε) +
      Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε

/-- Unfolding of the normalized left principal-value boundary face. -/
theorem Complex.finiteAbelPlana_log_leftBoundaryFacePVNormalized_unfold
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) :
    Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
          Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε) +
          Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε :=
  Eq.refl (Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε)

/-- Residue-normalized principal-value right endpoint boundary face after
splitting into the constant cotangent primitive and the normalized exponential
remainder. -/
noncomputable def Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
      Complex.I * Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε) +
      Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε

/-- Unfolding of the normalized right principal-value boundary face. -/
theorem Complex.finiteAbelPlana_log_rightBoundaryFacePVNormalized_unfold
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) :
    Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
          Complex.I * Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε) +
          Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε :=
  Eq.refl (Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε)

/-- Pointwise lower-half left vertical cotangent split. -/
theorem Complex.finiteAbelPlana_log_leftVertical_lower_pointwise_split
    (w : ℂ)
    (y : ℝ) :
    Complex.finiteAbelPlanaLogRectangleIntegrand w (Complex.I * (y : ℂ)) =
      Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
        ((Real.pi : ℂ) * Complex.I) +
    Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) -
          (Real.pi : ℂ) * Complex.I) := by
  exact
    Eq.trans
      (Complex.finiteAbelPlanaLogRectangleIntegrand_unfold
        w (Complex.I * (y : ℂ)))
      (Complex.mul_eq_mul_add_mul_sub
        (Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)))
        (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)))
        ((Real.pi : ℂ) * Complex.I))

/-- Pointwise upper-half left vertical cotangent split. -/
theorem Complex.finiteAbelPlana_log_leftVertical_upper_pointwise_split
    (w : ℂ)
    (y : ℝ) :
    Complex.finiteAbelPlanaLogRectangleIntegrand w (Complex.I * (y : ℂ)) =
      Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
        (-(Real.pi : ℂ) * Complex.I) +
    Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) +
          (Real.pi : ℂ) * Complex.I) := by
  exact
    Eq.trans
      (Complex.finiteAbelPlanaLogRectangleIntegrand_unfold
        w (Complex.I * (y : ℂ)))
      (Eq.trans
        (Complex.mul_eq_mul_neg_add_mul_add
          (Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)))
          (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)))
          ((Real.pi : ℂ) * Complex.I))
        (Complex.mul_neg_product_constant_add_normalize
          (Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)))
          (Real.pi : ℂ)
          Complex.I
          (Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) +
              (Real.pi : ℂ) * Complex.I))))

/-- Pointwise lower-half right vertical cotangent split. -/
theorem Complex.finiteAbelPlana_log_rightVertical_lower_pointwise_split
    (N : ℕ)
    (w : ℂ)
    (y : ℝ) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogRectangleIntegrand w
        ((M : ℂ) + Complex.I * (y : ℂ)) =
      Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
        ((Real.pi : ℂ) * Complex.I) +
      Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (y : ℂ)) -
          (Real.pi : ℂ) * Complex.I) := by
  exact
    Eq.trans
      (Complex.finiteAbelPlanaLogRectangleIntegrand_unfold
        w (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)))
      (Complex.mul_eq_mul_add_mul_sub
        (Complex.finiteAbelPlanaLogSummand w (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)))
        (Complex.finiteAbelPlanaCotangentKernel (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)))
        ((Real.pi : ℂ) * Complex.I))

/-- Pointwise upper-half right vertical cotangent split. -/
theorem Complex.finiteAbelPlana_log_rightVertical_upper_pointwise_split
    (N : ℕ)
    (w : ℂ)
    (y : ℝ) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogRectangleIntegrand w
        ((M : ℂ) + Complex.I * (y : ℂ)) =
      Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
        (-(Real.pi : ℂ) * Complex.I) +
      Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (y : ℂ)) +
          (Real.pi : ℂ) * Complex.I) := by
  exact
    Eq.trans
      (Complex.finiteAbelPlanaLogRectangleIntegrand_unfold
        w (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)))
      (Eq.trans
        (Complex.mul_eq_mul_neg_add_mul_add
          (Complex.finiteAbelPlanaLogSummand w (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)))
          (Complex.finiteAbelPlanaCotangentKernel (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)))
          ((Real.pi : ℂ) * Complex.I))
        (Complex.mul_neg_product_constant_add_normalize
          (Complex.finiteAbelPlanaLogSummand w (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)))
          (Real.pi : ℂ)
          Complex.I
          (Complex.finiteAbelPlanaLogSummand w (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) +
              (Real.pi : ℂ) * Complex.I))))

/-- The lower named boundary face unfolded into real-segment, endpoint, and
lower vertical integral pieces. -/
theorem Complex.finiteAbelPlana_log_lowerNamedBoundaryFace_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T =
      (let M : ℕ := N + 1;
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w -
          Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T) := by
  exact Eq.refl (Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T)

/-- The upper named boundary face unfolds to minus the upper vertical
integral. -/
theorem Complex.finiteAbelPlana_log_upperNamedBoundaryFace_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T =
      -Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T := by
  exact Eq.refl (Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T)

/-- The left vertical logarithmic path lies in the principal slit plane in
the open right half-plane. -/
theorem Complex.finiteAbelPlana_log_leftVerticalPath_mem_slitPlane
    {w : ℂ}
    (hw : 0 < w.re)
    (y : ℝ) :
    w + Complex.I * (y : ℂ) ∈ Complex.slitPlane := by
  have hpath :
      w + Complex.I * (y : ℂ) =
        w + (y : ℂ) * Complex.I := by
    exact congrArg (fun z : ℂ => w + z)
      (mul_comm Complex.I (y : ℂ))
  have hre : 0 < (w + Complex.I * (y : ℂ)).re := by
    have hre_aligned :
        (w + (y : ℂ) * Complex.I).re = w.re :=
      Complex.add_real_mul_I_re w y
    exact hpath ▸ (hre_aligned.symm ▸ hw)
  exact Complex.mem_slitPlane_iff.mpr (Or.inl hre)

/-- The right endpoint vertical logarithmic path lies in the principal slit
plane in the open right half-plane. -/
theorem Complex.finiteAbelPlana_log_rightVerticalPath_mem_slitPlane
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (y : ℝ) :
    w + ((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ) ∈ Complex.slitPlane := by
  have hN_nonneg : 0 ≤ (((N + 1 : ℕ) : ℝ)) := Nat.cast_nonneg (N + 1)
  have hre :
      0 < (w + ((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)).re := by
    have hpath :
        w + ((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ) =
          (w + ((N + 1 : ℕ) : ℂ)) + (y : ℂ) * Complex.I := by
      exact congrArg (fun z : ℂ => w + ((N + 1 : ℕ) : ℂ) + z)
        (mul_comm Complex.I (y : ℂ))
    have hre_aligned :
        ((w + ((N + 1 : ℕ) : ℂ)) + (y : ℂ) * Complex.I).re =
          (w + ((N + 1 : ℕ) : ℂ)).re :=
      Complex.add_real_mul_I_re (w + ((N + 1 : ℕ) : ℂ)) y
    have hre_shift :
        (w + ((N + 1 : ℕ) : ℂ)).re =
          w.re + (((N + 1 : ℕ) : ℝ)) := by
      calc
        (w + ((N + 1 : ℕ) : ℂ)).re =
            w.re + (((N + 1 : ℕ) : ℂ)).re :=
          Complex.add_re w (((N + 1 : ℕ) : ℂ))
        _ = w.re + (((N + 1 : ℕ) : ℝ)) := by
          exact congrArg (fun r : ℝ => w.re + r)
            (Complex.ofReal_re (((N + 1 : ℕ) : ℝ)))
    exact
      hpath ▸
        (hre_aligned.symm ▸
          (hre_shift.symm ▸ add_pos_of_pos_of_nonneg hw hN_nonneg))
  exact Complex.mem_slitPlane_iff.mpr (Or.inl hre)

/-- Continuity of the left vertical logarithmic summand path in the open
right half-plane. -/
theorem Complex.continuous_finiteAbelPlana_log_leftVerticalSummand
    {w : ℂ}
    (hw : 0 < w.re) :
    Continuous
      (fun y : ℝ =>
        Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ))) := by
  change Continuous (fun y : ℝ => Complex.log (w + Complex.I * (y : ℂ)))
  exact
    (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).clog
      (fun y => Complex.finiteAbelPlana_log_leftVerticalPath_mem_slitPlane hw y)

/-- Continuity of the right endpoint vertical logarithmic summand path in the
open right half-plane. -/
theorem Complex.continuous_finiteAbelPlana_log_rightVerticalSummand
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re) :
    Continuous
      (fun y : ℝ =>
        Complex.finiteAbelPlanaLogSummand w
          (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ))) := by
  change Continuous
    (fun y : ℝ =>
      Complex.log (w + (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ))))
  have hnormalized :
      Continuous
        (fun y : ℝ =>
          Complex.log (w + ((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ))) :=
    ((continuous_const.add continuous_const).add
        (continuous_const.mul Complex.continuous_ofReal)).clog
      (fun y => Complex.finiteAbelPlana_log_rightVerticalPath_mem_slitPlane N hw y)
  exact hnormalized.congr
    (fun y =>
      congrArg Complex.log
        (add_assoc w (((N + 1 : ℕ) : ℂ)) (Complex.I * (y : ℂ))))

/-- FTC for a right vertical constant-kernel segment of the logarithmic
primitive. -/
theorem Complex.finiteAbelPlana_log_rightVerticalConstantPrimitive_integral
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (a b : ℝ) :
    let M : ℕ := N + 1
    ∫ y : ℝ in a..b,
        Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
          ((Real.pi : ℂ) * Complex.I) =
      (Real.pi : ℂ) *
        (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (b : ℂ)) -
          Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (a : ℂ))) := by
  intro M
  let P : ℂ := (Real.pi : ℂ)
  let c : ℂ := (M : ℂ)
  let F : ℝ → ℂ := fun y : ℝ =>
    P * Complex.finiteAbelPlanaLogComplexPrimitive w ((y : ℂ) * Complex.I + c)
  have hderiv :
      ∀ y ∈ Set.uIcc a b,
        HasDerivAt F
          (Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
            ((Real.pi : ℂ) * Complex.I))
          y := by
    intro y _hy
    have hy_arg :
        (y : ℂ) * Complex.I + c = (M : ℂ) + Complex.I * (y : ℂ) := by
      calc
        (y : ℂ) * Complex.I + c =
            Complex.I * (y : ℂ) + c := by
          exact congrArg (fun z : ℂ => z + c) (mul_comm (y : ℂ) Complex.I)
        _ = c + Complex.I * (y : ℂ) := by
          exact add_comm (Complex.I * (y : ℂ)) c
        _ = (M : ℂ) + Complex.I * (y : ℂ) := by
          exact Eq.refl _
    have hslit :
        w + ((y : ℂ) * Complex.I + c) ∈ Complex.slitPlane := by
      have hpath :
          w + ((M : ℂ) + Complex.I * (y : ℂ)) =
            w + (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) := by
        exact Eq.refl _
      exact hy_arg ▸
        (hpath ▸
          Complex.finiteAbelPlana_log_rightVerticalPath_mem_slitPlane N hw y)
    have hline :
        HasDerivAt
          (fun s : ℝ =>
            Complex.finiteAbelPlanaLogComplexPrimitive w
              ((s : ℂ) * Complex.I + c))
          (Complex.I *
            Complex.finiteAbelPlanaLogSummand w ((y : ℂ) * Complex.I + c))
          y :=
      Complex.hasDerivAt_finiteAbelPlanaLogComplexPrimitive_line
        w c Complex.I hslit
    have hscaled :
        HasDerivAt F
          (P *
            (Complex.I *
              Complex.finiteAbelPlanaLogSummand w ((y : ℂ) * Complex.I + c)))
          y :=
      hline.const_mul P
    have hvalue :
        P *
            (Complex.I *
              Complex.finiteAbelPlanaLogSummand w ((y : ℂ) * Complex.I + c)) =
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
            ((Real.pi : ℂ) * Complex.I) := by
      have hsummand :
          Complex.finiteAbelPlanaLogSummand w ((y : ℂ) * Complex.I + c) =
            Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) := by
        exact congrArg (fun z : ℂ => Complex.finiteAbelPlanaLogSummand w z) hy_arg
      calc
        P *
            (Complex.I *
              Complex.finiteAbelPlanaLogSummand w ((y : ℂ) * Complex.I + c)) =
            P *
              (Complex.I *
                Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ))) := by
          exact congrArg
            (fun z : ℂ => P * (Complex.I * z))
            hsummand
        _ =
            (P * Complex.I) *
              Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) := by
          exact (mul_assoc P Complex.I
            (Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)))).symm
        _ =
            Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
              (P * Complex.I) := by
          exact mul_comm (P * Complex.I)
            (Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)))
        _ =
            Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
              ((Real.pi : ℂ) * Complex.I) := by
          exact Eq.refl _
    exact hvalue ▸ hscaled
  have hcont :
      ContinuousOn
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
            ((Real.pi : ℂ) * Complex.I))
        (Set.uIcc a b) := by
    intro y _hy
    exact
      ((Complex.continuous_finiteAbelPlana_log_rightVerticalSummand N hw).continuousAt.mul
        continuousAt_const).continuousWithinAt
  have hint :
      IntervalIntegrable
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
            ((Real.pi : ℂ) * Complex.I))
        volume a b :=
    hcont.intervalIntegrable
  have hFTC :
      ∫ y : ℝ in a..b,
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
            ((Real.pi : ℂ) * Complex.I) =
        F b - F a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hendpoints :
      F b - F a =
        (Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (b : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (a : ℂ))) := by
    have hb :
        (b : ℂ) * Complex.I + c = (M : ℂ) + Complex.I * (b : ℂ) := by
      calc
        (b : ℂ) * Complex.I + c =
            Complex.I * (b : ℂ) + c := by
          exact congrArg (fun z : ℂ => z + c) (mul_comm (b : ℂ) Complex.I)
        _ = c + Complex.I * (b : ℂ) := by
          exact add_comm (Complex.I * (b : ℂ)) c
        _ = (M : ℂ) + Complex.I * (b : ℂ) := by
          exact Eq.refl _
    have ha :
        (a : ℂ) * Complex.I + c = (M : ℂ) + Complex.I * (a : ℂ) := by
      calc
        (a : ℂ) * Complex.I + c =
            Complex.I * (a : ℂ) + c := by
          exact congrArg (fun z : ℂ => z + c) (mul_comm (a : ℂ) Complex.I)
        _ = c + Complex.I * (a : ℂ) := by
          exact add_comm (Complex.I * (a : ℂ)) c
        _ = (M : ℂ) + Complex.I * (a : ℂ) := by
          exact Eq.refl _
    calc
      F b - F a =
          P * Complex.finiteAbelPlanaLogComplexPrimitive w ((b : ℂ) * Complex.I + c) -
            P * Complex.finiteAbelPlanaLogComplexPrimitive w ((a : ℂ) * Complex.I + c) := by
        exact Eq.refl _
      _ =
          P * Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (b : ℂ)) -
            P * Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (a : ℂ)) := by
        exact congrArg₂ Sub.sub
          (congrArg (fun z : ℂ => P * Complex.finiteAbelPlanaLogComplexPrimitive w z) hb)
          (congrArg (fun z : ℂ => P * Complex.finiteAbelPlanaLogComplexPrimitive w z) ha)
      _ =
          P *
            (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (b : ℂ)) -
              Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (a : ℂ))) := by
        exact (mul_sub P
          (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (b : ℂ)))
          (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (a : ℂ)))).symm
      _ =
          (Real.pi : ℂ) *
            (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (b : ℂ)) -
              Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (a : ℂ))) := by
        exact Eq.refl _
  exact Eq.trans hFTC hendpoints

/-- Multiplication by the upper-half-plane vertical constant `-π i` is the
negative of multiplication by the lower-half-plane vertical constant `π i`. -/
theorem Complex.finiteAbelPlana_mul_neg_pi_I_eq_neg_mul_pi_I
    (a : ℂ) :
    a * (-(Real.pi : ℂ) * Complex.I) =
      -(a * ((Real.pi : ℂ) * Complex.I)) := by
  have hconst :
      (-(Real.pi : ℂ) * Complex.I) =
        -((Real.pi : ℂ) * Complex.I) := by
    exact neg_mul (Real.pi : ℂ) Complex.I
  calc
    a * (-(Real.pi : ℂ) * Complex.I) =
        a * (-((Real.pi : ℂ) * Complex.I)) := by
      exact congrArg (fun z : ℂ => a * z) hconst
    _ = -(a * ((Real.pi : ℂ) * Complex.I)) := by
      exact mul_neg a ((Real.pi : ℂ) * Complex.I)

/-- Interval-integral form of the upper-half-plane vertical sign
normalization. -/
theorem Complex.finiteAbelPlana_integral_mul_neg_pi_I_eq_neg_integral_mul_pi_I
    (f : ℝ → ℂ)
    (a b : ℝ) :
    ∫ y : ℝ in a..b, f y * (-(Real.pi : ℂ) * Complex.I) =
      -(∫ y : ℝ in a..b, f y * ((Real.pi : ℂ) * Complex.I)) := by
  have hpoint :
      Set.EqOn
        (fun y : ℝ => f y * (-(Real.pi : ℂ) * Complex.I))
        (fun y : ℝ => -(f y * ((Real.pi : ℂ) * Complex.I)))
        [[a, b]] := by
    intro y _hy
    exact Complex.finiteAbelPlana_mul_neg_pi_I_eq_neg_mul_pi_I (f y)
  calc
    ∫ y : ℝ in a..b, f y * (-(Real.pi : ℂ) * Complex.I) =
        ∫ y : ℝ in a..b, -(f y * ((Real.pi : ℂ) * Complex.I)) := by
      exact intervalIntegral.integral_congr hpoint
    _ = -(∫ y : ℝ in a..b, f y * ((Real.pi : ℂ) * Complex.I)) := by
      exact intervalIntegral.integral_neg

/-- Left vertical constant side evaluated by the logarithmic primitive. -/
theorem Complex.finiteAbelPlana_log_leftVerticalCotangentConstantSide_eq_primitive
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T =
      (Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (0 : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * ((-T : ℝ) : ℂ))) -
        (Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (T : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (0 : ℂ))) := by
  let f : ℝ → ℂ := fun y : ℝ =>
    Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ))
  have hfirst :
      ∫ y : ℝ in (-T)..(0 : ℝ),
          f y * ((Real.pi : ℂ) * Complex.I) =
        (Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * ((0 : ℝ) : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * ((-T : ℝ) : ℂ))) :=
    Complex.finiteAbelPlana_log_leftVerticalConstantPrimitive_integral
      hw (-T) 0
  have hsecond_pos :
      ∫ y : ℝ in (0 : ℝ)..T,
          f y * ((Real.pi : ℂ) * Complex.I) =
        (Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (T : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * ((0 : ℝ) : ℂ))) :=
    Complex.finiteAbelPlana_log_leftVerticalConstantPrimitive_integral
      hw 0 T
  have hsecond_neg :
      ∫ y : ℝ in (0 : ℝ)..T,
          f y * (-(Real.pi : ℂ) * Complex.I) =
        -((Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (T : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * ((0 : ℝ) : ℂ)))) := by
    calc
      ∫ y : ℝ in (0 : ℝ)..T,
          f y * (-(Real.pi : ℂ) * Complex.I) =
          -(∫ y : ℝ in (0 : ℝ)..T,
              f y * ((Real.pi : ℂ) * Complex.I)) := by
        exact
          Complex.finiteAbelPlana_integral_mul_neg_pi_I_eq_neg_integral_mul_pi_I
            f 0 T
      _ =
          -((Real.pi : ℂ) *
            (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (T : ℂ)) -
              Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * ((0 : ℝ) : ℂ)))) := by
        exact congrArg Neg.neg hsecond_pos
  calc
    Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T =
        (∫ y : ℝ in (-T)..(0 : ℝ),
          f y * ((Real.pi : ℂ) * Complex.I)) +
        (∫ y : ℝ in (0 : ℝ)..T,
          f y * (-(Real.pi : ℂ) * Complex.I)) := by
      rfl
    _ =
        ((Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * ((0 : ℝ) : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * ((-T : ℝ) : ℂ)))) +
        (-((Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (T : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * ((0 : ℝ) : ℂ))))) := by
      exact congrArg₂ HAdd.hAdd hfirst hsecond_neg
    _ =
        (Real.pi : ℂ) *
            (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (0 : ℂ)) -
              Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * ((-T : ℝ) : ℂ))) -
          (Real.pi : ℂ) *
            (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (T : ℂ)) -
              Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (0 : ℂ))) := by
      exact
        (sub_eq_add_neg
          ((Real.pi : ℂ) *
            (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (0 : ℂ)) -
              Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * ((-T : ℝ) : ℂ))))
          ((Real.pi : ℂ) *
            (Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (T : ℂ)) -
              Complex.finiteAbelPlanaLogComplexPrimitive w (Complex.I * (0 : ℂ))))).symm

/-- Right vertical constant side evaluated by the logarithmic primitive. -/
theorem Complex.finiteAbelPlana_log_rightVerticalCotangentConstantSide_eq_primitive
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T =
      (Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (0 : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * ((-T : ℝ) : ℂ))) -
        (Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (T : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (0 : ℂ))) := by
  intro M
  let f : ℝ → ℂ := fun y : ℝ =>
    Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ))
  have hfirst :
      ∫ y : ℝ in (-T)..(0 : ℝ),
          f y * ((Real.pi : ℂ) * Complex.I) =
        (Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * ((-T : ℝ) : ℂ))) :=
    Complex.finiteAbelPlana_log_rightVerticalConstantPrimitive_integral
      N hw (-T) 0
  have hsecond_pos :
      ∫ y : ℝ in (0 : ℝ)..T,
          f y * ((Real.pi : ℂ) * Complex.I) =
        (Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (T : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * ((0 : ℝ) : ℂ))) :=
    Complex.finiteAbelPlana_log_rightVerticalConstantPrimitive_integral
      N hw 0 T
  have hsecond_neg :
      ∫ y : ℝ in (0 : ℝ)..T,
          f y * (-(Real.pi : ℂ) * Complex.I) =
        -((Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (T : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * ((0 : ℝ) : ℂ)))) := by
    calc
      ∫ y : ℝ in (0 : ℝ)..T,
          f y * (-(Real.pi : ℂ) * Complex.I) =
          -(∫ y : ℝ in (0 : ℝ)..T,
              f y * ((Real.pi : ℂ) * Complex.I)) := by
        exact
          Complex.finiteAbelPlana_integral_mul_neg_pi_I_eq_neg_integral_mul_pi_I
            f 0 T
      _ =
          -((Real.pi : ℂ) *
            (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (T : ℂ)) -
              Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * ((0 : ℝ) : ℂ)))) := by
        exact congrArg Neg.neg hsecond_pos
  calc
    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T =
        (∫ y : ℝ in (-T)..(0 : ℝ),
          f y * ((Real.pi : ℂ) * Complex.I)) +
        (∫ y : ℝ in (0 : ℝ)..T,
          f y * (-(Real.pi : ℂ) * Complex.I)) := by
      rfl
    _ =
        ((Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * ((-T : ℝ) : ℂ)))) +
        (-((Real.pi : ℂ) *
          (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (T : ℂ)) -
            Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * ((0 : ℝ) : ℂ))))) := by
      exact congrArg₂ HAdd.hAdd hfirst hsecond_neg
    _ =
        (Real.pi : ℂ) *
            (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (0 : ℂ)) -
              Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * ((-T : ℝ) : ℂ))) -
          (Real.pi : ℂ) *
            (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (T : ℂ)) -
              Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (0 : ℂ))) := by
      exact
        (sub_eq_add_neg
          ((Real.pi : ℂ) *
            (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (0 : ℂ)) -
              Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * ((-T : ℝ) : ℂ))))
          ((Real.pi : ℂ) *
            (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (T : ℂ)) -
              Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℂ) + Complex.I * (0 : ℂ))))).symm

/-- Normalization by `(2πi)⁻¹` halves a term carrying one `πi` factor. -/
theorem Complex.finiteAbelPlana_two_pi_I_inv_mul_pi_I_mul
    (z : ℂ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (((Real.pi : ℂ) * Complex.I) * z)) =
      z / (2 : ℂ) := by
  let p : ℂ := (Real.pi : ℂ) * Complex.I
  have hp : p ≠ 0 :=
    mul_ne_zero
      ((Complex.ofReal_ne_zero).mpr Real.pi_ne_zero)
      Complex.I_ne_zero
  have hden :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) = (2 : ℂ) * p := by
    exact mul_assoc (2 : ℂ) (Real.pi : ℂ) Complex.I
  calc
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (((Real.pi : ℂ) * Complex.I) * z)) =
        ((2 : ℂ) * p)⁻¹ * (p * z) := by
      exact
        congrArg₂ HMul.hMul
          (congrArg Inv.inv hden)
          (Eq.refl (p * z))
    _ = (p * z) * ((2 : ℂ) * p)⁻¹ := by
      exact mul_comm ((2 : ℂ) * p)⁻¹ (p * z)
    _ = (p * z) / ((2 : ℂ) * p) := by
      exact (div_eq_mul_inv (p * z) ((2 : ℂ) * p)).symm
    _ = (z * p) / ((2 : ℂ) * p) := by
      exact congrArg (fun u : ℂ => u / ((2 : ℂ) * p)) (mul_comm p z)
    _ = z / (2 : ℂ) := by
      exact mul_div_mul_right z (2 : ℂ) hp

/-- Right-factor form of the `(2πi)⁻¹` normalization. -/
theorem Complex.finiteAbelPlana_two_pi_I_inv_mul_mul_pi_I
    (z : ℂ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (z * ((Real.pi : ℂ) * Complex.I))) =
      z / (2 : ℂ) := by
  have hcomm :
      z * ((Real.pi : ℂ) * Complex.I) =
        ((Real.pi : ℂ) * Complex.I) * z :=
    mul_comm z ((Real.pi : ℂ) * Complex.I)
  calc
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (z * ((Real.pi : ℂ) * Complex.I))) =
        (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (((Real.pi : ℂ) * Complex.I) * z)) := by
      exact congrArg
        (fun u : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * u)
        hcomm
    _ = z / (2 : ℂ) :=
      Complex.finiteAbelPlana_two_pi_I_inv_mul_pi_I_mul z

/-- Left constant-face packet algebra after primitive evaluation.

The upper horizontal constant side contributes the upper-left to upper-right
primitive difference with factor `-πi`; the left vertical constant side
contributes the two left vertical half-lines.  After orienting the normalized
left boundary packet, only the lower-left/upper-right height corners and twice
the left real endpoint remain. -/
theorem Complex.finiteAbelPlana_leftConstantPacket_normalized_of_primitives
    (upper lowerVertical leftReal lowerLeft upperLeft upperRight : ℂ)
    (hupper :
      upper = (upperRight - upperLeft) * (-(Real.pi : ℂ) * Complex.I))
    (hleft :
      lowerVertical =
        (Real.pi : ℂ) * (leftReal - lowerLeft) -
          (Real.pi : ℂ) * (upperLeft - leftReal)) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (-upper - Complex.I * lowerVertical) =
      (upperRight + lowerLeft - (leftReal + leftReal)) / (2 : ℂ) := by
  let p : ℂ := (Real.pi : ℂ) * Complex.I
  let packet : ℂ := upperRight + lowerLeft - (leftReal + leftReal)
  have hupper_oriented :
      -upper = (upperRight - upperLeft) * p := by
    have hneg_factor :
        (-(Real.pi : ℂ) * Complex.I) = -p := by
      exact neg_mul (Real.pi : ℂ) Complex.I
    calc
      -upper =
          -((upperRight - upperLeft) * (-(Real.pi : ℂ) * Complex.I)) := by
        exact congrArg Neg.neg hupper
      _ = -((upperRight - upperLeft) * (-p)) := by
        exact congrArg
          (fun z : ℂ => -((upperRight - upperLeft) * z))
          hneg_factor
      _ = -(-(upperRight - upperLeft) * p) := by
        exact congrArg Neg.neg (mul_neg (upperRight - upperLeft) p)
      _ = (upperRight - upperLeft) * p := by
        exact neg_neg ((upperRight - upperLeft) * p)
  have hleft_oriented :
      -(Complex.I * lowerVertical) =
        (upperLeft - leftReal + (lowerLeft - leftReal)) * p := by
    have hI_pi :
        Complex.I * (Real.pi : ℂ) = p := by
      exact mul_comm Complex.I (Real.pi : ℂ)
    have hI_left :
        Complex.I * lowerVertical =
          p * (leftReal - lowerLeft) -
            p * (upperLeft - leftReal) := by
      calc
        Complex.I * lowerVertical =
            Complex.I *
              ((Real.pi : ℂ) * (leftReal - lowerLeft) -
                (Real.pi : ℂ) * (upperLeft - leftReal)) := by
          exact congrArg (fun z : ℂ => Complex.I * z) hleft
        _ =
            Complex.I * ((Real.pi : ℂ) * (leftReal - lowerLeft)) -
              Complex.I * ((Real.pi : ℂ) * (upperLeft - leftReal)) := by
          exact mul_sub Complex.I
            ((Real.pi : ℂ) * (leftReal - lowerLeft))
            ((Real.pi : ℂ) * (upperLeft - leftReal))
        _ =
            (Complex.I * (Real.pi : ℂ)) * (leftReal - lowerLeft) -
              (Complex.I * (Real.pi : ℂ)) * (upperLeft - leftReal) := by
          exact congrArg₂ Sub.sub
            (mul_assoc Complex.I (Real.pi : ℂ) (leftReal - lowerLeft))
            (mul_assoc Complex.I (Real.pi : ℂ) (upperLeft - leftReal))
        _ =
            p * (leftReal - lowerLeft) -
              p * (upperLeft - leftReal) := by
          exact congrArg₂ Sub.sub
            (congrArg (fun z : ℂ => z * (leftReal - lowerLeft)) hI_pi)
            (congrArg (fun z : ℂ => z * (upperLeft - leftReal)) hI_pi)
    have hleft_as_p :
        p * (leftReal - lowerLeft) -
            p * (upperLeft - leftReal) =
          p * ((leftReal - lowerLeft) - (upperLeft - leftReal)) := by
      exact
        (mul_sub p (leftReal - lowerLeft) (upperLeft - leftReal)).symm
    have hneg_inside :
        -((leftReal - lowerLeft) - (upperLeft - leftReal)) =
          upperLeft - leftReal + (lowerLeft - leftReal) := by
      calc
        -((leftReal - lowerLeft) - (upperLeft - leftReal)) =
            (upperLeft - leftReal) - (leftReal - lowerLeft) := by
          exact neg_sub (leftReal - lowerLeft) (upperLeft - leftReal)
        _ =
            (upperLeft - leftReal) + -(leftReal - lowerLeft) := by
          exact sub_eq_add_neg (upperLeft - leftReal) (leftReal - lowerLeft)
        _ =
            (upperLeft - leftReal) + (lowerLeft - leftReal) := by
          have hneg_left :
              -(leftReal - lowerLeft) = lowerLeft - leftReal := by
            exact neg_sub leftReal lowerLeft
          exact congrArg
            (fun z : ℂ => (upperLeft - leftReal) + z)
            hneg_left
        _ =
            upperLeft - leftReal + (lowerLeft - leftReal) := by
          rfl
    calc
      -(Complex.I * lowerVertical) =
          -(p * ((leftReal - lowerLeft) - (upperLeft - leftReal))) := by
        exact congrArg Neg.neg (Eq.trans hI_left hleft_as_p)
      _ =
          p * (-((leftReal - lowerLeft) - (upperLeft - leftReal))) := by
        exact (mul_neg p ((leftReal - lowerLeft) - (upperLeft - leftReal))).symm
      _ =
          p * (upperLeft - leftReal + (lowerLeft - leftReal)) := by
        exact congrArg (fun z : ℂ => p * z) hneg_inside
      _ =
          (upperLeft - leftReal + (lowerLeft - leftReal)) * p := by
        exact mul_comm p (upperLeft - leftReal + (lowerLeft - leftReal))
  have hpacket_sum :
      (upperRight - upperLeft) +
          (upperLeft - leftReal + (lowerLeft - leftReal)) =
        packet := by
    calc
      (upperRight - upperLeft) +
          (upperLeft - leftReal + (lowerLeft - leftReal)) =
        ((upperRight - upperLeft) + (upperLeft - leftReal)) +
          (lowerLeft - leftReal) := by
        exact add_assoc (upperRight - upperLeft) (upperLeft - leftReal)
          (lowerLeft - leftReal)
      _ =
        (upperRight - leftReal) + (lowerLeft - leftReal) := by
        exact congrArg
          (fun z : ℂ => z + (lowerLeft - leftReal))
          (sub_add_sub_cancel upperRight upperLeft leftReal)
      _ =
        (upperRight + lowerLeft) - (leftReal + leftReal) := by
        exact add_sub_add_comm upperRight leftReal lowerLeft leftReal
      _ =
        upperRight + lowerLeft - (leftReal + leftReal) := by
        rfl
      _ = packet := by
        rfl
  have hpacket_scalar :
      -upper - Complex.I * lowerVertical = packet * p := by
    calc
      -upper - Complex.I * lowerVertical =
          -upper + -(Complex.I * lowerVertical) := by
        exact sub_eq_add_neg (-upper) (Complex.I * lowerVertical)
      _ =
          (upperRight - upperLeft) * p +
            (upperLeft - leftReal + (lowerLeft - leftReal)) * p := by
        exact congrArg₂ HAdd.hAdd hupper_oriented hleft_oriented
      _ =
          ((upperRight - upperLeft) +
            (upperLeft - leftReal + (lowerLeft - leftReal))) * p := by
        exact
          (right_distrib (upperRight - upperLeft)
            (upperLeft - leftReal + (lowerLeft - leftReal)) p).symm
      _ = packet * p := by
        exact congrArg (fun z : ℂ => z * p) hpacket_sum
  calc
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (-upper - Complex.I * lowerVertical) =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (packet * ((Real.pi : ℂ) * Complex.I)) := by
      exact congrArg
        (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
        hpacket_scalar
    _ = packet / (2 : ℂ) := by
      exact Complex.finiteAbelPlana_two_pi_I_inv_mul_mul_pi_I packet
    _ = (upperRight + lowerLeft - (leftReal + leftReal)) / (2 : ℂ) := by
      rfl

/-- Right constant-face packet algebra after primitive evaluation.

The lower horizontal constant side and the right vertical constant side have
compatible orientations in the normalized right boundary packet.  The
height-corner terms survive with negative sign, and twice the right real
endpoint remains. -/
theorem Complex.finiteAbelPlana_rightConstantPacket_normalized_of_primitives
    (lower rightVertical rightReal lowerLeft lowerRight upperRight : ℂ)
    (hlower :
      lower = (lowerRight - lowerLeft) * ((Real.pi : ℂ) * Complex.I))
    (hright :
      rightVertical =
        (Real.pi : ℂ) * (rightReal - lowerRight) -
          (Real.pi : ℂ) * (upperRight - rightReal)) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (lower + Complex.I * rightVertical) =
      (rightReal + rightReal - lowerLeft - upperRight) / (2 : ℂ) := by
  let p : ℂ := (Real.pi : ℂ) * Complex.I
  let packet : ℂ := rightReal + rightReal - lowerLeft - upperRight
  have hright_oriented :
      Complex.I * rightVertical =
        (rightReal - lowerRight - (upperRight - rightReal)) * p := by
    have hI_pi :
        Complex.I * (Real.pi : ℂ) = p := by
      exact mul_comm Complex.I (Real.pi : ℂ)
    calc
      Complex.I * rightVertical =
          Complex.I *
            ((Real.pi : ℂ) * (rightReal - lowerRight) -
              (Real.pi : ℂ) * (upperRight - rightReal)) := by
        exact congrArg (fun z : ℂ => Complex.I * z) hright
      _ =
          Complex.I * ((Real.pi : ℂ) * (rightReal - lowerRight)) -
            Complex.I * ((Real.pi : ℂ) * (upperRight - rightReal)) := by
        exact mul_sub Complex.I
          ((Real.pi : ℂ) * (rightReal - lowerRight))
          ((Real.pi : ℂ) * (upperRight - rightReal))
      _ =
          (Complex.I * (Real.pi : ℂ)) * (rightReal - lowerRight) -
            (Complex.I * (Real.pi : ℂ)) * (upperRight - rightReal) := by
        exact congrArg₂ Sub.sub
          (mul_assoc Complex.I (Real.pi : ℂ) (rightReal - lowerRight))
          (mul_assoc Complex.I (Real.pi : ℂ) (upperRight - rightReal))
      _ =
          p * (rightReal - lowerRight) -
            p * (upperRight - rightReal) := by
        exact congrArg₂ Sub.sub
          (congrArg (fun z : ℂ => z * (rightReal - lowerRight)) hI_pi)
          (congrArg (fun z : ℂ => z * (upperRight - rightReal)) hI_pi)
      _ =
          p * ((rightReal - lowerRight) - (upperRight - rightReal)) := by
        exact
          (mul_sub p (rightReal - lowerRight) (upperRight - rightReal)).symm
      _ =
          ((rightReal - lowerRight) - (upperRight - rightReal)) * p := by
        exact mul_comm p ((rightReal - lowerRight) - (upperRight - rightReal))
  have hpacket_sum :
      (lowerRight - lowerLeft) +
          ((rightReal - lowerRight) - (upperRight - rightReal)) =
        packet := by
    calc
      (lowerRight - lowerLeft) +
          ((rightReal - lowerRight) - (upperRight - rightReal)) =
        (lowerRight - lowerLeft) +
          ((rightReal - lowerRight) + -(upperRight - rightReal)) := by
        exact congrArg
          (fun z : ℂ => (lowerRight - lowerLeft) + z)
          (sub_eq_add_neg (rightReal - lowerRight) (upperRight - rightReal))
      _ =
        ((lowerRight - lowerLeft) + (rightReal - lowerRight)) +
          -(upperRight - rightReal) := by
        exact add_assoc (lowerRight - lowerLeft) (rightReal - lowerRight)
          (-(upperRight - rightReal))
      _ =
        (rightReal - lowerLeft) + -(upperRight - rightReal) := by
        have hcancel :
            (lowerRight - lowerLeft) + (rightReal - lowerRight) =
              rightReal - lowerLeft := by
          calc
            (lowerRight - lowerLeft) + (rightReal - lowerRight) =
                (rightReal - lowerRight) + (lowerRight - lowerLeft) := by
              exact add_comm (lowerRight - lowerLeft) (rightReal - lowerRight)
            _ = rightReal - lowerLeft := by
              exact sub_add_sub_cancel rightReal lowerRight lowerLeft
        exact congrArg
          (fun z : ℂ => z + -(upperRight - rightReal))
          hcancel
      _ =
        (rightReal - lowerLeft) + (rightReal - upperRight) := by
        have hneg :
            -(upperRight - rightReal) = rightReal - upperRight :=
          neg_sub upperRight rightReal
        exact congrArg
          (fun z : ℂ => (rightReal - lowerLeft) + z)
          hneg
      _ =
        (rightReal + rightReal) - (lowerLeft + upperRight) := by
        exact add_sub_add_comm rightReal lowerLeft rightReal upperRight
      _ =
        rightReal + rightReal - lowerLeft - upperRight := by
        exact (sub_sub (rightReal + rightReal) lowerLeft upperRight).symm
      _ = packet := by
        rfl
  have hpacket_scalar :
      lower + Complex.I * rightVertical = packet * p := by
    calc
      lower + Complex.I * rightVertical =
          (lowerRight - lowerLeft) * p +
            ((rightReal - lowerRight) - (upperRight - rightReal)) * p := by
        exact congrArg₂ HAdd.hAdd hlower hright_oriented
      _ =
          ((lowerRight - lowerLeft) +
            ((rightReal - lowerRight) - (upperRight - rightReal))) * p := by
        exact
          (right_distrib (lowerRight - lowerLeft)
            ((rightReal - lowerRight) - (upperRight - rightReal)) p).symm
      _ = packet * p := by
        exact congrArg (fun z : ℂ => z * p) hpacket_sum
  calc
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (lower + Complex.I * rightVertical) =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (packet * ((Real.pi : ℂ) * Complex.I)) := by
      exact congrArg
        (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
        hpacket_scalar
    _ = packet / (2 : ℂ) := by
      exact Complex.finiteAbelPlana_two_pi_I_inv_mul_mul_pi_I packet
    _ = (rightReal + rightReal - lowerLeft - upperRight) / (2 : ℂ) := by
      rfl

/-- Abstract half-packet cancellation for the four constant Abel-Plana faces.

After the `(2πi)⁻¹` normalization, the left constant packet contributes
`(upperRight + lowerLeft - 2 * leftReal) / 2`, while the right constant
packet contributes `(2 * rightReal - lowerLeft - upperRight) / 2`.  The two
height-corner terms cancel and only the real segment primitive difference
remains. -/
theorem Complex.finiteAbelPlana_constantFace_halfPackets_cancel
    (lowerLeft upperRight leftReal rightReal : ℂ) :
    ((upperRight + lowerLeft - (leftReal + leftReal)) / (2 : ℂ)) +
      ((rightReal + rightReal - lowerLeft - upperRight) / (2 : ℂ)) =
      rightReal - leftReal := by
  let A : ℂ := upperRight + lowerLeft - (leftReal + leftReal)
  let B : ℂ := rightReal + rightReal - lowerLeft - upperRight
  let Y : ℂ := rightReal - leftReal
  have hleft :
      A + B = Y + Y := by
    calc
      A + B =
          (upperRight + lowerLeft - (leftReal + leftReal)) +
            (rightReal + rightReal - lowerLeft - upperRight) := by
        rfl
      _ =
          ((upperRight + lowerLeft) - (leftReal + leftReal)) +
            ((rightReal + rightReal) - (lowerLeft + upperRight)) := by
        exact congrArg
          (fun z : ℂ =>
            (upperRight + lowerLeft - (leftReal + leftReal)) + z)
          (sub_sub (rightReal + rightReal) lowerLeft upperRight)
      _ =
          ((upperRight + lowerLeft) + (rightReal + rightReal)) -
            ((leftReal + leftReal) + (lowerLeft + upperRight)) := by
        exact add_sub_add_comm
          (upperRight + lowerLeft) (leftReal + leftReal)
          (rightReal + rightReal) (lowerLeft + upperRight)
      _ =
          ((rightReal + rightReal) + (upperRight + lowerLeft)) -
            ((leftReal + leftReal) + (lowerLeft + upperRight)) := by
        exact congrArg
          (fun z : ℂ => z - ((leftReal + leftReal) + (lowerLeft + upperRight)))
          (add_comm (upperRight + lowerLeft) (rightReal + rightReal))
      _ =
          (rightReal + rightReal) -
            (leftReal + leftReal) := by
        have hright_reorder :
            (leftReal + leftReal) + (lowerLeft + upperRight) =
              (leftReal + leftReal) + (upperRight + lowerLeft) := by
          exact congrArg
            (fun z : ℂ => (leftReal + leftReal) + z)
            (add_comm lowerLeft upperRight)
        have hcancel :
            ((rightReal + rightReal) + (upperRight + lowerLeft)) -
              ((leftReal + leftReal) + (upperRight + lowerLeft)) =
              (rightReal + rightReal) - (leftReal + leftReal) := by
          exact add_sub_add_right_eq_sub (rightReal + rightReal) (leftReal + leftReal)
            (upperRight + lowerLeft)
        exact Eq.trans
          (congrArg
            (fun z : ℂ => ((rightReal + rightReal) + (upperRight + lowerLeft)) - z)
            hright_reorder)
          hcancel
      _ =
          (rightReal - leftReal) + (rightReal - leftReal) := by
        exact (add_sub_add_comm rightReal leftReal rightReal leftReal).symm
      _ = Y + Y := by
        rfl
  calc
    (A / (2 : ℂ)) + (B / (2 : ℂ)) =
        (A + B) / (2 : ℂ) := by
      exact div_add_div_same A B (2 : ℂ)
    _ = (Y + Y) / (2 : ℂ) := by
      exact congrArg (fun z : ℂ => z / (2 : ℂ)) hleft
    _ = Y := by
      exact add_self_div_two Y
    _ = rightReal - leftReal := by
      rfl

/-- Left vertical lower endpoint equals the lower-left rectangle corner. -/
theorem Complex.finiteAbelPlana_leftVertical_lowerCorner_arg
    (T : ℝ) :
    Complex.I * ((-T : ℝ) : ℂ) =
      (0 : ℂ) - (T : ℂ) * Complex.I := by
  calc
    Complex.I * ((-T : ℝ) : ℂ) =
        Complex.I * (-(T : ℂ)) := by
      exact congrArg (fun z : ℂ => Complex.I * z) (Complex.ofReal_neg T)
    _ = -(Complex.I * (T : ℂ)) := by
      exact mul_neg Complex.I (T : ℂ)
    _ = -((T : ℂ) * Complex.I) := by
      exact congrArg Neg.neg (mul_comm Complex.I (T : ℂ))
    _ = (0 : ℂ) - (T : ℂ) * Complex.I := by
      exact (zero_sub ((T : ℂ) * Complex.I)).symm

/-- Left vertical upper endpoint equals the upper-left rectangle corner. -/
theorem Complex.finiteAbelPlana_leftVertical_upperCorner_arg
    (T : ℝ) :
    Complex.I * (T : ℂ) =
      (0 : ℂ) + (T : ℂ) * Complex.I := by
  calc
    Complex.I * (T : ℂ) =
        (T : ℂ) * Complex.I := by
      exact mul_comm Complex.I (T : ℂ)
    _ = (0 : ℂ) + (T : ℂ) * Complex.I := by
      exact (zero_add ((T : ℂ) * Complex.I)).symm

/-- Left vertical middle endpoint is the left real corner. -/
theorem Complex.finiteAbelPlana_leftVertical_realCorner_arg :
    Complex.I * (0 : ℂ) = (0 : ℂ) := by
  exact mul_zero Complex.I

/-- Right vertical lower endpoint equals the lower-right rectangle corner. -/
theorem Complex.finiteAbelPlana_rightVertical_lowerCorner_arg
    (M : ℕ)
    (T : ℝ) :
    (M : ℂ) + Complex.I * ((-T : ℝ) : ℂ) =
      ((M : ℝ) : ℂ) - (T : ℂ) * Complex.I := by
  calc
    (M : ℂ) + Complex.I * ((-T : ℝ) : ℂ) =
        (M : ℂ) + ((0 : ℂ) - (T : ℂ) * Complex.I) := by
      exact congrArg
        (fun z : ℂ => (M : ℂ) + z)
        (Complex.finiteAbelPlana_leftVertical_lowerCorner_arg T)
    _ = ((M : ℝ) : ℂ) + ((0 : ℂ) - (T : ℂ) * Complex.I) := by
      rfl
    _ = ((M : ℝ) : ℂ) - (T : ℂ) * Complex.I := by
      exact congrArg
        (fun z : ℂ => z - (T : ℂ) * Complex.I)
        (add_zero (((M : ℝ) : ℂ)))

/-- Right vertical upper endpoint equals the upper-right rectangle corner. -/
theorem Complex.finiteAbelPlana_rightVertical_upperCorner_arg
    (M : ℕ)
    (T : ℝ) :
    (M : ℂ) + Complex.I * (T : ℂ) =
      ((M : ℝ) : ℂ) + (T : ℂ) * Complex.I := by
  calc
    (M : ℂ) + Complex.I * (T : ℂ) =
        (M : ℂ) + ((0 : ℂ) + (T : ℂ) * Complex.I) := by
      exact congrArg
        (fun z : ℂ => (M : ℂ) + z)
        (Complex.finiteAbelPlana_leftVertical_upperCorner_arg T)
    _ = ((M : ℝ) : ℂ) + ((0 : ℂ) + (T : ℂ) * Complex.I) := by
      rfl
    _ = ((M : ℝ) : ℂ) + (T : ℂ) * Complex.I := by
      exact congrArg
        (fun z : ℂ => ((M : ℝ) : ℂ) + z)
        (zero_add ((T : ℂ) * Complex.I))

/-- Right vertical middle endpoint is the right real corner. -/
theorem Complex.finiteAbelPlana_rightVertical_realCorner_arg
    (M : ℕ) :
    (M : ℂ) + Complex.I * (0 : ℂ) = ((M : ℝ) : ℂ) := by
  calc
    (M : ℂ) + Complex.I * (0 : ℂ) =
        (M : ℂ) + (0 : ℂ) := by
      exact congrArg (fun z : ℂ => (M : ℂ) + z) (mul_zero Complex.I)
    _ = (M : ℂ) := by
      exact add_zero (M : ℂ)
    _ = ((M : ℝ) : ℂ) := by
      rfl

/-- Concrete left normalized constant-face packet for the finite Abel-Plana
rectangle. -/
theorem Complex.finiteAbelPlana_log_leftConstantPacket_normalized_eq_halfPacket
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ) :
    let M : ℕ := N + 1
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
          Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T) =
      (Complex.finiteAbelPlanaLogComplexPrimitive w
          (((M : ℝ) : ℂ) + (T : ℂ) * Complex.I) +
        Complex.finiteAbelPlanaLogComplexPrimitive w
          ((0 : ℂ) - (T : ℂ) * Complex.I) -
        (Complex.finiteAbelPlanaLogComplexPrimitive w (0 : ℂ) +
          Complex.finiteAbelPlanaLogComplexPrimitive w (0 : ℂ))) / (2 : ℂ) := by
  intro M
  let F : ℂ → ℂ := fun z : ℂ => Complex.finiteAbelPlanaLogComplexPrimitive w z
  have hupper :
      Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T =
        (F (((M : ℝ) : ℂ) + (T : ℂ) * Complex.I) -
          F ((0 : ℂ) + (T : ℂ) * Complex.I)) *
          (-(Real.pi : ℂ) * Complex.I) :=
    Complex.finiteAbelPlana_log_upperHorizontalCotangentConstantSide_eq_primitive
      N hw T
  have hleft_raw :
      Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T =
        (Real.pi : ℂ) *
            (F (Complex.I * (0 : ℂ)) -
              F (Complex.I * ((-T : ℝ) : ℂ))) -
          (Real.pi : ℂ) *
            (F (Complex.I * (T : ℂ)) -
              F (Complex.I * (0 : ℂ))) :=
    Complex.finiteAbelPlana_log_leftVerticalCotangentConstantSide_eq_primitive
      hw T
  have hleft :
      Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T =
        (Real.pi : ℂ) *
            (F (0 : ℂ) -
              F ((0 : ℂ) - (T : ℂ) * Complex.I)) -
          (Real.pi : ℂ) *
            (F ((0 : ℂ) + (T : ℂ) * Complex.I) -
              F (0 : ℂ)) := by
    have hzero :
        F (Complex.I * (0 : ℂ)) = F (0 : ℂ) :=
      congrArg F Complex.finiteAbelPlana_leftVertical_realCorner_arg
    have hlower :
        F (Complex.I * ((-T : ℝ) : ℂ)) =
          F ((0 : ℂ) - (T : ℂ) * Complex.I) :=
      congrArg F (Complex.finiteAbelPlana_leftVertical_lowerCorner_arg T)
    have hupper_left :
        F (Complex.I * (T : ℂ)) =
          F ((0 : ℂ) + (T : ℂ) * Complex.I) :=
      congrArg F (Complex.finiteAbelPlana_leftVertical_upperCorner_arg T)
    calc
      Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T =
          (Real.pi : ℂ) *
              (F (Complex.I * (0 : ℂ)) -
                F (Complex.I * ((-T : ℝ) : ℂ))) -
            (Real.pi : ℂ) *
              (F (Complex.I * (T : ℂ)) -
                F (Complex.I * (0 : ℂ))) := hleft_raw
      _ =
          (Real.pi : ℂ) *
              (F (0 : ℂ) -
                F ((0 : ℂ) - (T : ℂ) * Complex.I)) -
            (Real.pi : ℂ) *
              (F ((0 : ℂ) + (T : ℂ) * Complex.I) -
                F (0 : ℂ)) := by
        exact congrArg₂ Sub.sub
          (congrArg
            (fun z : ℂ => (Real.pi : ℂ) * z)
            (congrArg₂ Sub.sub hzero hlower))
          (congrArg
            (fun z : ℂ => (Real.pi : ℂ) * z)
            (congrArg₂ Sub.sub hupper_left hzero))
  exact
    Complex.finiteAbelPlana_leftConstantPacket_normalized_of_primitives
      (Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T)
      (Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)
      (F (0 : ℂ))
      (F ((0 : ℂ) - (T : ℂ) * Complex.I))
      (F ((0 : ℂ) + (T : ℂ) * Complex.I))
      (F (((M : ℝ) : ℂ) + (T : ℂ) * Complex.I))
      hupper
      hleft

/-- Concrete right normalized constant-face packet for the finite Abel-Plana
rectangle. -/
theorem Complex.finiteAbelPlana_log_rightConstantPacket_normalized_eq_halfPacket
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ) :
    let M : ℕ := N + 1
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
          Complex.I *
            Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T) =
      (Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℝ) : ℂ) +
          Complex.finiteAbelPlanaLogComplexPrimitive w ((M : ℝ) : ℂ) -
        Complex.finiteAbelPlanaLogComplexPrimitive w
          ((0 : ℂ) - (T : ℂ) * Complex.I) -
        Complex.finiteAbelPlanaLogComplexPrimitive w
          (((M : ℝ) : ℂ) + (T : ℂ) * Complex.I)) / (2 : ℂ) := by
  intro M
  let F : ℂ → ℂ := fun z : ℂ => Complex.finiteAbelPlanaLogComplexPrimitive w z
  have hlower :
      Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T =
        (F (((M : ℝ) : ℂ) - (T : ℂ) * Complex.I) -
          F ((0 : ℂ) - (T : ℂ) * Complex.I)) *
          ((Real.pi : ℂ) * Complex.I) :=
    Complex.finiteAbelPlana_log_lowerHorizontalCotangentConstantSide_eq_primitive
      N hw T
  have hright_raw :
      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T =
        (Real.pi : ℂ) *
            (F ((M : ℂ) + Complex.I * (0 : ℂ)) -
              F ((M : ℂ) + Complex.I * ((-T : ℝ) : ℂ))) -
          (Real.pi : ℂ) *
            (F ((M : ℂ) + Complex.I * (T : ℂ)) -
              F ((M : ℂ) + Complex.I * (0 : ℂ))) :=
    Complex.finiteAbelPlana_log_rightVerticalCotangentConstantSide_eq_primitive
      N hw T
  have hright :
      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T =
        (Real.pi : ℂ) *
            (F ((M : ℝ) : ℂ) -
              F (((M : ℝ) : ℂ) - (T : ℂ) * Complex.I)) -
          (Real.pi : ℂ) *
            (F (((M : ℝ) : ℂ) + (T : ℂ) * Complex.I) -
              F ((M : ℝ) : ℂ)) := by
    have hzero :
        F ((M : ℂ) + Complex.I * (0 : ℂ)) =
          F ((M : ℝ) : ℂ) :=
      congrArg F (Complex.finiteAbelPlana_rightVertical_realCorner_arg M)
    have hlower_right :
        F ((M : ℂ) + Complex.I * ((-T : ℝ) : ℂ)) =
          F (((M : ℝ) : ℂ) - (T : ℂ) * Complex.I) :=
      congrArg F (Complex.finiteAbelPlana_rightVertical_lowerCorner_arg M T)
    have hupper_right :
        F ((M : ℂ) + Complex.I * (T : ℂ)) =
          F (((M : ℝ) : ℂ) + (T : ℂ) * Complex.I) :=
      congrArg F (Complex.finiteAbelPlana_rightVertical_upperCorner_arg M T)
    calc
      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T =
          (Real.pi : ℂ) *
              (F ((M : ℂ) + Complex.I * (0 : ℂ)) -
                F ((M : ℂ) + Complex.I * ((-T : ℝ) : ℂ))) -
            (Real.pi : ℂ) *
              (F ((M : ℂ) + Complex.I * (T : ℂ)) -
                F ((M : ℂ) + Complex.I * (0 : ℂ))) := hright_raw
      _ =
          (Real.pi : ℂ) *
              (F ((M : ℝ) : ℂ) -
                F (((M : ℝ) : ℂ) - (T : ℂ) * Complex.I)) -
            (Real.pi : ℂ) *
              (F (((M : ℝ) : ℂ) + (T : ℂ) * Complex.I) -
                F ((M : ℝ) : ℂ)) := by
        exact congrArg₂ Sub.sub
          (congrArg
            (fun z : ℂ => (Real.pi : ℂ) * z)
            (congrArg₂ Sub.sub hzero hlower_right))
          (congrArg
            (fun z : ℂ => (Real.pi : ℂ) * z)
            (congrArg₂ Sub.sub hupper_right hzero))
  exact
    Complex.finiteAbelPlana_rightConstantPacket_normalized_of_primitives
      (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T)
      (Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)
      (F ((M : ℝ) : ℂ))
      (F ((0 : ℂ) - (T : ℂ) * Complex.I))
      (F (((M : ℝ) : ℂ) - (T : ℂ) * Complex.I))
      (F (((M : ℝ) : ℂ) + (T : ℂ) * Complex.I))
      hlower
      hright

/-- PV left vertical side splits into its constant and exponential-remainder
parts. -/
theorem Complex.finiteAbelPlana_log_leftVerticalSidePV_eq_constant_add_remainder
    (w : ℂ)
    (T ε : ℝ)
    (hw : 0 < w.re)
    (hε : 0 < ε)
    (hεT : ε < T) :
    Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ε =
      Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε +
        Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePV w T ε := by
  unfold Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV
    Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV
    Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePV
  have hneg_order : -T ≤ -ε :=
    neg_le_neg hεT.le
  have hneg_eps : -ε < 0 :=
    neg_neg_of_pos hε
  have hleft_path :
      Continuous (fun y : ℝ => Complex.I * (y : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  have hleft_log :
      Continuous
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ))) :=
    Complex.continuous_finiteAbelPlana_log_leftVerticalSummand hw
  have hcot_lower :
      ContinuousOn
        (fun y : ℝ =>
          Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)))
        (Set.uIcc (-T) (-ε)) := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (-T) (-ε) :=
      (Set.uIcc_of_le hneg_order).symm ▸ hy
    have hy_ne : y ≠ 0 :=
      ne_of_lt (lt_of_le_of_lt hyIcc.2 hneg_eps)
    exact
      ((Complex.differentiableAt_finiteAbelPlanaCotangentKernel
        (Complex.sin_pi_mul_ne_zero_of_im_ne_zero
          (by
            have him : (Complex.I * (y : ℂ)).im = y := by
              exact Eq.trans (Complex.I_mul_im (y : ℂ)) (Complex.ofReal_re y)
            exact him.symm ▸ hy_ne))).continuousAt.comp'
        hleft_path.continuousAt).continuousWithinAt
  have hcot_upper :
      ContinuousOn
        (fun y : ℝ =>
          Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)))
        (Set.uIcc ε T) := by
    intro y hy
    have hpos_order : ε ≤ T := hεT.le
    have hyIcc : y ∈ Set.Icc ε T :=
      (Set.uIcc_of_le hpos_order).symm ▸ hy
    have hy_ne : y ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le hε hyIcc.1)
    exact
      ((Complex.differentiableAt_finiteAbelPlanaCotangentKernel
        (Complex.sin_pi_mul_ne_zero_of_im_ne_zero
          (by
            have him : (Complex.I * (y : ℂ)).im = y := by
              exact Eq.trans (Complex.I_mul_im (y : ℂ)) (Complex.ofReal_re y)
            exact him.symm ▸ hy_ne))).continuousAt.comp'
        hleft_path.continuousAt).continuousWithinAt
  have hlower_const_int :
      IntervalIntegrable
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            ((Real.pi : ℂ) * Complex.I))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (-T) (-ε) :=
    (hleft_log.mul continuous_const).continuousOn.intervalIntegrable
  have hupper_const_int :
      IntervalIntegrable
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            (-(Real.pi : ℂ) * Complex.I))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) ε T :=
    (hleft_log.mul continuous_const).continuousOn.intervalIntegrable
  have hlower_rem_int :
      IntervalIntegrable
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) -
              (Real.pi : ℂ) * Complex.I))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (-T) (-ε) := by
    exact
      (hleft_log.continuousOn.mul
        (hcot_lower.sub continuousOn_const)).intervalIntegrable
  have hupper_rem_int :
      IntervalIntegrable
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) +
              (Real.pi : ℂ) * Complex.I))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) ε T := by
    exact
      (hleft_log.continuousOn.mul
        (hcot_upper.add continuousOn_const)).intervalIntegrable
  have hlower_split :
      (∫ y : ℝ in (-T)..(-ε),
        Complex.finiteAbelPlanaLogRectangleIntegrand w (Complex.I * (y : ℂ))) =
      (∫ y : ℝ in (-T)..(-ε),
        Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
          ((Real.pi : ℂ) * Complex.I)) +
      (∫ y : ℝ in (-T)..(-ε),
        Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
          (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) -
            (Real.pi : ℂ) * Complex.I)) := by
    exact
      Eq.trans
        (intervalIntegral.integral_congr
          (fun y _hy =>
            Complex.finiteAbelPlana_log_leftVertical_lower_pointwise_split w y))
        (intervalIntegral.integral_add
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
          hlower_const_int hlower_rem_int)
  have hupper_split :
      (∫ y : ℝ in ε..T,
        Complex.finiteAbelPlanaLogRectangleIntegrand w (Complex.I * (y : ℂ))) =
      (∫ y : ℝ in ε..T,
        Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
          (-(Real.pi : ℂ) * Complex.I)) +
      (∫ y : ℝ in ε..T,
        Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
          (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) +
            (Real.pi : ℂ) * Complex.I)) := by
    exact
      Eq.trans
        (intervalIntegral.integral_congr
          (fun y _hy =>
            Complex.finiteAbelPlana_log_leftVertical_upper_pointwise_split w y))
        (intervalIntegral.integral_add
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
          hupper_const_int hupper_rem_int)
  exact
    Eq.trans
      (congrArg₂ HAdd.hAdd hlower_split hupper_split)
      (Complex.verticalSide_split_collect
        (∫ y : ℝ in (-T)..(-ε),
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            ((Real.pi : ℂ) * Complex.I))
        (∫ y : ℝ in ε..T,
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            (-(Real.pi : ℂ) * Complex.I))
        (∫ y : ℝ in (-T)..(-ε),
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) -
              (Real.pi : ℂ) * Complex.I))
        (∫ y : ℝ in ε..T,
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) +
              (Real.pi : ℂ) * Complex.I)))

/-- PV right vertical side splits into its constant and exponential-remainder
parts. -/
theorem Complex.finiteAbelPlana_log_rightVerticalSidePV_eq_constant_add_remainder
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ)
    (hw : 0 < w.re)
    (hε : 0 < ε)
    (hεT : ε < T) :
    Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ε =
      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε +
        Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePV N w T ε := by
  unfold Complex.finiteAbelPlanaLogFiniteHeightRightSidePV
    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV
    Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePV
  have hneg_order : -T ≤ -ε :=
    neg_le_neg hεT.le
  have hneg_eps : -ε < 0 :=
    neg_neg_of_pos hε
  have hright_path :
      Continuous
        (fun y : ℝ => (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ))) :=
    continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  have hright_log :
      Continuous
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w
            (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ))) :=
    Complex.continuous_finiteAbelPlana_log_rightVerticalSummand N hw
  have hcot_lower :
      ContinuousOn
        (fun y : ℝ =>
          Complex.finiteAbelPlanaCotangentKernel
            (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)))
        (Set.uIcc (-T) (-ε)) := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (-T) (-ε) :=
      (Set.uIcc_of_le hneg_order).symm ▸ hy
    have hy_ne : y ≠ 0 :=
      ne_of_lt (lt_of_le_of_lt hyIcc.2 hneg_eps)
    exact
      ((Complex.differentiableAt_finiteAbelPlanaCotangentKernel
        (Complex.sin_pi_mul_ne_zero_of_im_ne_zero
          (by
            have hnat_im : (((N + 1 : ℕ) : ℂ)).im = 0 :=
              Complex.ofReal_im (((N + 1 : ℕ) : ℝ))
            have hI_im : (Complex.I * (y : ℂ)).im = y := by
              exact Eq.trans (Complex.I_mul_im (y : ℂ)) (Complex.ofReal_re y)
            have him :
                ((((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)).im) = y := by
              calc
                ((((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)).im) =
                    (((N + 1 : ℕ) : ℂ)).im + (Complex.I * (y : ℂ)).im := by
                  exact Complex.add_im (((N + 1 : ℕ) : ℂ)) (Complex.I * (y : ℂ))
                _ = 0 + (Complex.I * (y : ℂ)).im := by
                  exact congrArg (fun r : ℝ => r + (Complex.I * (y : ℂ)).im) hnat_im
                _ = 0 + y := by
                  exact congrArg (fun r : ℝ => 0 + r) hI_im
                _ = y := by
                  exact zero_add y
            exact him.symm ▸ hy_ne))).continuousAt.comp'
        hright_path.continuousAt).continuousWithinAt
  have hcot_upper :
      ContinuousOn
        (fun y : ℝ =>
          Complex.finiteAbelPlanaCotangentKernel
            (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)))
        (Set.uIcc ε T) := by
    intro y hy
    have hpos_order : ε ≤ T := hεT.le
    have hyIcc : y ∈ Set.Icc ε T :=
      (Set.uIcc_of_le hpos_order).symm ▸ hy
    have hy_ne : y ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le hε hyIcc.1)
    exact
      ((Complex.differentiableAt_finiteAbelPlanaCotangentKernel
        (Complex.sin_pi_mul_ne_zero_of_im_ne_zero
          (by
            have hnat_im : (((N + 1 : ℕ) : ℂ)).im = 0 :=
              Complex.ofReal_im (((N + 1 : ℕ) : ℝ))
            have hI_im : (Complex.I * (y : ℂ)).im = y := by
              exact Eq.trans (Complex.I_mul_im (y : ℂ)) (Complex.ofReal_re y)
            have him :
                ((((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)).im) = y := by
              calc
                ((((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)).im) =
                    (((N + 1 : ℕ) : ℂ)).im + (Complex.I * (y : ℂ)).im := by
                  exact Complex.add_im (((N + 1 : ℕ) : ℂ)) (Complex.I * (y : ℂ))
                _ = 0 + (Complex.I * (y : ℂ)).im := by
                  exact congrArg (fun r : ℝ => r + (Complex.I * (y : ℂ)).im) hnat_im
                _ = 0 + y := by
                  exact congrArg (fun r : ℝ => 0 + r) hI_im
                _ = y := by
                  exact zero_add y
            exact him.symm ▸ hy_ne))).continuousAt.comp'
        hright_path.continuousAt).continuousWithinAt
  have hlower_const_int :
      IntervalIntegrable
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w
            (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
            ((Real.pi : ℂ) * Complex.I))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (-T) (-ε) :=
    (hright_log.mul continuous_const).continuousOn.intervalIntegrable
  have hupper_const_int :
      IntervalIntegrable
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w
            (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
            (-(Real.pi : ℂ) * Complex.I))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) ε T :=
    (hright_log.mul continuous_const).continuousOn.intervalIntegrable
  have hlower_rem_int :
      IntervalIntegrable
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w
            (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel
                (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) -
              (Real.pi : ℂ) * Complex.I))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (-T) (-ε) := by
    exact
      (hright_log.continuousOn.mul
        (hcot_lower.sub continuousOn_const)).intervalIntegrable
  have hupper_rem_int :
      IntervalIntegrable
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w
            (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel
                (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) +
              (Real.pi : ℂ) * Complex.I))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) ε T := by
    exact
      (hright_log.continuousOn.mul
        (hcot_upper.add continuousOn_const)).intervalIntegrable
  have hlower_split :
      (∫ y : ℝ in (-T)..(-ε),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ))) =
      (∫ y : ℝ in (-T)..(-ε),
        Complex.finiteAbelPlanaLogSummand w
          (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
          ((Real.pi : ℂ) * Complex.I)) +
      (∫ y : ℝ in (-T)..(-ε),
        Complex.finiteAbelPlanaLogSummand w
          (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
          (Complex.finiteAbelPlanaCotangentKernel
              (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) -
            (Real.pi : ℂ) * Complex.I)) := by
    exact
      Eq.trans
        (intervalIntegral.integral_congr
          (fun y _hy =>
            Complex.finiteAbelPlana_log_rightVertical_lower_pointwise_split N w y))
        (intervalIntegral.integral_add
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
          hlower_const_int hlower_rem_int)
  have hupper_split :
      (∫ y : ℝ in ε..T,
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ))) =
      (∫ y : ℝ in ε..T,
        Complex.finiteAbelPlanaLogSummand w
          (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
          (-(Real.pi : ℂ) * Complex.I)) +
      (∫ y : ℝ in ε..T,
        Complex.finiteAbelPlanaLogSummand w
          (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
          (Complex.finiteAbelPlanaCotangentKernel
              (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) +
            (Real.pi : ℂ) * Complex.I)) := by
    exact
      Eq.trans
        (intervalIntegral.integral_congr
          (fun y _hy =>
            Complex.finiteAbelPlana_log_rightVertical_upper_pointwise_split N w y))
        (intervalIntegral.integral_add
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
          hupper_const_int hupper_rem_int)
  exact
    Eq.trans
      (congrArg₂ HAdd.hAdd hlower_split hupper_split)
      (Complex.verticalSide_split_collect
        (∫ y : ℝ in (-T)..(-ε),
          Complex.finiteAbelPlanaLogSummand w
            (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
            ((Real.pi : ℂ) * Complex.I))
        (∫ y : ℝ in ε..T,
          Complex.finiteAbelPlanaLogSummand w
            (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
            (-(Real.pi : ℂ) * Complex.I))
        (∫ y : ℝ in (-T)..(-ε),
          Complex.finiteAbelPlanaLogSummand w
            (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel
                (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) -
              (Real.pi : ℂ) * Complex.I))
        (∫ y : ℝ in ε..T,
          Complex.finiteAbelPlanaLogSummand w
            (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel
                (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) +
              (Real.pi : ℂ) * Complex.I)))

/-- Truncated lower vertical Abel-Plana integral with lower cutoff `ε`. -/
noncomputable def Complex.finiteAbelPlanaLogLowerVerticalIntegralFromTo
    (w : ℂ)
    (ε T : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioc ε T,
    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t

/-- Truncated upper vertical Abel-Plana integral with lower cutoff `ε`. -/
noncomputable def Complex.finiteAbelPlanaLogUpperVerticalIntegralFromTo
    (N : ℕ)
    (w : ℂ)
    (ε T : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioc ε T,
    Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t

/-- Interval integrability of the left constant-side vertical integrand. -/
theorem Complex.intervalIntegrable_finiteAbelPlana_log_leftConstantVerticalIntegrand
    {w : ℂ}
    (hw : 0 < w.re)
    (a b : ℝ)
    (c : ℂ) :
    IntervalIntegrable
      (fun y : ℝ =>
        Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) * c)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b := by
  exact
    ((Complex.continuous_finiteAbelPlana_log_leftVerticalSummand hw).mul
      continuous_const).continuousOn.intervalIntegrable

/-- Interval integrability of the right constant-side vertical integrand. -/
theorem Complex.intervalIntegrable_finiteAbelPlana_log_rightConstantVerticalIntegrand
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (a b : ℝ)
    (c : ℂ) :
    IntervalIntegrable
      (fun y : ℝ =>
        Complex.finiteAbelPlanaLogSummand w
          (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) * c)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b := by
  exact
    ((Complex.continuous_finiteAbelPlana_log_rightVerticalSummand N hw).mul
      continuous_const).continuousOn.intervalIntegrable


end

end LFunctions
end Boundary
