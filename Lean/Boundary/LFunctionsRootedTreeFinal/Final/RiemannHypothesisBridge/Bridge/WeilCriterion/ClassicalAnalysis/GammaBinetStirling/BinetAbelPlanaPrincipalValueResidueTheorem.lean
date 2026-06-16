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
  exact Eq.symm
    (Eq.trans
      (congrArg
        (fun z : ℂ => a * c + z)
        (mul_sub a b c))
      (add_sub_cancel_left (a * c) (a * b)))

/-- A right cancellation identity used by the upper-half-plane cotangent split. -/
theorem Complex.neg_add_add_cancel_right
    (x y : ℂ) :
    -x + (y + x) = y := by
  exact
    Eq.trans
      (add_assoc (-x) y x)
      (Eq.trans
        (congrArg
          (fun z : ℂ => z + x)
          (add_comm (-x) y))
        (Eq.trans
          (Eq.symm (add_assoc y (-x) x))
          (Eq.trans
            (congrArg
              (fun z : ℂ => y + z)
              (neg_add_cancel x))
            (add_zero y))))

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
        (add_assoc lowerRemainder upperConstant upperRemainder)
    _ = lowerConstant + ((upperConstant + lowerRemainder) + upperRemainder) := by
      exact congrArg
        (fun z : ℂ => lowerConstant + (z + upperRemainder))
        (add_comm lowerRemainder upperConstant)
    _ = lowerConstant + (upperConstant + (lowerRemainder + upperRemainder)) := by
      exact congrArg
        (fun z : ℂ => lowerConstant + z)
        (Eq.symm (add_assoc upperConstant lowerRemainder upperRemainder))
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
  exact
    Eq.trans
      (mul_add (-Complex.I) constant remainder)
      (Eq.trans
        (congrArg
          (fun z : ℂ => z + (-Complex.I * remainder))
          (neg_mul Complex.I constant))
        (Eq.symm
          (Eq.trans
            (add_assoc horizontal (-horizontal - Complex.I * constant)
              (-Complex.I * remainder))
            (Eq.trans
              (congrArg
                (fun z : ℂ => z + (-Complex.I * remainder))
                (Eq.trans
                  (sub_eq_add_neg horizontal (Complex.I * constant) ▸
                    add_assoc horizontal (-horizontal) (-(Complex.I * constant)))
                  (Eq.trans
                    (congrArg
                      (fun z : ℂ => z + -(Complex.I * constant))
                      (add_neg_cancel horizontal))
                    (zero_add (-(Complex.I * constant)))))
              (Eq.symm
                (add_assoc (-(Complex.I * constant))
                  (-Complex.I * remainder) 0))))))

/-- Cancellation of an adjacent horizontal constant in the right oriented
side assembly. -/
theorem Complex.rightOrientedVertical_assembly_collect
    (horizontal constant remainder : ℂ) :
    Complex.I * (constant + remainder) =
      (horizontal + Complex.I * constant) +
        (Complex.I * remainder) - horizontal := by
  exact
    Eq.trans
      (mul_add Complex.I constant remainder)
      (Eq.symm
        (Eq.trans
          (sub_eq_add_neg
            ((horizontal + Complex.I * constant) + Complex.I * remainder)
            horizontal)
          (Eq.trans
            (add_assoc (horizontal + Complex.I * constant)
              (Complex.I * remainder) (-horizontal))
            (Eq.trans
              (congrArg
                (fun z : ℂ => (horizontal + Complex.I * constant) + z)
                (add_comm (Complex.I * remainder) (-horizontal)))
              (Eq.trans
                (Eq.symm
                  (add_assoc (horizontal + Complex.I * constant)
                    (-horizontal) (Complex.I * remainder)))
                (Eq.trans
                  (congrArg
                    (fun z : ℂ => z + Complex.I * remainder)
                    (Eq.trans
                      (add_assoc horizontal (Complex.I * constant) (-horizontal))
                      (Eq.trans
                        (congrArg
                          (fun z : ℂ => horizontal + z)
                          (add_comm (Complex.I * constant) (-horizontal)))
                        (Eq.trans
                          (Eq.symm
                            (add_assoc horizontal (-horizontal)
                              (Complex.I * constant)))
                          (Eq.trans
                            (congrArg
                              (fun z : ℂ => z + Complex.I * constant)
                              (add_neg_cancel horizontal))
                            (zero_add (Complex.I * constant)))))))
                  (Eq.refl (Complex.I * constant + Complex.I * remainder)))))))

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
  add_sub_cancel_left lower upperFace

/-- Boundary-face algebra: left and right raw faces collect into constant
horizontal and raw vertical contributions. -/
theorem Complex.finiteAbelPlana_boundaryFace_collect
    (lower upper right left : ℂ) :
    (-upper - Complex.I * left) + (lower + Complex.I * right) =
      lower - upper + (Complex.I * right - Complex.I * left) := by
  calc
    (-upper - Complex.I * left) + (lower + Complex.I * right)
        = lower + ((-upper - Complex.I * left) + Complex.I * right) := by
      exact (add_comm (-upper - Complex.I * left) (lower + Complex.I * right)).trans
        (add_assoc lower (-upper - Complex.I * left) (Complex.I * right)).symm
    _ = lower + ((-upper) + ((-Complex.I * left) + Complex.I * right)) := by
      exact congrArg (fun z : ℂ => lower + z)
        (sub_eq_add_neg upper (Complex.I * left) ▸
          add_assoc (-upper) (-Complex.I * left) (Complex.I * right))
    _ = lower - upper + (Complex.I * right - Complex.I * left) := by
      exact congrArg (fun z : ℂ => lower - upper + z)
        (add_comm (-Complex.I * left) (Complex.I * right))

/-- Named-boundary algebra: lower face plus upper face equals real endpoint
plus the combined named vertical side. -/
theorem Complex.finiteAbelPlana_namedBoundary_collect
    (endpoint lower upper : ℂ) :
    (endpoint - lower) + (-upper) =
      endpoint + (-lower - upper) := by
  calc
    (endpoint - lower) + (-upper) =
        endpoint + (-lower) + (-upper) := by
      exact add_assoc endpoint (-lower) (-upper)
    _ = endpoint + (-lower - upper) := by
      exact (add_assoc endpoint (-lower) (-upper)).symm

/-- Principal-value finite punctured-rectangle residue accounting obtained by
combining the Cauchy-Goursat punctured-boundary limit with the small-circle
residue limits. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangleResidueAccountingPV
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) := by
  have hcauchy :
      Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (0 : ℂ)) :=
    Complex.finiteAbelPlana_log_puncturedRectangleCauchyGoursat_pvSmallCircles
      hw N T hT
  have hcircles :
      Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ)
        (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) :=
    Complex.finiteAbelPlana_log_pvDeletedBoundaryIntegralContribution_tendsto_pvResidues
      hw N
  have hsum :
      Tendsto
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
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ) =
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ) := by
    funext ρ
    exact sub_add_cancel
      (Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
      (Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ)
  exact hpoint ▸ by
    simpa using hsum

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
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) := by
  exact
    Complex.finiteAbelPlana_log_puncturedRectangleResidueAccountingPV
      hw N T hT

/-- Principal-value residue theorem for the finite Abel-Plana logarithmic
rectangle.

The intended proof is the standard Abel-Plana contour argument:

1. apply the rectangle Cauchy theorem to
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
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝
        (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) := by
  have hlim :
      Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) :=
    Complex.finiteAbelPlana_log_finiteHeightPuncturedRectangleBoundary_tendsto_residues
      hw N T hT
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
  rfl

/-- The finite-height named side expression is the real/endpoints part plus
the named lower and upper vertical Abel-Plana jump integrals. -/
theorem Complex.finiteAbelPlana_log_finiteHeightNamedSideExpression_eq_realEndpoint_add_vertical
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
      Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
        Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T := by
  rfl

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
  calc
    a * K = a * (C + (K - C)) := by
      exact congrArg (fun z : ℂ => a * z) (Eq.symm (add_sub_cancel_left C K))
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
  rw [harg]
  dsimp [Complex.finiteAbelPlanaLogRectangleIntegrand]
  exact
    Complex.mul_kernel_eq_constant_add_subtractiveRemainder
      (Complex.finiteAbelPlanaLogSummand w ((x : ℂ) - (T : ℂ) * Complex.I))
      (Complex.finiteAbelPlanaCotangentKernel ((x : ℂ) - (T : ℂ) * Complex.I))
      ((Real.pi : ℂ) * Complex.I)

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
  rw [harg]
  dsimp [Complex.finiteAbelPlanaLogRectangleIntegrand]
  exact
    Complex.mul_kernel_eq_negConstant_add_additiveRemainder
      (Complex.finiteAbelPlanaLogSummand w ((x : ℂ) + (T : ℂ) * Complex.I))
      (Complex.finiteAbelPlanaCotangentKernel ((x : ℂ) + (T : ℂ) * Complex.I))
      ((Real.pi : ℂ) * Complex.I)

/-- The lower horizontal side splits into its lower-half-plane constant
cotangent part plus the named decaying bottom horizontal edge. -/
theorem Complex.finiteAbelPlana_log_lowerHorizontalSide_eq_constant_add_bottomEdge
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
      Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
        Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T := by
  dsimp [Complex.finiteAbelPlanaLogFiniteHeightLowerSide,
    Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide,
    Complex.finiteAbelPlanaLogBottomHorizontalEdge]
  rw [show
      (fun x : ℝ =>
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((x : ℂ) - Complex.I * (T : ℂ))) =
      (fun x : ℝ =>
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) - (T : ℂ) * Complex.I) *
          ((Real.pi : ℂ) * Complex.I) +
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) - (T : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) - (T : ℂ) * Complex.I) -
            (Real.pi : ℂ) * Complex.I)) by
      funext x
      exact Complex.finiteAbelPlana_lowerHorizontal_integrand_split w x T]
  rw [intervalIntegral.integral_add]
  rfl

/-- The upper horizontal side splits into its upper-half-plane constant
cotangent part plus the named decaying top horizontal edge. -/
theorem Complex.finiteAbelPlana_log_upperHorizontalSide_eq_constant_add_topEdge
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
      Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
        Complex.finiteAbelPlanaLogTopHorizontalEdge N w T := by
  dsimp [Complex.finiteAbelPlanaLogFiniteHeightUpperSide,
    Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide,
    Complex.finiteAbelPlanaLogTopHorizontalEdge]
  rw [show
      (fun x : ℝ =>
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((x : ℂ) + Complex.I * (T : ℂ))) =
      (fun x : ℝ =>
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) + (T : ℂ) * Complex.I) *
          (-(Real.pi : ℂ) * Complex.I) +
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) + (T : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) + (T : ℂ) * Complex.I) +
            (Real.pi : ℂ) * Complex.I)) by
      funext x
      exact Complex.finiteAbelPlana_upperHorizontal_integrand_split w x T]
  rw [intervalIntegral.integral_add]
  rfl

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
  dsimp [Complex.finiteAbelPlanaLogLeftBoundaryFace,
    Complex.finiteAbelPlanaLogRightBoundaryFace,
    Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression]
  exact Complex.finiteAbelPlana_boundaryFace_collect
    (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T)
    (Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T)
    (Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T)
    (Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T)

/-- Unfolding of the raw left boundary face. -/
theorem Complex.finiteAbelPlana_log_leftBoundaryFace_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLeftBoundaryFace N w T =
      -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T := by
  rfl

/-- Unfolding of the raw right boundary face. -/
theorem Complex.finiteAbelPlana_log_rightBoundaryFace_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogRightBoundaryFace N w T =
      Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T := by
  rfl

/-- Named lower boundary-face contribution in the coupled Abel-Plana
normalization. -/
noncomputable def Complex.finiteAbelPlanaLogLowerNamedBoundaryFace
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  (∫ x : ℝ in (0 : ℝ)..(N + 1 : ℝ),
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
  dsimp [Complex.finiteAbelPlanaLogLowerNamedBoundaryFace,
    Complex.finiteAbelPlanaLogUpperNamedBoundaryFace,
    Complex.finiteAbelPlanaLogNamedBoundaryFaceSum,
    Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression,
    Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression]
  exact Complex.finiteAbelPlana_namedBoundary_collect
    ((∫ x : ℝ in (0 : ℝ)..(N + 1 : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
      Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w)
    (Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)
    (Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)

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
  -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
    Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε +
      Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε

/-- Residue-normalized principal-value right endpoint boundary face after
splitting into the constant cotangent primitive and the normalized exponential
remainder. -/
noncomputable def Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
    Complex.I * Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε +
      Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε

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
  dsimp [Complex.finiteAbelPlanaLogRectangleIntegrand]
  exact Complex.mul_eq_mul_add_mul_sub
    (Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)))
    (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)))
    ((Real.pi : ℂ) * Complex.I)

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
  dsimp [Complex.finiteAbelPlanaLogRectangleIntegrand]
  exact Complex.mul_eq_mul_neg_add_mul_add
    (Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)))
    (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)))
    ((Real.pi : ℂ) * Complex.I)

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
  dsimp [Complex.finiteAbelPlanaLogRectangleIntegrand]
  exact Complex.mul_eq_mul_add_mul_sub
    (Complex.finiteAbelPlanaLogSummand w ((N + 1 : ℂ) + Complex.I * (y : ℂ)))
    (Complex.finiteAbelPlanaCotangentKernel ((N + 1 : ℂ) + Complex.I * (y : ℂ)))
    ((Real.pi : ℂ) * Complex.I)

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
  dsimp [Complex.finiteAbelPlanaLogRectangleIntegrand]
  exact Complex.mul_eq_mul_neg_add_mul_add
    (Complex.finiteAbelPlanaLogSummand w ((N + 1 : ℂ) + Complex.I * (y : ℂ)))
    (Complex.finiteAbelPlanaCotangentKernel ((N + 1 : ℂ) + Complex.I * (y : ℂ)))
    ((Real.pi : ℂ) * Complex.I)

/-- The left vertical side is the sum of its constant-kernel and
exponential-remainder parts. -/
theorem Complex.finiteAbelPlana_log_leftVerticalSide_eq_constant_add_remainder
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T =
      Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T +
        Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSide w T := by
  dsimp [Complex.finiteAbelPlanaLogFiniteHeightLeftSide,
    Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide,
    Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSide]
  exact Complex.verticalSide_split_collect
    (∫ y : ℝ in (-T)..(0 : ℝ),
      Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
        ((Real.pi : ℂ) * Complex.I))
    (∫ y : ℝ in (0 : ℝ)..T,
      Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
        (-(Real.pi : ℂ) * Complex.I))
    (∫ y : ℝ in (-T)..(0 : ℝ),
      Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) -
          (Real.pi : ℂ) * Complex.I))
    (∫ y : ℝ in (0 : ℝ)..T,
      Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) +
          (Real.pi : ℂ) * Complex.I))

/-- The right vertical side is the sum of its constant-kernel and
exponential-remainder parts. -/
theorem Complex.finiteAbelPlana_log_rightVerticalSide_eq_constant_add_remainder
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T =
      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T +
        Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSide N w T := by
  dsimp [Complex.finiteAbelPlanaLogFiniteHeightRightSide,
    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide,
    Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSide]
  exact Complex.verticalSide_split_collect
    (∫ y : ℝ in (-T)..(0 : ℝ),
      Complex.finiteAbelPlanaLogSummand w ((N + 1 : ℂ) + Complex.I * (y : ℂ)) *
        ((Real.pi : ℂ) * Complex.I))
    (∫ y : ℝ in (0 : ℝ)..T,
      Complex.finiteAbelPlanaLogSummand w ((N + 1 : ℂ) + Complex.I * (y : ℂ)) *
        (-(Real.pi : ℂ) * Complex.I))
    (∫ y : ℝ in (-T)..(0 : ℝ),
      Complex.finiteAbelPlanaLogSummand w ((N + 1 : ℂ) + Complex.I * (y : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel ((N + 1 : ℂ) + Complex.I * (y : ℂ)) -
          (Real.pi : ℂ) * Complex.I))
    (∫ y : ℝ in (0 : ℝ)..T,
      Complex.finiteAbelPlanaLogSummand w ((N + 1 : ℂ) + Complex.I * (y : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel ((N + 1 : ℂ) + Complex.I * (y : ℂ)) +
          (Real.pi : ℂ) * Complex.I))

/-- Left constant-kernel primitive assembly.

The upper horizontal constant side and the constant part of the oriented left
vertical side are exactly the real segment plus endpoint principal-value
contribution. -/
theorem Complex.finiteAbelPlana_log_leftConstantKernelPrimitiveAssembly
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
        Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T =
      Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w := by
  dsimp [Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide,
    Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide,
    Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression,
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution,
    Complex.finiteAbelPlanaLogSummandHalfEndpoints]
  ring

/-- Right constant-kernel primitive assembly.

The lower horizontal constant side and the constant part of the oriented right
vertical side cancel after endpoint normalization. -/
theorem Complex.finiteAbelPlana_log_rightConstantKernelPrimitiveAssembly
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
        Complex.I * Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T =
      0 := by
  dsimp [Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide,
    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide]
  ring

/-- Left exponential-remainder vertical assembly.

The exponential part of the oriented left vertical side is the negative lower
Abel-Plana logarithmic-jump integral. -/
theorem Complex.finiteAbelPlana_log_leftVerticalRemainderAssembly
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    -Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSide w T =
      -Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T := by
  dsimp [Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSide,
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo,
    Complex.finiteAbelPlanaLogLowerVerticalIntegrand]
  ring

/-- Right exponential-remainder vertical assembly.

The exponential part of the oriented right vertical side is the negative upper
Abel-Plana endpoint logarithmic-jump integral. -/
theorem Complex.finiteAbelPlana_log_rightVerticalRemainderAssembly
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.I * Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSide N w T =
      -Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T := by
  dsimp [Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSide,
    Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo,
    Complex.finiteAbelPlanaLogUpperVerticalIntegrand]
  ring

/-- Oriented left vertical side assembly.

After splitting the interval `[-T,T]` at zero and using the cotangent
half-plane formulas on `I t` and `-I t`, the oriented left vertical side
reconstructs the upper constant horizontal contribution together with the
lower named Abel-Plana boundary face.  This is the local owner theorem for the
left-side branch-jump calculation. -/
theorem Complex.finiteAbelPlana_log_orientedLeftVerticalSide_eq_upperConstant_add_lowerNamedFace
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    -Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T =
      Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
        Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T := by
  have hsplit :
      Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T =
        Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T +
          Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSide w T :=
    Complex.finiteAbelPlana_log_leftVerticalSide_eq_constant_add_remainder
      w T hT
  have hconst :
      -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
          Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T =
        Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w :=
    Complex.finiteAbelPlana_log_leftConstantKernelPrimitiveAssembly
      N w T hT
  have hrem :
      -Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSide w T =
        -Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T :=
    Complex.finiteAbelPlana_log_leftVerticalRemainderAssembly w T hT
  rw [hsplit]
  dsimp [Complex.finiteAbelPlanaLogLowerNamedBoundaryFace,
    Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression]
  calc
    -Complex.I *
        (Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T +
          Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSide w T) =
      Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
        ((-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T) +
          (-Complex.I *
            Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSide w T)) := by
      exact Complex.leftOrientedVertical_assembly_collect
        (Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T)
        (Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)
        (Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSide w T)
    _ =
      Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
        (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w -
          Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T) := by
      exact congrArg
        (fun z : ℂ =>
          Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T + z)
        (by
          calc
            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T) +
                (-Complex.I *
                  Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSide w T) =
              Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
                (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T) := by
              exact congrArg₂ HAdd.hAdd hconst hrem
            _ =
              Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w -
                Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T := by
              exact Complex.leftOrientedVertical_after_substitution
                (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w)
                (Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T))
    _ =
      Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
        ((∫ x : ℝ in (0 : ℝ)..(N + 1 : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w -
          Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T) := by
      rfl

/-- Oriented right vertical side assembly.

After splitting the right vertical side at zero and applying the same
cotangent half-plane formulas at the endpoint `N + 1`, the oriented right
vertical side is the upper named boundary face after removing the lower
constant horizontal contribution. -/
theorem Complex.finiteAbelPlana_log_orientedRightVerticalSide_eq_upperNamed_minus_lowerConstant
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T =
      Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T -
        Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T := by
  have hsplit :
      Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T =
        Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSide N w T :=
    Complex.finiteAbelPlana_log_rightVerticalSide_eq_constant_add_remainder
      N w T hT
  have hconst :
      Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
          Complex.I * Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T =
        0 :=
    Complex.finiteAbelPlana_log_rightConstantKernelPrimitiveAssembly
      N w T hT
  have hrem :
      Complex.I * Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSide N w T =
        -Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T :=
    Complex.finiteAbelPlana_log_rightVerticalRemainderAssembly
      N w T hT
  rw [hsplit]
  dsimp [Complex.finiteAbelPlanaLogUpperNamedBoundaryFace]
  calc
    Complex.I *
        (Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSide N w T) =
      (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
          Complex.I * Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T) +
        (Complex.I * Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSide N w T) -
          Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T := by
      exact Complex.rightOrientedVertical_assembly_collect
        (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T)
        (Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)
        (Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSide N w T)
    _ =
      0 + (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T) -
        Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T := by
      exact congrArg₂
        (fun a b : ℂ =>
          a + b -
            Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T)
        hconst hrem
    _ =
      -Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T := by
      exact Complex.rightOrientedVertical_after_substitution
        (Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)
        (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T)

/-- Left half-contour Abel-Plana assembly.

This is the owner statement for the left/top half of the finite rectangle:
the upper horizontal constant cotangent term, the oriented left vertical side,
and the endpoint principal-value indentation assemble to the real segment plus
the lower Abel-Plana logarithmic-jump integral.

The proof is the standard half-contour form of Abel-Plana: split the left
vertical integral at `0`, use the upper/lower half-plane cotangent exponential
formulas on `±I t`, and use the principal-log jump
`log (w + I t) - log (w - I t)` to identify the lower vertical kernel. -/
theorem Complex.finiteAbelPlana_log_leftHalfContourAssembly
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogLeftBoundaryFace N w T =
      Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T := by
  have hvertical :
      -Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T =
        Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T :=
    Complex.finiteAbelPlana_log_orientedLeftVerticalSide_eq_upperConstant_add_lowerNamedFace
      N w T hT
  dsimp [Complex.finiteAbelPlanaLogLeftBoundaryFace]
  calc
    -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T =
      -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
        (-Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T) := by
      exact sub_eq_add_neg
        (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T)
        (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T)
    _ =
      -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
        (Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T) := by
      exact congrArg
        (fun z : ℂ =>
          -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T + z)
        hvertical
    _ = Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T := by
      exact Complex.leftHalfContour_cancel_horizontal
        (Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T)
        (Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T)

/-- Right half-contour Abel-Plana assembly.

This is the owner statement for the right/bottom half of the finite rectangle:
the lower horizontal constant cotangent term and the oriented right vertical
side assemble to the finite upper endpoint logarithmic-jump integral.

The proof is the same finite Abel-Plana side calculation at the endpoint
`M = N + 1`: split the right vertical side at `0`, rewrite cotangent in the two
half-planes, and identify the endpoint jump with
`binetAbelPlanaFiniteUpperLogJump`. -/
theorem Complex.finiteAbelPlana_log_rightHalfContourAssembly
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogRightBoundaryFace N w T =
      Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T := by
  have hvertical :
      Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T =
        Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T -
          Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T :=
    Complex.finiteAbelPlana_log_orientedRightVerticalSide_eq_upperNamed_minus_lowerConstant
      N w T hT
  dsimp [Complex.finiteAbelPlanaLogRightBoundaryFace]
  calc
    Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T =
      Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
        (Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T -
          Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T) := by
      exact congrArg
        (fun z : ℂ =>
          Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T + z)
        hvertical
    _ = Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T := by
      exact Complex.rightHalfContour_cancel_horizontal
        (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T)
        (Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T)

/-- The lower named boundary face unfolded into real-segment, endpoint, and
lower vertical integral pieces. -/
theorem Complex.finiteAbelPlana_log_lowerNamedBoundaryFace_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T =
      (∫ x : ℝ in (0 : ℝ)..(N + 1 : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
        Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w -
        Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T := by
  rfl

/-- The upper named boundary face unfolds to minus the upper vertical
integral. -/
theorem Complex.finiteAbelPlana_log_upperNamedBoundaryFace_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T =
      -Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T := by
  rfl

/-- Coupled lower-face Abel-Plana normalization.

This public face theorem is now a thin wrapper over the left half-contour
assembly theorem, which owns the cotangent/log-jump calculation. -/
theorem Complex.finiteAbelPlana_log_leftBoundaryFace_eq_lowerNamedBoundaryFace
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogLeftBoundaryFace N w T =
      Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T :=
  Complex.finiteAbelPlana_log_leftHalfContourAssembly N w T hT

/-- Coupled upper-face Abel-Plana normalization.

This public face theorem is now a thin wrapper over the right half-contour
assembly theorem, which owns the endpoint cotangent/log-jump calculation. -/
theorem Complex.finiteAbelPlana_log_rightBoundaryFace_eq_upperNamedBoundaryFace
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogRightBoundaryFace N w T =
      Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T :=
  Complex.finiteAbelPlana_log_rightHalfContourAssembly N w T hT

/-- PV left vertical side splits into its constant and exponential-remainder
parts. -/
theorem Complex.finiteAbelPlana_log_leftVerticalSidePV_eq_constant_add_remainder
    (w : ℂ)
    (T ε : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ε =
      Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε +
        Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePV w T ε := by
  dsimp [Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV,
    Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV,
    Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePV]
  exact Complex.verticalSide_split_collect
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
          (Real.pi : ℂ) * Complex.I))

/-- PV right vertical side splits into its constant and exponential-remainder
parts. -/
theorem Complex.finiteAbelPlana_log_rightVerticalSidePV_eq_constant_add_remainder
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ε =
      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε +
        Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePV N w T ε := by
  dsimp [Complex.finiteAbelPlanaLogFiniteHeightRightSidePV,
    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV,
    Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePV]
  exact Complex.verticalSide_split_collect
    (∫ y : ℝ in (-T)..(-ε),
      Complex.finiteAbelPlanaLogSummand w ((N + 1 : ℂ) + Complex.I * (y : ℂ)) *
        ((Real.pi : ℂ) * Complex.I))
    (∫ y : ℝ in ε..T,
      Complex.finiteAbelPlanaLogSummand w ((N + 1 : ℂ) + Complex.I * (y : ℂ)) *
        (-(Real.pi : ℂ) * Complex.I))
    (∫ y : ℝ in (-T)..(-ε),
      Complex.finiteAbelPlanaLogSummand w ((N + 1 : ℂ) + Complex.I * (y : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel ((N + 1 : ℂ) + Complex.I * (y : ℂ)) -
          (Real.pi : ℂ) * Complex.I))
    (∫ y : ℝ in ε..T,
      Complex.finiteAbelPlanaLogSummand w ((N + 1 : ℂ) + Complex.I * (y : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel ((N + 1 : ℂ) + Complex.I * (y : ℂ)) +
          (Real.pi : ℂ) * Complex.I))

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

/-- The left vertical logarithmic path lies in the principal slit plane in
the open right half-plane. -/
theorem Complex.finiteAbelPlana_log_leftVerticalPath_mem_slitPlane
    {w : ℂ}
    (hw : 0 < w.re)
    (y : ℝ) :
    w + Complex.I * (y : ℂ) ∈ Complex.slitPlane := by
  have hre : 0 < (w + Complex.I * (y : ℂ)).re := by
    simpa using hw
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
    simpa [add_assoc] using add_pos_of_pos_of_nonneg hw hN_nonneg
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
  have hpath :
      (fun y : ℝ =>
        w + (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ))) =
        fun y : ℝ =>
          w + ((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ) := by
    funext y
    exact add_assoc w (((N + 1 : ℕ) : ℂ)) (Complex.I * (y : ℂ))
  rw [hpath]
  exact
    ((continuous_const.add continuous_const).add
      (continuous_const.mul Complex.continuous_ofReal)).clog
      (fun y => Complex.finiteAbelPlana_log_rightVerticalPath_mem_slitPlane N hw y)

/-- Interval integrability of the left constant-side vertical integrand. -/
theorem Complex.intervalIntegrable_finiteAbelPlana_log_leftConstantVerticalIntegrand
    {w : ℂ}
    (hw : 0 < w.re)
    (a b : ℝ)
    (c : ℂ) :
    IntervalIntegrable
      (fun y : ℝ =>
        Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) * c)
      volume a b := by
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
      volume a b := by
  exact
    ((Complex.continuous_finiteAbelPlana_log_rightVerticalSummand N hw).mul
      continuous_const).continuousOn.intervalIntegrable


end

end LFunctions
end Boundary
