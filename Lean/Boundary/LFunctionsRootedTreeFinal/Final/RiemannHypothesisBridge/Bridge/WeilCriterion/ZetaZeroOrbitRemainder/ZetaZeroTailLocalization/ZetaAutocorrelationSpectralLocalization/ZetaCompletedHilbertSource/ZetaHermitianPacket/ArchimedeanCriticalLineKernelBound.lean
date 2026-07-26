import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ArchimedeanCriticalLineGamma

/-!
# Linear bound for the centered archimedean kernel

The direct quarter-line Abel-Plana estimate controls the ordinary Gamma term.
The elementary pi term and the reciprocal poles are then added explicitly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex

namespace ZetaAdmissibleFunction

/-- The centered spectral line is the fixed real-part line with real part `1 / 2`. -/
private theorem zetaCompletedCenteredSpectralLine_eq_fixedHalfLine (t : ℝ) :
    zetaCompletedCenteredSpectralLine t =
      ((1 / 2 : ℝ) + (t : ℂ) * Complex.I : ℂ) :=
  Eq.trans
    (Eq.refl _ :
      zetaCompletedCenteredSpectralLine t =
        (1 / 2 : ℂ) + (t : ℂ) * Complex.I)
    (congrArg
      (fun half : ℂ => half + (t : ℂ) * Complex.I)
      (Eq.symm (Complex.ofReal_div (1 : ℝ) (2 : ℝ))))

/-- Negating the complex half is the coercion of the negated real half. -/
private theorem zetaCompleted_neg_complexHalf_eq_ofReal_negHalf :
    -(1 / 2 : ℂ) = ((-(1 / 2 : ℝ)) : ℂ) := by
  have hhalf_complex : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) :=
    Eq.symm (Complex.ofReal_div (1 : ℝ) (2 : ℝ))
  have hneg_half :
      -((1 / 2 : ℝ) : ℂ) = ((-(1 / 2 : ℝ)) : ℂ) := by
    exact Eq.refl _
  exact Eq.trans (congrArg Neg.neg hhalf_complex) hneg_half

/-- Linear-bound constant for the half-weighted ordinary Gamma logarithmic
derivative on the quarter-line. -/
noncomputable def zetaCompletedQuarterLineHalfGammaBoundConstant : ℝ :=
  ‖(1 / 2 : ℂ)‖ *
    |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant (1 / 4 : ℝ)|

/-- The quarter-line half-Gamma bound constant is nonnegative. -/
theorem zetaCompletedQuarterLineHalfGammaBoundConstant_nonneg :
    0 ≤ zetaCompletedQuarterLineHalfGammaBoundConstant := by
  exact mul_nonneg
    (norm_nonneg (1 / 2 : ℂ))
    (abs_nonneg
      (Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
        (1 / 4 : ℝ)))

/-- Halving the height does not increase its Japanese bracket. -/
theorem zetaCompleted_halfHeight_one_add_norm_le (t : ℝ) :
    1 + ‖t / 2‖ ≤ 1 + ‖t‖ := by
  have denominatorNormLower : (1 : ℝ) ≤ ‖(2 : ℝ)‖ := by
    have twoNorm : ‖(2 : ℝ)‖ = 2 :=
      Real.norm_of_nonneg zero_le_two
    exact Eq.subst
      (motive := fun value : ℝ => 1 ≤ value)
      twoNorm.symm
      one_le_two
  have heightNorm : ‖t / 2‖ ≤ ‖t‖ := by
    calc
      ‖t / 2‖ = ‖t‖ / ‖(2 : ℝ)‖ := by
        exact norm_div t (2 : ℝ)
      _ ≤ ‖t‖ := by
        exact div_le_self (norm_nonneg t) denominatorNormLower
  exact add_le_add_left heightNorm 1

/-- The half-weighted ordinary Gamma logarithmic derivative on the quarter-line
has a linear height bound. -/
theorem zetaCompletedQuarterLineHalfGamma_logDerivative_bound (t : ℝ) :
    ‖(deriv Complex.Gamma
          ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I) * (1 / 2 : ℂ)) /
        Complex.Gamma
          ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I)‖ ≤
      zetaCompletedQuarterLineHalfGammaBoundConstant * (1 + ‖t‖) := by
  let point : ℂ :=
    ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I : ℂ)
  let quotient : ℂ :=
    deriv Complex.Gamma point / Complex.Gamma point
  have quarterPositive : (0 : ℝ) < (1 / 4 : ℝ) := by
    exact div_pos zero_lt_one (by exact zero_lt_four)
  have directBound :=
    Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_direct
      quarterPositive (t / 2)
  have directAbsoluteBound :
      ‖deriv Complex.Gamma point / Complex.Gamma point‖ ≤
        |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
            (1 / 4 : ℝ)| *
          (1 + ‖t / 2‖) := by
    have bracketNonnegative : 0 ≤ 1 + ‖t / 2‖ :=
      Real.zero_le_one_add_norm (t / 2)
    have constantBound :
        Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
            (1 / 4 : ℝ) ≤
          |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
            (1 / 4 : ℝ)| :=
      le_abs_self _
    exact directBound.trans
      (mul_le_mul_of_nonneg_right constantBound bracketNonnegative)
  have enlargedBound :
      ‖quotient‖ ≤
        |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
            (1 / 4 : ℝ)| *
          (1 + ‖t‖) := by
    have constantNonnegative :
        0 ≤
          |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
            (1 / 4 : ℝ)| :=
      abs_nonneg _
    exact directAbsoluteBound.trans
      (mul_le_mul_of_nonneg_left
        (zetaCompleted_halfHeight_one_add_norm_le t)
        constantNonnegative)
  have weightedIdentity :
      (deriv Complex.Gamma point * (1 / 2 : ℂ)) /
          Complex.Gamma point =
        quotient * (1 / 2 : ℂ) := by
    exact mul_div_right_comm
      (deriv Complex.Gamma point) (1 / 2 : ℂ) (Complex.Gamma point)
  have weightedNorm :
      ‖(deriv Complex.Gamma point * (1 / 2 : ℂ)) /
          Complex.Gamma point‖ =
        ‖quotient‖ * ‖(1 / 2 : ℂ)‖ := by
    exact Eq.trans
      (congrArg norm weightedIdentity)
      (norm_mul quotient (1 / 2 : ℂ))
  have multipliedBound :
      ‖quotient‖ * ‖(1 / 2 : ℂ)‖ ≤
        (|Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
            (1 / 4 : ℝ)| * (1 + ‖t‖)) * ‖(1 / 2 : ℂ)‖ :=
    mul_le_mul_of_nonneg_right enlargedBound (norm_nonneg (1 / 2 : ℂ))
  have scalarRearrangement :
      (|Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
          (1 / 4 : ℝ)| * (1 + ‖t‖)) * ‖(1 / 2 : ℂ)‖ =
        zetaCompletedQuarterLineHalfGammaBoundConstant * (1 + ‖t‖) := by
    calc
      (|Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
          (1 / 4 : ℝ)| * (1 + ‖t‖)) * ‖(1 / 2 : ℂ)‖ =
          |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
              (1 / 4 : ℝ)| *
            ((1 + ‖t‖) * ‖(1 / 2 : ℂ)‖) := by
        exact mul_assoc _ _ _
      _ =
          |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
              (1 / 4 : ℝ)| *
            (‖(1 / 2 : ℂ)‖ * (1 + ‖t‖)) := by
        exact congrArg
          (fun value : ℝ =>
            |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
              (1 / 4 : ℝ)| * value)
          (mul_comm (1 + ‖t‖) ‖(1 / 2 : ℂ)‖)
      _ =
          (‖(1 / 2 : ℂ)‖ *
            |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
              (1 / 4 : ℝ)|) * (1 + ‖t‖) := by
        exact Eq.trans
          (mul_assoc
            |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
              (1 / 4 : ℝ)|
            ‖(1 / 2 : ℂ)‖ (1 + ‖t‖)).symm
          (congrArg (fun value : ℝ => value * (1 + ‖t‖))
            (mul_comm
              |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
                (1 / 4 : ℝ)|
              ‖(1 / 2 : ℂ)‖))
      _ = zetaCompletedQuarterLineHalfGammaBoundConstant * (1 + ‖t‖) := by
        exact Eq.refl _
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤
        zetaCompletedQuarterLineHalfGammaBoundConstant * (1 + ‖t‖))
    (show
      (deriv Complex.Gamma point * (1 / 2 : ℂ)) /
          Complex.Gamma point =
        (deriv Complex.Gamma
            ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I) * (1 / 2 : ℂ)) /
          Complex.Gamma
            ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I)
      from Eq.refl _)
    (Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          zetaCompletedQuarterLineHalfGammaBoundConstant * (1 + ‖t‖))
      weightedNorm.symm
      (multipliedBound.trans_eq scalarRearrangement))

/-- Linear-bound constant for the `Gammaℝ` logarithmic derivative on the
centered critical line. -/
noncomputable def zetaCompletedCenteredGammaRealBoundConstant : ℝ :=
  ‖Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))‖ +
    zetaCompletedQuarterLineHalfGammaBoundConstant

/-- The centered `Gammaℝ` logarithmic-derivative constant is nonnegative. -/
theorem zetaCompletedCenteredGammaRealBoundConstant_nonneg :
    0 ≤ zetaCompletedCenteredGammaRealBoundConstant := by
  exact add_nonneg
    (norm_nonneg (Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))))
    zetaCompletedQuarterLineHalfGammaBoundConstant_nonneg

/-- The `Gammaℝ` logarithmic derivative has linear growth on the centered
critical line. -/
theorem zetaCompletedCenteredGammaReal_logDerivative_bound (t : ℝ) :
    ‖deriv Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t) /
        Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t)‖ ≤
      zetaCompletedCenteredGammaRealBoundConstant * (1 + ‖t‖) := by
  let piTerm : ℂ :=
    Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))
  let gammaTerm : ℂ :=
    (deriv Complex.Gamma
        ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I) * (1 / 2 : ℂ)) /
      Complex.Gamma
        ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I)
  have decomposition :=
    GammaReal_logDerivative_centeredSpectralLine_eq_quarterLine t
  have triangle : ‖piTerm + gammaTerm‖ ≤ ‖piTerm‖ + ‖gammaTerm‖ :=
    norm_add_le piTerm gammaTerm
  have piBound : ‖piTerm‖ ≤ ‖piTerm‖ * (1 + ‖t‖) := by
    calc
      ‖piTerm‖ = ‖piTerm‖ * 1 := by
        exact (mul_one ‖piTerm‖).symm
      _ ≤ ‖piTerm‖ * (1 + ‖t‖) := by
        exact mul_le_mul_of_nonneg_left
          (Real.one_le_one_add_norm t) (norm_nonneg piTerm)
  have gammaBound :
      ‖gammaTerm‖ ≤
        zetaCompletedQuarterLineHalfGammaBoundConstant * (1 + ‖t‖) :=
    zetaCompletedQuarterLineHalfGamma_logDerivative_bound t
  have sumBound :
      ‖piTerm‖ + ‖gammaTerm‖ ≤
        ‖piTerm‖ * (1 + ‖t‖) +
          zetaCompletedQuarterLineHalfGammaBoundConstant * (1 + ‖t‖) :=
    add_le_add piBound gammaBound
  have factorEquality :
      ‖piTerm‖ * (1 + ‖t‖) +
          zetaCompletedQuarterLineHalfGammaBoundConstant * (1 + ‖t‖) =
        zetaCompletedCenteredGammaRealBoundConstant * (1 + ‖t‖) := by
    exact (add_mul ‖piTerm‖
      zetaCompletedQuarterLineHalfGammaBoundConstant (1 + ‖t‖)).symm
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤
        zetaCompletedCenteredGammaRealBoundConstant * (1 + ‖t‖))
    decomposition.symm
    (triangle.trans (sumBound.trans_eq factorEquality))

/-- Uniform-bound constant for the two elementary completed-zeta pole terms on
the centered critical line. -/
noncomputable def zetaCompletedCenteredElementaryPoleBoundConstant : ℝ :=
  ‖(-1 : ℂ)‖ * |(1 / 2 : ℝ)|⁻¹ +
    ‖(-1 : ℂ)‖ * |(-(1 / 2 : ℝ))|⁻¹

/-- The elementary pole bound constant is nonnegative. -/
theorem zetaCompletedCenteredElementaryPoleBoundConstant_nonneg :
    0 ≤ zetaCompletedCenteredElementaryPoleBoundConstant := by
  exact add_nonneg
    (mul_nonneg (norm_nonneg (-1 : ℂ))
      (inv_nonneg.mpr (abs_nonneg (1 / 2 : ℝ))))
    (mul_nonneg (norm_nonneg (-1 : ℂ))
      (inv_nonneg.mpr (abs_nonneg (-(1 / 2 : ℝ)))))

/-- The first elementary reciprocal pole is uniformly bounded on the centered
critical line. -/
theorem zetaCompletedCentered_zeroPole_bound (t : ℝ) :
    ‖(-1 : ℂ) / zetaCompletedCenteredSpectralLine t‖ ≤
      (‖(-1 : ℂ)‖ * |(1 / 2 : ℝ)|⁻¹) * (1 + ‖t‖) := by
  have inverseBound :
      ‖(zetaCompletedCenteredSpectralLine t)⁻¹‖ ≤
        |(1 / 2 : ℝ)|⁻¹ * (1 + ‖t‖) := by
    exact Eq.subst
      (motive := fun line : ℂ =>
        ‖line⁻¹‖ ≤ |(1 / 2 : ℝ)|⁻¹ * (1 + ‖t‖))
      (zetaCompletedCenteredSpectralLine_eq_fixedHalfLine t).symm
      (Complex.fixedRealPartLine_inv_norm_le_abs_re_inv_mul_one_add_norm
        (ne_of_gt one_half_pos) t)
  have divisionIdentity :
      (-1 : ℂ) / zetaCompletedCenteredSpectralLine t =
        (-1 : ℂ) * (zetaCompletedCenteredSpectralLine t)⁻¹ :=
    div_eq_mul_inv (-1 : ℂ) (zetaCompletedCenteredSpectralLine t)
  have productNorm :
      ‖(-1 : ℂ) * (zetaCompletedCenteredSpectralLine t)⁻¹‖ =
        ‖(-1 : ℂ)‖ * ‖(zetaCompletedCenteredSpectralLine t)⁻¹‖ :=
    norm_mul (-1 : ℂ) (zetaCompletedCenteredSpectralLine t)⁻¹
  have multipliedBound :
      ‖(-1 : ℂ)‖ * ‖(zetaCompletedCenteredSpectralLine t)⁻¹‖ ≤
        ‖(-1 : ℂ)‖ * (|(1 / 2 : ℝ)|⁻¹ * (1 + ‖t‖)) :=
    mul_le_mul_of_nonneg_left inverseBound (norm_nonneg (-1 : ℂ))
  have association :
      ‖(-1 : ℂ)‖ * (|(1 / 2 : ℝ)|⁻¹ * (1 + ‖t‖)) =
        (‖(-1 : ℂ)‖ * |(1 / 2 : ℝ)|⁻¹) * (1 + ‖t‖) :=
    (mul_assoc ‖(-1 : ℂ)‖ |(1 / 2 : ℝ)|⁻¹ (1 + ‖t‖)).symm
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤
        (‖(-1 : ℂ)‖ * |(1 / 2 : ℝ)|⁻¹) * (1 + ‖t‖))
    divisionIdentity.symm
    (Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          (‖(-1 : ℂ)‖ * |(1 / 2 : ℝ)|⁻¹) * (1 + ‖t‖))
      productNorm.symm
      (multipliedBound.trans_eq association))

/-- Subtracting one from a centered critical-line point gives the fixed line
with real part negative one half. -/
theorem zetaCompletedCenteredSpectralLine_sub_one (t : ℝ) :
    zetaCompletedCenteredSpectralLine t - 1 =
      (((-(1 / 2 : ℝ)) : ℂ) + (t : ℂ) * Complex.I) := by
  calc
    zetaCompletedCenteredSpectralLine t - 1 =
        (t : ℂ) * Complex.I + (1 / 2 : ℂ) - 1 := by
      exact congrArg (fun value : ℂ => value - 1)
        (add_comm (1 / 2 : ℂ) ((t : ℂ) * Complex.I))
    _ = (t : ℂ) * Complex.I + ((1 / 2 : ℂ) - 1) := by
      exact add_sub_assoc ((t : ℂ) * Complex.I) (1 / 2 : ℂ) 1
    _ = ((1 / 2 : ℂ) - 1) + (t : ℂ) * Complex.I := by
      exact add_comm ((t : ℂ) * Complex.I) ((1 / 2 : ℂ) - 1)
    _ = (-(1 / 2 : ℂ)) + (t : ℂ) * Complex.I := by
      have scalarEquality : (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) := by
        exact Eq.trans
          (neg_sub (1 : ℂ) (1 / 2 : ℂ)).symm
          (congrArg Neg.neg (sub_half (1 : ℂ)))
      exact congrArg
        (fun realPart : ℂ => realPart + (t : ℂ) * Complex.I)
        scalarEquality
    _ = (-(1 / 2 : ℝ) + (t : ℂ) * Complex.I : ℂ) := by
      exact congrArg
        (fun realPart : ℂ => realPart + (t : ℂ) * Complex.I)
        zetaCompleted_neg_complexHalf_eq_ofReal_negHalf

/-- The second elementary reciprocal pole is uniformly bounded on the centered
critical line. -/
theorem zetaCompletedCentered_onePole_bound (t : ℝ) :
    ‖(-1 : ℂ) / (zetaCompletedCenteredSpectralLine t - 1)‖ ≤
      (‖(-1 : ℂ)‖ * |(-(1 / 2 : ℝ))|⁻¹) * (1 + ‖t‖) := by
  have lineEquality := zetaCompletedCenteredSpectralLine_sub_one t
  have inverseBound :
      ‖(((-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ ≤
        |(-(1 / 2 : ℝ))|⁻¹ * (1 + ‖t‖) := by
    have fixedBound :
        ‖(((↑(-(1 / 2 : ℝ)) : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ ≤
          |(-(1 / 2 : ℝ))|⁻¹ * (1 + ‖t‖) :=
      Complex.fixedRealPartLine_inv_norm_le_abs_re_inv_mul_one_add_norm
        (ne_of_lt (neg_lt_zero.mpr one_half_pos)) t
    have hnegativeLine :
        ((↑(-(1 / 2 : ℝ)) : ℂ) + (t : ℂ) * Complex.I) =
          (-((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) :=
      congrArg
        (fun realPart : ℂ => realPart + (t : ℂ) * Complex.I)
        (map_neg Complex.ofRealHom (1 / 2 : ℝ))
    exact Eq.subst
      (motive := fun line : ℂ =>
        ‖line⁻¹‖ ≤ |(-(1 / 2 : ℝ))|⁻¹ * (1 + ‖t‖))
      hnegativeLine
      fixedBound
  have divisionIdentity :
      (-1 : ℂ) / (zetaCompletedCenteredSpectralLine t - 1) =
        (-1 : ℂ) *
          (((-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))⁻¹ := by
    exact Eq.trans
      (div_eq_mul_inv (-1 : ℂ)
        (zetaCompletedCenteredSpectralLine t - 1))
      (congrArg (fun denominator : ℂ => (-1 : ℂ) * denominator⁻¹)
        lineEquality)
  have productNorm :
      ‖(-1 : ℂ) *
          (((-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ =
        ‖(-1 : ℂ)‖ *
          ‖(((-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ :=
    norm_mul (-1 : ℂ)
      (((-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))⁻¹
  have multipliedBound :
      ‖(-1 : ℂ)‖ *
          ‖(((-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ ≤
        ‖(-1 : ℂ)‖ *
          (|(-(1 / 2 : ℝ))|⁻¹ * (1 + ‖t‖)) :=
    mul_le_mul_of_nonneg_left inverseBound (norm_nonneg (-1 : ℂ))
  have association :
      ‖(-1 : ℂ)‖ *
          (|(-(1 / 2 : ℝ))|⁻¹ * (1 + ‖t‖)) =
        (‖(-1 : ℂ)‖ * |(-(1 / 2 : ℝ))|⁻¹) * (1 + ‖t‖) :=
    (mul_assoc ‖(-1 : ℂ)‖ |(-(1 / 2 : ℝ))|⁻¹ (1 + ‖t‖)).symm
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤
        (‖(-1 : ℂ)‖ * |(-(1 / 2 : ℝ))|⁻¹) * (1 + ‖t‖))
    divisionIdentity.symm
    (Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          (‖(-1 : ℂ)‖ * |(-(1 / 2 : ℝ))|⁻¹) * (1 + ‖t‖))
      productNorm.symm
      (multipliedBound.trans_eq association))

/-- The combined elementary pole correction has a linear height bound. -/
theorem zetaCompletedCenteredElementaryPoleCorrection_bound (t : ℝ) :
    ‖(-1 : ℂ) / zetaCompletedCenteredSpectralLine t -
        1 / (zetaCompletedCenteredSpectralLine t - 1)‖ ≤
      zetaCompletedCenteredElementaryPoleBoundConstant * (1 + ‖t‖) := by
  have secondNumerator :
      -(1 / (zetaCompletedCenteredSpectralLine t - 1)) =
        (-1 : ℂ) / (zetaCompletedCenteredSpectralLine t - 1) := by
    exact (neg_div (zetaCompletedCenteredSpectralLine t - 1) (1 : ℂ)).symm
  have correctionEquality :
      (-1 : ℂ) / zetaCompletedCenteredSpectralLine t -
          1 / (zetaCompletedCenteredSpectralLine t - 1) =
        (-1 : ℂ) / zetaCompletedCenteredSpectralLine t +
          (-1 : ℂ) / (zetaCompletedCenteredSpectralLine t - 1) := by
    exact Eq.trans
      (sub_eq_add_neg
        ((-1 : ℂ) / zetaCompletedCenteredSpectralLine t)
        (1 / (zetaCompletedCenteredSpectralLine t - 1)))
      (congrArg
        (fun value : ℂ =>
          (-1 : ℂ) / zetaCompletedCenteredSpectralLine t + value)
        secondNumerator)
  have triangle := norm_add_le
    ((-1 : ℂ) / zetaCompletedCenteredSpectralLine t)
    ((-1 : ℂ) / (zetaCompletedCenteredSpectralLine t - 1))
  have sumBound := add_le_add
    (zetaCompletedCentered_zeroPole_bound t)
    (zetaCompletedCentered_onePole_bound t)
  have factorEquality :
      (‖(-1 : ℂ)‖ * |(1 / 2 : ℝ)|⁻¹) * (1 + ‖t‖) +
          (‖(-1 : ℂ)‖ * |(-(1 / 2 : ℝ))|⁻¹) * (1 + ‖t‖) =
        zetaCompletedCenteredElementaryPoleBoundConstant * (1 + ‖t‖) := by
    exact (add_mul
      (‖(-1 : ℂ)‖ * |(1 / 2 : ℝ)|⁻¹)
      (‖(-1 : ℂ)‖ * |(-(1 / 2 : ℝ))|⁻¹)
      (1 + ‖t‖)).symm
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤
        zetaCompletedCenteredElementaryPoleBoundConstant * (1 + ‖t‖))
    correctionEquality.symm
    (triangle.trans (sumBound.trans_eq factorEquality))

/-- Canonical linear-bound constant for the centered archimedean kernel. -/
noncomputable def zetaCompletedArchimedeanKernelLinearBoundConstant : ℝ :=
  zetaCompletedCenteredGammaRealBoundConstant +
    zetaCompletedCenteredElementaryPoleBoundConstant

/-- The centered archimedean kernel bound constant is nonnegative. -/
theorem zetaCompletedArchimedeanKernelLinearBoundConstant_nonneg :
    0 ≤ zetaCompletedArchimedeanKernelLinearBoundConstant := by
  exact add_nonneg
    zetaCompletedCenteredGammaRealBoundConstant_nonneg
    zetaCompletedCenteredElementaryPoleBoundConstant_nonneg

/-- The centered archimedean logarithmic-derivative kernel has linear growth. -/
theorem zetaCompletedArchimedeanLogDerivativeKernel_centered_bound (t : ℝ) :
    ‖zetaCompletedArchimedeanLogDerivativeKernel
        (zetaCompletedCenteredSpectralLine t)‖ ≤
      zetaCompletedArchimedeanKernelLinearBoundConstant * (1 + ‖t‖) := by
  let gammaQuotient : ℂ :=
    deriv Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t) /
      Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t)
  let poleCorrection : ℂ :=
    (-1 : ℂ) / zetaCompletedCenteredSpectralLine t -
      1 / (zetaCompletedCenteredSpectralLine t - 1)
  have inverseIdentity :=
    inverseGammaCompletionLogDeriv_centeredSpectralLine_eq t
  have inverseNorm :
      ‖inverseGammaCompletionLogDeriv
          (zetaCompletedCenteredSpectralLine t)‖ =
        ‖gammaQuotient‖ := by
    calc
      ‖inverseGammaCompletionLogDeriv
          (zetaCompletedCenteredSpectralLine t)‖ =
          ‖-deriv Complex.Gammaℝ
              (zetaCompletedCenteredSpectralLine t) /
            Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t)‖ := by
        exact congrArg norm inverseIdentity
      _ = ‖-gammaQuotient‖ := by
        exact congrArg norm
          (neg_div
            (Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t))
            (deriv Complex.Gammaℝ
              (zetaCompletedCenteredSpectralLine t)))
      _ = ‖gammaQuotient‖ :=
        norm_neg gammaQuotient
  have kernelEquality :
      zetaCompletedArchimedeanLogDerivativeKernel
          (zetaCompletedCenteredSpectralLine t) =
        inverseGammaCompletionLogDeriv
            (zetaCompletedCenteredSpectralLine t) - poleCorrection := by
    exact Eq.refl _
  have triangle :
      ‖inverseGammaCompletionLogDeriv
            (zetaCompletedCenteredSpectralLine t) - poleCorrection‖ ≤
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedCenteredSpectralLine t)‖ + ‖poleCorrection‖ :=
    norm_sub_le
      (inverseGammaCompletionLogDeriv
        (zetaCompletedCenteredSpectralLine t))
      poleCorrection
  have gammaBound :
      ‖inverseGammaCompletionLogDeriv
          (zetaCompletedCenteredSpectralLine t)‖ ≤
        zetaCompletedCenteredGammaRealBoundConstant * (1 + ‖t‖) :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          zetaCompletedCenteredGammaRealBoundConstant * (1 + ‖t‖))
      inverseNorm.symm
      (zetaCompletedCenteredGammaReal_logDerivative_bound t)
  have poleBound :
      ‖poleCorrection‖ ≤
        zetaCompletedCenteredElementaryPoleBoundConstant * (1 + ‖t‖) :=
    zetaCompletedCenteredElementaryPoleCorrection_bound t
  have sumBound := add_le_add gammaBound poleBound
  have factorEquality :
      zetaCompletedCenteredGammaRealBoundConstant * (1 + ‖t‖) +
          zetaCompletedCenteredElementaryPoleBoundConstant * (1 + ‖t‖) =
        zetaCompletedArchimedeanKernelLinearBoundConstant * (1 + ‖t‖) := by
    exact (add_mul
      zetaCompletedCenteredGammaRealBoundConstant
      zetaCompletedCenteredElementaryPoleBoundConstant
      (1 + ‖t‖)).symm
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤
        zetaCompletedArchimedeanKernelLinearBoundConstant * (1 + ‖t‖))
    kernelEquality.symm
    (triangle.trans (sumBound.trans_eq factorEquality))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
