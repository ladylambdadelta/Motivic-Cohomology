import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.FiniteSpectralZeroOperator
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGrowth

/-!
# Growth of finite spectral multiplier coefficients

A bounded completed-zero coefficient, a finite constant-coefficient spectral
multiplier, and completed-zero multiplicity have polynomial growth in centered
height.  This is the concrete growth input for atomic Fourier localization.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

open scoped ENNReal

/-- The norm of a completed-zero coordinate is bounded by its centered height. -/
theorem completedZero_norm_le_centeredHeight
    (rho : ZetaCompletedZeroCoordinate) :
    ‖(rho : ℂ)‖ ≤ zetaCompletedZeroCenteredHeight rho := by
  have hstrip := zetaCompletedZero_re_mem_centeredCriticalStrip rho
  have hrealAbsolute : |(rho : ℂ).re| ≤ (1 / 2 : ℝ) :=
    (abs_le).mpr hstrip
  have hhalfLeOne : (1 / 2 : ℝ) ≤ 1 :=
    (div_le_iff₀ (show (0 : ℝ) < 2 from zero_lt_two)).mpr
      (Eq.mp
        (congrArg
          (fun right : ℝ => (1 : ℝ) ≤ right)
          (one_mul (2 : ℝ)).symm)
        one_le_two)
  have hnormToCoordinates :
      ‖(rho : ℂ)‖ ≤ |(rho : ℂ).re| + |(rho : ℂ).im| :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤ |(rho : ℂ).re| + |(rho : ℂ).im|)
      (Complex.norm_eq_abs (rho : ℂ)).symm
      (Complex.abs_le_abs_re_add_abs_im (rho : ℂ))
  have hcoordinateBound :
      |(rho : ℂ).re| + |(rho : ℂ).im| ≤
        1 + |(rho : ℂ).im| :=
    add_le_add_right (le_trans hrealAbsolute hhalfLeOne) |(rho : ℂ).im|
  have hheightIdentity :
      zetaCompletedZeroCenteredHeight rho =
        1 + |(rho : ℂ).im| :=
    Eq.trans
      (zetaCompletedZeroCenteredHeight_eq_one_add_norm_im rho)
      (congrArg (fun value : ℝ => 1 + value)
        (Real.norm_eq_abs (rho : ℂ).im))
  exact le_trans hnormToCoordinates
    (Eq.subst
      (motive := fun value : ℝ =>
        |(rho : ℂ).re| + |(rho : ℂ).im| ≤ value)
      hheightIdentity.symm
      hcoordinateBound)

/-- Each factor of a finite spectral multiplier is bounded by a constant
times centered height. -/
theorem spectralDifference_norm_le_sampleBound_mul_centeredHeight
    (sample : ℂ)
    (rho : ZetaCompletedZeroCoordinate) :
    ‖sample - (rho : ℂ)‖ ≤
      (‖sample‖ + 1) * zetaCompletedZeroCenteredHeight rho := by
  let height : ℝ := zetaCompletedZeroCenteredHeight rho
  have hheightOne : 1 ≤ height :=
    zetaCompletedZeroCenteredHeight_ge_one rho
  have hsampleGrowth : ‖sample‖ ≤ ‖sample‖ * height :=
    le_mul_of_one_le_right (norm_nonneg sample) hheightOne
  have htriangle :
      ‖sample - (rho : ℂ)‖ ≤ ‖sample‖ + ‖(rho : ℂ)‖ :=
    norm_sub_le sample (rho : ℂ)
  have hcoordinate :
      ‖sample‖ + ‖(rho : ℂ)‖ ≤ ‖sample‖ + height :=
    add_le_add_left (completedZero_norm_le_centeredHeight rho) ‖sample‖
  have hlinear :
      ‖sample‖ + height ≤ (‖sample‖ + 1) * height := by
    have hadd : ‖sample‖ + height ≤ ‖sample‖ * height + height :=
      add_le_add_right hsampleGrowth height
    have hexpand :
        ‖sample‖ * height + height = (‖sample‖ + 1) * height :=
      Eq.trans
        (congrArg (fun value : ℝ => ‖sample‖ * height + value)
          (one_mul height).symm)
        (add_mul ‖sample‖ 1 height).symm
    exact hadd.trans_eq hexpand
  exact le_trans htriangle (le_trans hcoordinate hlinear)

/-- Product bound for an explicit list of finite spectral multiplier factors. -/
theorem spectralDifferenceListProduct_norm_le
    (samples : List ℂ)
    (rho : ZetaCompletedZeroCoordinate) :
    ‖(samples.map (fun sample : ℂ => sample - (rho : ℂ))).prod‖ ≤
      (samples.map (fun sample : ℂ => ‖sample‖ + 1)).prod *
        zetaCompletedZeroCenteredHeight rho ^ samples.length := by
  induction samples with
  | nil =>
      exact Eq.le
        (Eq.trans
          (norm_one : ‖(1 : ℂ)‖ = 1)
          (Eq.trans
            (one_mul (1 : ℝ)).symm
            (congrArg (fun value : ℝ => 1 * value)
              (pow_zero (zetaCompletedZeroCenteredHeight rho)).symm)))
  | cons sample samples hinduction =>
      have hfactor :=
        spectralDifference_norm_le_sampleBound_mul_centeredHeight sample rho
      have htailNonnegative :
          0 ≤ ‖(samples.map
            (fun value : ℂ => value - (rho : ℂ))).prod‖ :=
        norm_nonneg
          ((samples.map (fun value : ℂ => value - (rho : ℂ))).prod)
      have hfactorEnvelopeNonnegative :
          0 ≤ (‖sample‖ + 1) * zetaCompletedZeroCenteredHeight rho :=
        mul_nonneg
          (add_nonneg (norm_nonneg sample) zero_le_one)
          (le_trans zero_le_one
            (zetaCompletedZeroCenteredHeight_ge_one rho))
      have hproductBound :
          ‖sample - (rho : ℂ)‖ *
              ‖(samples.map
                (fun value : ℂ => value - (rho : ℂ))).prod‖ ≤
            ((‖sample‖ + 1) * zetaCompletedZeroCenteredHeight rho) *
              ((samples.map (fun value : ℂ => ‖value‖ + 1)).prod *
                zetaCompletedZeroCenteredHeight rho ^ samples.length) :=
        mul_le_mul hfactor hinduction htailNonnegative
          hfactorEnvelopeNonnegative
      have hreassociate :
          ((‖sample‖ + 1) * zetaCompletedZeroCenteredHeight rho) *
              ((samples.map (fun value : ℂ => ‖value‖ + 1)).prod *
                zetaCompletedZeroCenteredHeight rho ^ samples.length) =
            ((‖sample‖ + 1) *
              (samples.map (fun value : ℂ => ‖value‖ + 1)).prod) *
              zetaCompletedZeroCenteredHeight rho ^ (samples.length + 1) := by
        have hpowerSuccessor :
            zetaCompletedZeroCenteredHeight rho ^ (samples.length + 1) =
              zetaCompletedZeroCenteredHeight rho *
                zetaCompletedZeroCenteredHeight rho ^ samples.length :=
          Eq.trans
            (pow_add (zetaCompletedZeroCenteredHeight rho) samples.length 1)
            (Eq.trans
              (congrArg
                (fun value : ℝ =>
                  zetaCompletedZeroCenteredHeight rho ^ samples.length * value)
                (pow_one (zetaCompletedZeroCenteredHeight rho)))
              (mul_comm
                (zetaCompletedZeroCenteredHeight rho ^ samples.length)
                (zetaCompletedZeroCenteredHeight rho)))
        exact Eq.trans
          (mul_mul_mul_comm
            (‖sample‖ + 1)
            (zetaCompletedZeroCenteredHeight rho)
            ((samples.map (fun value : ℂ => ‖value‖ + 1)).prod)
            (zetaCompletedZeroCenteredHeight rho ^ samples.length))
          (congrArg
            (fun value : ℝ =>
              ((‖sample‖ + 1) *
                (samples.map (fun item : ℂ => ‖item‖ + 1)).prod) * value)
            hpowerSuccessor.symm)
      calc
        ‖(sample - (rho : ℂ)) *
            (samples.map (fun value : ℂ => value - (rho : ℂ))).prod‖ =
            ‖sample - (rho : ℂ)‖ *
              ‖(samples.map
                (fun value : ℂ => value - (rho : ℂ))).prod‖ :=
          norm_mul
            (sample - (rho : ℂ))
            ((samples.map (fun value : ℂ => value - (rho : ℂ))).prod)
        _ ≤
            ((‖sample‖ + 1) * zetaCompletedZeroCenteredHeight rho) *
              ((samples.map (fun value : ℂ => ‖value‖ + 1)).prod *
                zetaCompletedZeroCenteredHeight rho ^ samples.length) :=
          hproductBound
        _ =
            ((‖sample‖ + 1) *
              (samples.map (fun value : ℂ => ‖value‖ + 1)).prod) *
              zetaCompletedZeroCenteredHeight rho ^ (samples.length + 1) :=
          hreassociate
        _ =
            ((sample :: samples).map
              (fun value : ℂ => ‖value‖ + 1)).prod *
              zetaCompletedZeroCenteredHeight rho ^ (sample :: samples).length :=
          rfl

/-- A finite spectral-zero multiplier has polynomial growth in completed-zero
centered height. -/
theorem finiteSpectralZeroMultiplier_polynomialGrowth
    (P : Finset ℂ) :
    CompletedZeroAtomicPolynomialGrowth
      (fun rho : ZetaCompletedZeroCoordinate =>
        (P.toList.map (fun sample : ℂ => sample - (rho : ℂ))).prod) := by
  exact
    ⟨(P.toList.map (fun sample : ℂ => ‖sample‖ + 1)).prod,
      P.toList.length,
      List.prod_nonneg
        (fun value hvalue =>
          match List.mem_map.mp hvalue with
          | ⟨sample, hsample, hequal⟩ => by
              have hsampleNonnegative : 0 ≤ ‖sample‖ + 1 :=
                add_nonneg (norm_nonneg sample) zero_le_one
              have hproposition :
                  (0 ≤ ‖sample‖ + 1) = (0 ≤ value) :=
                congrArg (fun item : ℝ => 0 ≤ item) hequal
              exact Eq.mp hproposition hsampleNonnegative),
      spectralDifferenceListProduct_norm_le P.toList⟩

/-- Completed-zero multiplicity, viewed as a complex atomic coefficient, has
polynomial centered-height growth. -/
theorem completedZeroMultiplicity_polynomialGrowth
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    CompletedZeroAtomicPolynomialGrowth
      (fun rho : ZetaCompletedZeroCoordinate =>
        -((zetaZeroMultiplicity (rho : ℂ) : ℂ))) := by
  obtain ⟨bound, degree, hboundPositive, hestimate⟩ :=
    exists_zetaZeroMultiplicityGrowthEnvelope_bound
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  have hpolynomialBound :
      ∀ rho : ZetaCompletedZeroCoordinate,
        ‖-((zetaZeroMultiplicity (rho : ℂ) : ℂ))‖ ≤
          bound * zetaCompletedZeroCenteredHeight rho ^ degree := by
    intro rho
    have hnegativeNorm :
        ‖-((zetaZeroMultiplicity (rho : ℂ) : ℂ))‖ =
          ‖(zetaZeroMultiplicity (rho : ℂ) : ℂ)‖ :=
      norm_neg ((zetaZeroMultiplicity (rho : ℂ) : ℂ))
    have hnaturalPower :
        zetaCompletedZeroCenteredHeight rho ^ degree =
          zetaCompletedZeroCenteredHeight rho ^ (degree : ℤ) :=
      (zpow_natCast (zetaCompletedZeroCenteredHeight rho) degree).symm
    calc
      ‖-((zetaZeroMultiplicity (rho : ℂ) : ℂ))‖ =
          ‖(zetaZeroMultiplicity (rho : ℂ) : ℂ)‖ := hnegativeNorm
      _ ≤ bound *
          zetaCompletedZeroCenteredHeight rho ^ (degree : ℤ) :=
        hestimate rho
      _ = bound * zetaCompletedZeroCenteredHeight rho ^ degree :=
        congrArg (fun value : ℝ => bound * value) hnaturalPower.symm
  
  exact ⟨bound, degree, le_of_lt hboundPositive, hpolynomialBound⟩

/-- The atomic coefficient produced by a bounded dual coefficient and a finite
spectral-zero multiplier has polynomial centered-height growth. -/
theorem polynomialWeightedCompletedZeroAtomicCoefficient_growth
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ)
    (b : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal)) :
    CompletedZeroAtomicPolynomialGrowth
      (fun rho : ZetaCompletedZeroCoordinate =>
        b rho *
          ((P.toList.map (fun sample : ℂ => sample - (rho : ℂ))).prod *
            Neg.neg (zetaZeroMultiplicity (rho : ℂ) : ℂ))) := by
  have hmultiplierGrowth :
      CompletedZeroAtomicPolynomialGrowth
        (fun rho : ZetaCompletedZeroCoordinate =>
          (P.toList.map (fun sample : ℂ => sample - (rho : ℂ))).prod) :=
    finiteSpectralZeroMultiplier_polynomialGrowth P
  have hmultiplicityGrowth :
      CompletedZeroAtomicPolynomialGrowth
        (fun rho : ZetaCompletedZeroCoordinate =>
          -((zetaZeroMultiplicity (rho : ℂ) : ℂ))) :=
    completedZeroMultiplicity_polynomialGrowth
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  have hproductGrowth :
      CompletedZeroAtomicPolynomialGrowth
        (fun rho : ZetaCompletedZeroCoordinate =>
          (P.toList.map (fun sample : ℂ => sample - (rho : ℂ))).prod *
            -((zetaZeroMultiplicity (rho : ℂ) : ℂ))) :=
    CompletedZeroAtomicPolynomialGrowth.mul
      (fun rho : ZetaCompletedZeroCoordinate =>
        (P.toList.map (fun sample : ℂ => sample - (rho : ℂ))).prod)
      (fun rho : ZetaCompletedZeroCoordinate =>
        -((zetaZeroMultiplicity (rho : ℂ) : ℂ)))
      hmultiplierGrowth
      hmultiplicityGrowth
  exact CompletedZeroAtomicPolynomialGrowth.mul_bounded_left
    (fun rho : ZetaCompletedZeroCoordinate =>
      (P.toList.map (fun sample : ℂ => sample - (rho : ℂ))).prod *
        -((zetaZeroMultiplicity (rho : ℂ) : ℂ)))
    (fun rho : ZetaCompletedZeroCoordinate => b rho)
    hproductGrowth
    ‖b‖
    (norm_nonneg b)
    (fun rho => lp.norm_apply_le_norm ENNReal.top_ne_zero b rho)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
