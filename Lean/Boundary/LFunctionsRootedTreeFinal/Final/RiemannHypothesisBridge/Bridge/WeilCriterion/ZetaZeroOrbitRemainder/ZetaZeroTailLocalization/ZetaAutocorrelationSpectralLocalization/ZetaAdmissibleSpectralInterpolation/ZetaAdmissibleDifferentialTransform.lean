import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleDifferential
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCalculusBase.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralLinearity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Laplace multipliers of admissible differential operators

Physical differentiation acts on the bilateral Laplace transform by
multiplication with the negative spectral parameter.  Consequently `D + a`
forces a spectral zero at `a`.
-/

namespace Boundary
namespace LFunctions
noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

theorem hasDerivAt_laplaceExponential_real
    (z : ℂ)
    (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => Complex.exp (z * (u : ℂ)))
      (z * Complex.exp (z * (t : ℂ)))
      t := by
  have hlinearComplex :
      HasDerivAt (fun w : ℂ => z * w) z (t : ℂ) := by
    have hid : HasDerivAt (fun w : ℂ => w) 1 (t : ℂ) :=
      hasDerivAt_id (t : ℂ)
    exact Eq.subst
      (motive := fun value : ℂ => HasDerivAt (fun w : ℂ => z * w) value (t : ℂ))
      (mul_one z)
      (hid.const_mul z)
  have hlinearReal :
      HasDerivAt (fun u : ℝ => z * (u : ℂ)) z t :=
    hlinearComplex.comp_ofReal
  have hexponential :
      HasDerivAt
        (fun u : ℝ => Complex.exp (z * (u : ℂ)))
        (Complex.exp (z * (t : ℂ)) * z)
        t :=
    (Complex.hasDerivAt_exp (z * (t : ℂ))).comp t hlinearReal
  exact Eq.subst
    (motive := fun value : ℂ =>
      HasDerivAt (fun u : ℝ => Complex.exp (z * (u : ℂ))) value t)
    (mul_comm (Complex.exp (z * (t : ℂ))) z)
    hexponential

theorem physicalDerivative_laplaceKernel_integrable
    (f : ZetaAdmissibleFunction)
    (z : ℂ) :
    Integrable
      (fun t : ℝ => physicalDerivative f t * Complex.exp (z * (t : ℂ))) := by
  have hcontinuous :
      Continuous
        (fun t : ℝ => physicalDerivative f t * Complex.exp (z * (t : ℂ))) :=
    (physicalDerivative f).toZetaTestFunction.continuous.mul
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal))
  have hcompact :
      HasCompactSupport
        (fun t : ℝ => physicalDerivative f t * Complex.exp (z * (t : ℂ))) :=
    (physicalDerivative f).toZetaTestFunction.hasCompactSupport.mul_right
  exact hcontinuous.integrable_of_hasCompactSupport hcompact

theorem laplaceDerivativePartner_integrable
    (f : ZetaAdmissibleFunction)
    (z : ℂ) :
    Integrable
      (fun t : ℝ => f t * (z * Complex.exp (z * (t : ℂ)))) := by
  have hcontinuous :
      Continuous
        (fun t : ℝ => f t * (z * Complex.exp (z * (t : ℂ)))) :=
    f.toZetaTestFunction.continuous.mul
      (continuous_const.mul
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)))
  have hcompact :
      HasCompactSupport
        (fun t : ℝ => f t * (z * Complex.exp (z * (t : ℂ)))) :=
    f.toZetaTestFunction.hasCompactSupport.mul_right
  exact hcontinuous.integrable_of_hasCompactSupport hcompact

theorem zetaLaplaceTransform_physicalDerivative
    (f : ZetaAdmissibleFunction)
    (z : ℂ) :
    Boundary.zetaLaplaceTransform (physicalDerivative f).toZetaTestFunction' z =
      -z * Boundary.zetaLaplaceTransform f.toZetaTestFunction' z := by
  have hintegrationByParts :
      (∫ t : ℝ, f t * (z * Complex.exp (z * (t : ℂ)))) =
        - ∫ t : ℝ, physicalDerivative f t * Complex.exp (z * (t : ℂ)) := by
    exact integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun t : ℝ => hasDerivAt_physicalDerivative_source f t)
      (fun t : ℝ => hasDerivAt_laplaceExponential_real z t)
      (laplaceDerivativePartner_integrable f z)
      (physicalDerivative_laplaceKernel_integrable f z)
      (integrable_laplaceKernel_of_hasCompactSupport
        f.toZetaTestFunction' z f.toZetaTestFunction.hasCompactSupport)
  have hleftFactor :
      (∫ t : ℝ, f t * (z * Complex.exp (z * (t : ℂ)))) =
        z * Boundary.zetaLaplaceTransform f.toZetaTestFunction' z := by
    calc
      (∫ t : ℝ, f t * (z * Complex.exp (z * (t : ℂ)))) =
          ∫ t : ℝ, z * (f t * Complex.exp (z * (t : ℂ))) := by
        exact integral_congr_ae
          (Filter.Eventually.of_forall
            (fun t : ℝ =>
              calc
                f t * (z * Complex.exp (z * (t : ℂ))) =
                    (f t * z) * Complex.exp (z * (t : ℂ)) :=
                  (mul_assoc (f t) z (Complex.exp (z * (t : ℂ)))).symm
                _ = (z * f t) * Complex.exp (z * (t : ℂ)) :=
                  congrArg
                    (fun value : ℂ => value * Complex.exp (z * (t : ℂ)))
                    (mul_comm (f t) z)
                _ = z * (f t * Complex.exp (z * (t : ℂ))) :=
                  mul_assoc z (f t) (Complex.exp (z * (t : ℂ)))))
      _ = z * ∫ t : ℝ, f t * Complex.exp (z * (t : ℂ)) :=
        integral_smul z
          (fun t : ℝ => f t * Complex.exp (z * (t : ℂ)))
      _ = z * Boundary.zetaLaplaceTransform f.toZetaTestFunction' z := by
        rfl
  have hderivativeIntegral :
      (∫ t : ℝ, physicalDerivative f t * Complex.exp (z * (t : ℂ))) =
        -z * Boundary.zetaLaplaceTransform f.toZetaTestFunction' z := by
    have hnegEquality :
        -(z * Boundary.zetaLaplaceTransform f.toZetaTestFunction' z) =
          ∫ t : ℝ, physicalDerivative f t * Complex.exp (z * (t : ℂ)) :=
      neg_eq_iff_eq_neg.mpr (Eq.trans hleftFactor.symm hintegrationByParts)
    exact Eq.trans hnegEquality.symm
      (neg_mul z (Boundary.zetaLaplaceTransform f.toZetaTestFunction' z)).symm
  exact hderivativeIntegral

theorem zetaSpectralEval_firstOrderSpectralZeroOperator
    (a z : ℂ)
    (f : ZetaAdmissibleFunction) :
    zetaSpectralEval (firstOrderSpectralZeroOperator a f) z =
      (a - z) * zetaSpectralEval f z := by
  have hderivative :
      zetaSpectralEval (physicalDerivative f) z =
        -z * zetaSpectralEval f z :=
    Eq.trans
      (zetaSpectralEval_eq_laplace (physicalDerivative f) z)
      (Eq.trans
        (zetaLaplaceTransform_physicalDerivative f z)
        (congrArg (fun value : ℂ => -z * value)
          (zetaSpectralEval_eq_laplace f z).symm))
  calc
    zetaSpectralEval (firstOrderSpectralZeroOperator a f) z =
        zetaSpectralEval (physicalDerivative f + a • f) z := by
      rfl
    _ = zetaSpectralEval (physicalDerivative f) z +
          zetaSpectralEval (a • f) z :=
      zetaSpectralEval_add (physicalDerivative f) (a • f) z
    _ = (-z * zetaSpectralEval f z) + a * zetaSpectralEval f z := by
      exact congrArg₂ HAdd.hAdd hderivative (zetaSpectralEval_smul a f z)
    _ = (a - z) * zetaSpectralEval f z := by
      exact Eq.trans
        (add_comm (-z * zetaSpectralEval f z) (a * zetaSpectralEval f z))
        (Eq.trans
          (add_mul a (-z) (zetaSpectralEval f z)).symm
          (congrArg
            (fun value : ℂ => value * zetaSpectralEval f z)
            (sub_eq_add_neg a z).symm))

theorem zetaSpectralEval_firstOrderSpectralZeroOperator_at
    (a : ℂ)
    (f : ZetaAdmissibleFunction) :
    zetaSpectralEval (firstOrderSpectralZeroOperator a f) a = 0 := by
  exact Eq.trans
    (zetaSpectralEval_firstOrderSpectralZeroOperator a a f)
    (Eq.trans
      (congrArg
        (fun value : ℂ => value * zetaSpectralEval f a)
        (sub_self a))
      (zero_mul (zetaSpectralEval f a)))

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
