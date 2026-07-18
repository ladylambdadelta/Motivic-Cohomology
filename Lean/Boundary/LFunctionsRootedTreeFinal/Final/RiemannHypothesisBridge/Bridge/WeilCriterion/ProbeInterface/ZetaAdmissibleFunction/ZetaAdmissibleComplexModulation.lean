import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleFunctionCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCalculusBase.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Core

/-!
# Complex exponential modulation of admissible probes

This owner closes admissible probes under multiplication by `exp (-a t)` for an arbitrary
complex spectral center `a`.  It is the physical-space operation whose Laplace transform
is translated by `-a`.
-/

namespace Boundary
namespace LFunctions
noncomputable section

open scoped ContDiff
open MeasureTheory

namespace ZetaAdmissibleFunction

/-- Complex exponential modulation by the spectral center `a`. -/
def complexExponentialModulate
    (a : ℂ)
    (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction where
  toZetaTestFunction :=
    CompactlySupportedContinuousMap.mk
      ⟨fun t : ℝ => f.toZetaTestFunction' t * Complex.exp (-(a * (t : ℂ))),
        f.toZetaTestFunction.continuous.mul
          (Complex.continuous_exp.comp
            (continuous_neg.comp
              (continuous_const.mul Complex.continuous_ofReal)))⟩
      (f.toZetaTestFunction.hasCompactSupport.mul_right)
  smooth := by
    have hargument :
        ContDiff ℝ ∞ (fun t : ℝ => -(a * (t : ℂ))) := by
      exact (contDiff_const.mul Complex.ofRealCLM.contDiff).neg
    have hexponential :
        ContDiff ℝ ∞ (fun t : ℝ => Complex.exp (-(a * (t : ℂ)))) := by
      exact Complex.contDiff_exp.comp hargument
    exact f.smooth.mul hexponential

/-- Pointwise form of complex exponential modulation. -/
theorem complexExponentialModulate_apply
    (a : ℂ)
    (f : ZetaAdmissibleFunction)
    (t : ℝ) :
    complexExponentialModulate a f t =
      f.toZetaTestFunction' t * Complex.exp (-(a * (t : ℂ))) := by
  exact rfl

/-- Complex modulation preserves the pointwise support because its exponential factor never
vanishes. -/
theorem support_complexExponentialModulate
    (a : ℂ)
    (f : ZetaAdmissibleFunction) :
    Function.support (complexExponentialModulate a f) = Function.support f := by
  apply Set.ext
  intro t
  change
    (f.toZetaTestFunction' t * Complex.exp (-(a * (t : ℂ)) ) ≠ 0) ↔
      f.toZetaTestFunction' t ≠ 0
  constructor
  · intro hproduct hzero
    apply hproduct
    calc
      f.toZetaTestFunction' t * Complex.exp (-(a * (t : ℂ))) =
          0 * Complex.exp (-(a * (t : ℂ))) := by
        exact congrArg (fun u : ℂ => u * Complex.exp (-(a * (t : ℂ)))) hzero
      _ = 0 := by
        exact zero_mul (Complex.exp (-(a * (t : ℂ))))
  · intro hzero
    have hexp : Complex.exp (-(a * (t : ℂ))) ≠ 0 :=
      Complex.exp_ne_zero (-(a * (t : ℂ)))
    exact mul_ne_zero hzero hexp

/-- Complex modulation preserves the closed support used to select a fixed Paley-Wiener
Hilbert fiber. -/
theorem tsupport_complexExponentialModulate
    (a : ℂ)
    (f : ZetaAdmissibleFunction) :
    tsupport (complexExponentialModulate a f) = tsupport f := by
  unfold tsupport
  exact congrArg closure (support_complexExponentialModulate a f)

/-- Complex modulation translates the Laplace transform by the negative spectral center. -/
theorem zetaLaplaceTransform_complexExponentialModulate
    (a z : ℂ)
    (f : ZetaAdmissibleFunction) :
    zetaLaplaceTransform
        (complexExponentialModulate a f).toZetaTestFunction' z =
      zetaLaplaceTransform f.toZetaTestFunction' (z - a) := by
  unfold zetaLaplaceTransform
  exact integral_congr_ae
    (Filter.Eventually.of_forall (fun t : ℝ => by
      have hcombine :
          Complex.exp (-(a * (t : ℂ))) * Complex.exp (z * (t : ℂ)) =
            Complex.exp ((z - a) * (t : ℂ)) := by
        have hargument :
            -(a * (t : ℂ)) + z * (t : ℂ) = (z - a) * (t : ℂ) := by
          calc
            -(a * (t : ℂ)) + z * (t : ℂ) =
                z * (t : ℂ) + -(a * (t : ℂ)) := by
                  exact add_comm (-(a * (t : ℂ))) (z * (t : ℂ))
            _ = z * (t : ℂ) - a * (t : ℂ) := by
                  exact (sub_eq_add_neg (z * (t : ℂ)) (a * (t : ℂ))).symm
            _ = (z - a) * (t : ℂ) := by
                  exact (sub_mul z a (t : ℂ)).symm
        exact Eq.trans
          (Complex.exp_add (-(a * (t : ℂ))) (z * (t : ℂ))).symm
          (congrArg Complex.exp hargument)
      calc
        (complexExponentialModulate a f).toZetaTestFunction' t *
            Complex.exp (z * (t : ℂ)) =
            (f.toZetaTestFunction' t * Complex.exp (-(a * (t : ℂ)))) *
              Complex.exp (z * (t : ℂ)) := by
              exact congrArg
                (fun value : ℂ => value * Complex.exp (z * (t : ℂ)))
                (complexExponentialModulate_apply a f t)
        _ = f.toZetaTestFunction' t *
              (Complex.exp (-(a * (t : ℂ))) * Complex.exp (z * (t : ℂ))) := by
              exact mul_assoc
                (f.toZetaTestFunction' t)
                (Complex.exp (-(a * (t : ℂ))))
                (Complex.exp (z * (t : ℂ)))
        _ = f.toZetaTestFunction' t * Complex.exp ((z - a) * (t : ℂ)) := by
              exact congrArg (fun value : ℂ => f.toZetaTestFunction' t * value) hcombine))

/-- Complex modulation translates the admissible spectral evaluation by the negative
spectral center. -/
theorem zetaSpectralEval_complexExponentialModulate
    (a z : ℂ)
    (f : ZetaAdmissibleFunction) :
    zetaSpectralEval (complexExponentialModulate a f) z =
      zetaSpectralEval f (z - a) := by
  calc
    zetaSpectralEval (complexExponentialModulate a f) z =
        zetaLaplaceTransform
          (complexExponentialModulate a f).toZetaTestFunction' z := by
          exact zetaSpectralEval_eq_laplace (complexExponentialModulate a f) z
    _ = zetaLaplaceTransform f.toZetaTestFunction' (z - a) :=
          zetaLaplaceTransform_complexExponentialModulate a z f
    _ = zetaSpectralEval f (z - a) := by
          exact (zetaSpectralEval_eq_laplace f (z - a)).symm

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
