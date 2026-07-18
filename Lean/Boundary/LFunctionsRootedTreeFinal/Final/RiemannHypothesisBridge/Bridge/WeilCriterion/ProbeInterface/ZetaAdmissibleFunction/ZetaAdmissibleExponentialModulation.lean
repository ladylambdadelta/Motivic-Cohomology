import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCalculusBase.Owner

namespace Boundary
namespace LFunctions
noncomputable section

open scoped ContDiff
open MeasureTheory

namespace ZetaAdmissibleFunction

theorem two_mul_half_parameter (c : ℝ) :
    2 * (c / 2) = c := by
  calc
    2 * (c / 2) = (2 * c) / 2 := by
      exact (mul_div_assoc 2 c 2).symm
    _ = c := by
      exact mul_div_cancel_left₀ c (by exact (two_ne_zero : (2 : ℝ) ≠ 0))

def exponentialModulate
    (c : ℝ) (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction where
  toZetaTestFunction :=
    CompactlySupportedContinuousMap.mk
      ⟨fun t : ℝ => f.toZetaTestFunction' t * (Real.exp (c * t) : ℂ),
        f.toZetaTestFunction.continuous.mul
          (Complex.continuous_ofReal.comp
            (Real.continuous_exp.comp (continuous_const.mul continuous_id)))⟩
      (f.toZetaTestFunction.hasCompactSupport.mul_right)
  smooth := by
    have hsource :
        ContDiff ℝ ∞ (fun t : ℝ => f.toZetaTestFunction' t) :=
      f.smooth
    have hlinear :
        ContDiff ℝ ∞ (fun t : ℝ => c * t) :=
      contDiff_const.mul contDiff_id
    have hexpReal :
        ContDiff ℝ ∞ (fun t : ℝ => Real.exp (c * t)) :=
      Real.contDiff_exp.comp hlinear
    have hexpComplex :
        ContDiff ℝ ∞ (fun t : ℝ => (Real.exp (c * t) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hexpReal
    exact hsource.mul hexpComplex

theorem exponentialModulate_apply
    (c : ℝ) (f : ZetaAdmissibleFunction) (t : ℝ) :
    exponentialModulate c f t =
      f.toZetaTestFunction' t * (Real.exp (c * t) : ℂ) := by
  rfl

theorem zetaLaplaceTransform_exponentialModulate
    (c : ℝ) (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaLaplaceTransform
        (exponentialModulate c f).toZetaTestFunction' z =
      zetaLaplaceTransform f.toZetaTestFunction'
        (z + (c : ℂ)) := by
  unfold zetaLaplaceTransform
  exact integral_congr_ae
    (Filter.Eventually.of_forall (fun t : ℝ => by
      have hreal :
          (Real.exp (c * t) : ℂ) =
            Complex.exp ((c : ℂ) * (t : ℂ)) := by
        exact Eq.trans
          (Complex.ofReal_exp (c * t))
          (congrArg Complex.exp (Complex.ofReal_mul c t))
      have hmul :
          ((c : ℂ) * (t : ℂ)) = ((c * t : ℝ) : ℂ) := by
        exact (Complex.ofReal_mul c t).symm
      have hexp :
          Complex.exp ((c : ℂ) * (t : ℂ)) *
              Complex.exp (z * (t : ℂ)) =
            Complex.exp ((z + (c : ℂ)) * (t : ℂ)) := by
        exact Eq.trans
          (Complex.exp_add ((c : ℂ) * (t : ℂ)) (z * (t : ℂ))).symm
          (congrArg Complex.exp
            (by
              calc
                (c : ℂ) * (t : ℂ) + z * (t : ℂ) =
                    z * (t : ℂ) + (c : ℂ) * (t : ℂ) := by
                      exact add_comm _ _
                _ = (z + (c : ℂ)) * (t : ℂ) := by
                  exact (add_mul z (c : ℂ) (t : ℂ)).symm))
      calc
        (exponentialModulate c f).toZetaTestFunction' t *
            Complex.exp (z * (t : ℂ)) =
          (f.toZetaTestFunction' t * (Real.exp (c * t) : ℂ)) *
            Complex.exp (z * (t : ℂ)) := by
              exact congrArg
                (fun value : ℂ => value * Complex.exp (z * (t : ℂ)))
                (exponentialModulate_apply c f t)
        _ = f.toZetaTestFunction' t *
              (Complex.exp ((c : ℂ) * (t : ℂ)) *
                Complex.exp (z * (t : ℂ))) := by
              have hprod :=
                congrArg
                  (fun value : ℂ =>
                    (f.toZetaTestFunction' t * value) *
                      Complex.exp (z * (t : ℂ)))
                  hreal
              exact Eq.trans hprod
                (mul_assoc (f.toZetaTestFunction' t)
                  (Complex.exp ((c : ℂ) * (t : ℂ)))
                  (Complex.exp (z * (t : ℂ))))
        _ = f.toZetaTestFunction' t *
              Complex.exp ((z + (c : ℂ)) * (t : ℂ)) := by
              exact congrArg (fun value : ℂ => f.toZetaTestFunction' t * value) hexp))

theorem zetaSpectralEval_exponentialModulate
    (c : ℝ) (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralEval (exponentialModulate c f) z =
      zetaSpectralEval f (z + (c : ℂ)) := by
  calc
    zetaSpectralEval (exponentialModulate c f) z =
        zetaLaplaceTransform
          (exponentialModulate c f).toZetaTestFunction' z := by
      exact zetaSpectralEval_eq_laplace
        (exponentialModulate c f) z
    _ = zetaLaplaceTransform f.toZetaTestFunction' (z + (c : ℂ)) :=
      zetaLaplaceTransform_exponentialModulate c f z
    _ = zetaSpectralEval f (z + (c : ℂ)) := by
      exact (zetaSpectralEval_eq_laplace f (z + (c : ℂ))).symm

theorem autocorrelation_exponentialModulate_apply
    (c : ℝ) (f : ZetaAdmissibleFunction) (t : ℝ) :
    autocorrelation (exponentialModulate c f) t =
      (Real.exp (2 * c * t) : ℂ) * autocorrelation f t := by
  have hstar_exp :
      star (Real.exp (c * t) : ℂ) = (Real.exp (c * t) : ℂ) := by
    exact Complex.conj_ofReal (Real.exp (c * t))
  have harg : c * t + c * t = 2 * c * t := by
    calc
      c * t + c * t = 2 * (c * t) := by
        exact (two_mul (c * t)).symm
      _ = 2 * c * t := by
        exact (mul_assoc 2 c t).symm
  have hdouble :
      (Real.exp (c * t) : ℂ) * (Real.exp (c * t) : ℂ) =
        (Real.exp (2 * c * t) : ℂ) := by
    calc
      (Real.exp (c * t) : ℂ) * (Real.exp (c * t) : ℂ) =
          ((Real.exp (c * t) * Real.exp (c * t) : ℝ) : ℂ) := by
        exact (Complex.ofReal_mul (Real.exp (c * t))
          (Real.exp (c * t))).symm
      _ = ((Real.exp (c * t + c * t) : ℝ) : ℂ) := by
        exact congrArg (fun value : ℝ => (value : ℂ))
          (Real.exp_add (c * t) (c * t)).symm
      _ = (Real.exp (2 * c * t) : ℂ) := by
        exact congrArg (fun value : ℝ => (Real.exp value : ℂ)) harg
  have hforward :
      (Real.exp (c * t) : ℂ) * (Real.exp (c * t) : ℂ) *
          (f.toZetaTestFunction' t * star (f.toZetaTestFunction' t)) =
        (Real.exp (2 * c * t) : ℂ) * autocorrelation f t := by
    have hpoint :
        f.toZetaTestFunction' t * star (f.toZetaTestFunction' t) =
          autocorrelation f t := by
      exact (autocorrelation_apply f t).symm
    exact Eq.trans
      (congrArg
        (fun value : ℂ => value *
          (f.toZetaTestFunction' t * star (f.toZetaTestFunction' t)))
        hdouble)
      (congrArg
        (fun value : ℂ => (Real.exp (2 * c * t) : ℂ) * value)
        hpoint)
  calc
    autocorrelation (exponentialModulate c f) t =
        exponentialModulate c f t * star (exponentialModulate c f t) :=
      autocorrelation_apply (exponentialModulate c f) t
    _ = (f.toZetaTestFunction' t * (Real.exp (c * t) : ℂ)) *
          star (f.toZetaTestFunction' t * (Real.exp (c * t) : ℂ)) := by
      exact congrArg₂ (fun x y : ℂ => x * star y)
        (exponentialModulate_apply c f t)
        (exponentialModulate_apply c f t)
    _ = (Real.exp (c * t) : ℂ) * (Real.exp (c * t) : ℂ) *
          (f.toZetaTestFunction' t * star (f.toZetaTestFunction' t)) := by
      have hstar_product :
          star (f.toZetaTestFunction' t * (Real.exp (c * t) : ℂ)) =
            (Real.exp (c * t) : ℂ) *
              star (f.toZetaTestFunction' t) := by
        calc
          star (f.toZetaTestFunction' t * (Real.exp (c * t) : ℂ)) =
              star (Real.exp (c * t) : ℂ) *
                star (f.toZetaTestFunction' t) := by
            exact star_mul (f.toZetaTestFunction' t)
              (Real.exp (c * t) : ℂ)
          _ = (Real.exp (c * t) : ℂ) *
                star (f.toZetaTestFunction' t) := by
            exact congrArg
              (fun value : ℂ => value * star (f.toZetaTestFunction' t))
              hstar_exp
      calc
        (f.toZetaTestFunction' t * (Real.exp (c * t) : ℂ)) *
            star (f.toZetaTestFunction' t * (Real.exp (c * t) : ℂ)) =
            (f.toZetaTestFunction' t * (Real.exp (c * t) : ℂ)) *
              ((Real.exp (c * t) : ℂ) *
                star (f.toZetaTestFunction' t)) := by
          exact congrArg
            (fun value : ℂ =>
              (f.toZetaTestFunction' t * (Real.exp (c * t) : ℂ)) * value)
            hstar_product
        _ = (Real.exp (c * t) : ℂ) * (Real.exp (c * t) : ℂ) *
              (f.toZetaTestFunction' t * star (f.toZetaTestFunction' t)) := by
          calc
            (f.toZetaTestFunction' t * (Real.exp (c * t) : ℂ)) *
                ((Real.exp (c * t) : ℂ) *
                  star (f.toZetaTestFunction' t)) =
                ((f.toZetaTestFunction' t * (Real.exp (c * t) : ℂ)) *
                  (Real.exp (c * t) : ℂ)) *
                    star (f.toZetaTestFunction' t) := by
              exact (mul_assoc
                (f.toZetaTestFunction' t * (Real.exp (c * t) : ℂ))
                (Real.exp (c * t) : ℂ)
                (star (f.toZetaTestFunction' t))).symm
            _ = (f.toZetaTestFunction' t *
                  ((Real.exp (c * t) : ℂ) * (Real.exp (c * t) : ℂ))) *
                    star (f.toZetaTestFunction' t) := by
              exact congrArg
                (fun value : ℂ => value * star (f.toZetaTestFunction' t))
                (mul_assoc (f.toZetaTestFunction' t)
                  (Real.exp (c * t) : ℂ) (Real.exp (c * t) : ℂ))
            _ = (((Real.exp (c * t) : ℂ) * (Real.exp (c * t) : ℂ)) *
                  f.toZetaTestFunction' t) *
                    star (f.toZetaTestFunction' t) := by
              exact congrArg
                (fun value : ℂ => value * star (f.toZetaTestFunction' t))
                (mul_comm (f.toZetaTestFunction' t)
                  ((Real.exp (c * t) : ℂ) * (Real.exp (c * t) : ℂ)))
            _ = ((Real.exp (c * t) : ℂ) * (Real.exp (c * t) : ℂ)) *
                  (f.toZetaTestFunction' t *
                    star (f.toZetaTestFunction' t)) := by
              exact mul_assoc
                ((Real.exp (c * t) : ℂ) * (Real.exp (c * t) : ℂ))
                (f.toZetaTestFunction' t)
                (star (f.toZetaTestFunction' t))
    _ = (Real.exp (2 * c * t) : ℂ) * autocorrelation f t := hforward

theorem autocorrelation_exponentialModulate_eq_exponentialModulate_autocorrelation
    (c : ℝ) (f : ZetaAdmissibleFunction) :
    autocorrelation (exponentialModulate c f) =
      exponentialModulate (2 * c) (autocorrelation f) := by
  ext t
  calc
    autocorrelation (exponentialModulate c f) t =
        (Real.exp (2 * c * t) : ℂ) * autocorrelation f t :=
      autocorrelation_exponentialModulate_apply c f t
    _ = autocorrelation f t * (Real.exp (2 * c * t) : ℂ) := by
      exact mul_comm _ _
    _ = exponentialModulate (2 * c) (autocorrelation f) t := by
      exact (exponentialModulate_apply (2 * c) (autocorrelation f) t).symm

theorem exponential_shift_argument
    (c u t : ℝ) :
    c * (u + t / 2) = c * t + c * (u - t / 2) := by
  have hhalf : t / 2 + t / 2 = t := add_halves t
  have hscaled : c * (t / 2) + c * (t / 2) = c * t := by
    exact Eq.trans
      (mul_add c (t / 2) (t / 2)).symm
      (congrArg (fun value : ℝ => c * value) hhalf)
  calc
    c * (u + t / 2) = c * u + c * (t / 2) := by
      exact mul_add c u (t / 2)
    _ = (c * (t / 2) + c * (t / 2)) +
          (c * u - c * (t / 2)) := by
      have hcancel :
          c * (t / 2) + (c * u - c * (t / 2)) = c * u := by
        exact Eq.trans
          (add_comm (c * (t / 2)) (c * u - c * (t / 2)))
          (sub_add_cancel (c * u) (c * (t / 2)))
      exact Eq.trans
        (add_comm (c * u) (c * (t / 2)))
        (Eq.trans
          (congrArg (fun value : ℝ => c * (t / 2) + value)
            hcancel.symm)
          (add_assoc (c * (t / 2)) (c * (t / 2))
            (c * u - c * (t / 2))).symm)
    _ = c * t + c * (u - t / 2) := by
      exact congrArg₂ (fun left right : ℝ => left + right)
        hscaled (mul_sub c u (t / 2)).symm

theorem convolutionPair_oppositeExponentialModulate_apply
    (c : ℝ) (f : ZetaAdmissibleFunction) (t : ℝ) :
    convolutionPair (exponentialModulate c f)
        (exponentialModulate (-c) f) t =
      exponentialModulate c (convolutionAutocorrelation f) t := by
  have hpointwise :
      ∀ u : ℝ,
        exponentialModulate c f (u + t / 2) *
            star (exponentialModulate (-c) f (u - t / 2)) =
          (Real.exp (c * t) : ℂ) *
            (f (u + t / 2) * star (f (u - t / 2))) := by
    intro u
    have hleft := exponentialModulate_apply c f (u + t / 2)
    have hright := exponentialModulate_apply (-c) f (u - t / 2)
    have hstar :
        star (Real.exp (-c * (u - t / 2)) : ℂ) =
          (Real.exp (-c * (u - t / 2)) : ℂ) := by
      exact Complex.conj_ofReal (Real.exp (-c * (u - t / 2)))
    have harg :
        c * (u + t / 2) + (-c) * (u - t / 2) = c * t := by
      have hshift := exponential_shift_argument c u t
      have hneg :
          (-c) * (u - t / 2) = -(c * (u - t / 2)) := by
        exact neg_mul c (u - t / 2)
      calc
        c * (u + t / 2) + (-c) * (u - t / 2) =
            (c * t + c * (u - t / 2)) +
              (-(c * (u - t / 2))) := by
          exact congrArg₂ (fun left right : ℝ => left + right)
            hshift hneg
        _ = c * t +
              (c * (u - t / 2) - c * (u - t / 2)) := by
          exact Eq.trans
            (add_assoc (c * t) (c * (u - t / 2))
              (-(c * (u - t / 2))))
            (congrArg (fun value : ℝ => c * t + value)
              (sub_eq_add_neg (c * (u - t / 2))
                (c * (u - t / 2))))
        _ = c * t := by
          exact Eq.trans
            (congrArg (fun value : ℝ => c * t + value)
              (sub_self (c * (u - t / 2))))
            (add_zero (c * t))
    have hfactor :
        (Real.exp (c * (u + t / 2)) : ℂ) *
            (Real.exp (-c * (u - t / 2)) : ℂ) =
          (Real.exp (c * t) : ℂ) := by
      exact Eq.trans
        (Eq.trans
          (Complex.ofReal_mul
            (Real.exp (c * (u + t / 2)))
            (Real.exp (-c * (u - t / 2)))).symm
          (congrArg (fun value : ℝ => (value : ℂ))
            (Real.exp_add (c * (u + t / 2))
              (-c * (u - t / 2))).symm))
        (congrArg (fun value : ℝ => (Real.exp value : ℂ)) harg)
    calc
      exponentialModulate c f (u + t / 2) *
          star (exponentialModulate (-c) f (u - t / 2)) =
          (f (u + t / 2) *
            (Real.exp (c * (u + t / 2)) : ℂ)) *
            star (f (u - t / 2) *
              (Real.exp (-c * (u - t / 2)) : ℂ)) := by
        exact congrArg₂ (fun left right : ℂ => left * star right)
          hleft hright
      _ = (Real.exp (c * t) : ℂ) *
            (f (u + t / 2) * star (f (u - t / 2))) := by
        have hstarProduct :
            star (f (u - t / 2) *
                (Real.exp (-c * (u - t / 2)) : ℂ)) =
              (Real.exp (-c * (u - t / 2)) : ℂ) *
                star (f (u - t / 2)) := by
          exact Eq.trans
            (star_mul (f (u - t / 2))
              (Real.exp (-c * (u - t / 2)) : ℂ))
            (congrArg
              (fun value : ℂ => value * star (f (u - t / 2)))
              hstar)
        exact Eq.trans
          (congrArg
            (fun value : ℂ =>
              (f (u + t / 2) *
                (Real.exp (c * (u + t / 2)) : ℂ)) * value)
            hstarProduct)
          (Eq.trans
            (congrArg
              (fun value : ℂ => value *
                ((Real.exp (-c * (u - t / 2)) : ℂ) *
                  star (f (u - t / 2))))
              (mul_comm (f (u + t / 2))
                (Real.exp (c * (u + t / 2)) : ℂ)))
            (Eq.trans
              (complex_mul_pair_reassociate
                (Real.exp (c * (u + t / 2)) : ℂ)
                (f (u + t / 2))
                (Real.exp (-c * (u - t / 2)) : ℂ)
                (star (f (u - t / 2))))
              (congrArg
                (fun value : ℂ => value *
                  (f (u + t / 2) * star (f (u - t / 2))))
                hfactor)))
  calc
    convolutionPair (exponentialModulate c f)
        (exponentialModulate (-c) f) t =
        ∫ u : ℝ,
          exponentialModulate c f (u + t / 2) *
            star (exponentialModulate (-c) f (u - t / 2)) := by
      exact convolutionPair_apply
        (exponentialModulate c f) (exponentialModulate (-c) f) t
    _ = ∫ u : ℝ,
          (Real.exp (c * t) : ℂ) *
            (f (u + t / 2) * star (f (u - t / 2))) := by
      exact integral_congr_ae
        (Filter.Eventually.of_forall hpointwise)
    _ = (Real.exp (c * t) : ℂ) *
          convolutionAutocorrelation f t := by
      exact integral_mul_left
        (Real.exp (c * t) : ℂ)
        (fun u : ℝ => f (u + t / 2) * star (f (u - t / 2)))
    _ = exponentialModulate c (convolutionAutocorrelation f) t := by
      exact Eq.trans (mul_comm _ _)
        (exponentialModulate_apply c
          (convolutionAutocorrelation f) t).symm

def convolutionAutocorrelationShifted
    (c : ℝ) (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction :=
  convolutionPair (exponentialModulate c f)
    (exponentialModulate (-c) f)

theorem convolutionAutocorrelationShifted_eq_exponentialModulate
    (c : ℝ) (f : ZetaAdmissibleFunction) :
    convolutionAutocorrelationShifted c f =
      exponentialModulate c (convolutionAutocorrelation f) := by
  ext t
  exact convolutionPair_oppositeExponentialModulate_apply c f t

theorem exponentialModulate_comp
    (c d : ℝ) (f : ZetaAdmissibleFunction) :
    exponentialModulate c (exponentialModulate d f) =
      exponentialModulate (c + d) f := by
  ext t
  have hleft := exponentialModulate_apply c (exponentialModulate d f) t
  have hinner := exponentialModulate_apply d f t
  have hexp :
      Real.exp (d * t) * Real.exp (c * t) =
        Real.exp ((c + d) * t) := by
    exact Eq.trans
      (Real.exp_add (d * t) (c * t)).symm
      (congrArg Real.exp
        (Eq.trans
          (add_comm (d * t) (c * t))
          (add_mul c d t).symm))
  calc
    exponentialModulate c (exponentialModulate d f) t =
        exponentialModulate d f t * (Real.exp (c * t) : ℂ) := hleft
    _ = (f.toZetaTestFunction' t * (Real.exp (d * t) : ℂ)) *
          (Real.exp (c * t) : ℂ) := by
      exact congrArg
        (fun value : ℂ => value * (Real.exp (c * t) : ℂ)) hinner
    _ = f.toZetaTestFunction' t *
          ((Real.exp (d * t) : ℂ) * (Real.exp (c * t) : ℂ)) := by
      exact mul_assoc (f.toZetaTestFunction' t)
        (Real.exp (d * t) : ℂ) (Real.exp (c * t) : ℂ)
    _ = f.toZetaTestFunction' t *
          (Real.exp ((c + d) * t) : ℂ) := by
      exact congrArg
        (fun value : ℂ => f.toZetaTestFunction' t * value)
        (Eq.trans
          (Complex.ofReal_mul (Real.exp (d * t))
            (Real.exp (c * t))).symm
          (congrArg (fun value : ℝ => (value : ℂ)) hexp))
    _ = exponentialModulate (c + d) f t :=
      (exponentialModulate_apply (c + d) f t).symm

theorem exponentialModulate_zero
    (f : ZetaAdmissibleFunction) :
    exponentialModulate 0 f = f := by
  ext t
  have hexp : Real.exp (0 * t) = 1 := by
    exact Eq.trans
      (congrArg Real.exp (zero_mul t))
      Real.exp_zero
  calc
    exponentialModulate 0 f t =
        f.toZetaTestFunction' t * (Real.exp (0 * t) : ℂ) :=
      exponentialModulate_apply 0 f t
    _ = f.toZetaTestFunction' t * (1 : ℂ) := by
      exact congrArg
        (fun value : ℝ => f.toZetaTestFunction' t * (value : ℂ)) hexp
    _ = f t := by
      exact (mul_one (f t)).trans rfl

theorem zetaSpectralEval_positiveModulation_at_centeredZero
    (f : ZetaAdmissibleFunction) (ρ : ℂ) :
    zetaSpectralEval
        (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
        (zetaCenteredZero ρ) =
      zetaSpectralEval (convolutionAutocorrelation f) ρ := by
  have hshift :
      zetaCenteredZero ρ + ((1 / 2 : ℝ) : ℂ) = ρ := by
    have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
      exact Complex.ofReal_div 1 2
    unfold zetaCenteredZero
    exact Eq.trans
      (congrArg (fun value : ℂ => (ρ - (1 / 2 : ℂ)) + value)
        hhalf)
      (sub_add_cancel ρ (1 / 2 : ℂ))
  have heval :=
    zetaSpectralEval_exponentialModulate
      (1 / 2 : ℝ) (convolutionAutocorrelation f)
      (zetaCenteredZero ρ)
  have hprobe :=
    convolutionAutocorrelationShifted_eq_exponentialModulate
      (1 / 2 : ℝ) f
  exact Eq.trans
    (congrArg
      (fun g : ZetaAdmissibleFunction =>
        zetaSpectralEval g (zetaCenteredZero ρ)) hprobe)
    (Eq.trans heval
      (congrArg
        (fun z : ℂ => zetaSpectralEval (convolutionAutocorrelation f) z)
        hshift))

theorem zetaSpectralEval_inverseModulation_at_zero
    (f : ZetaAdmissibleFunction) (ρ : ℂ) :
    zetaSpectralEval
        (exponentialModulate (-(1 / 2 : ℝ)) f) ρ =
      zetaSpectralEval f (zetaCenteredZero ρ) := by
  have hshiftCore : ρ + (-(1 / 2 : ℂ)) = zetaCenteredZero ρ := by
    unfold zetaCenteredZero
    exact (sub_eq_add_neg ρ (1 / 2 : ℂ)).symm
  have hshift : ρ + ((-(1 / 2 : ℝ)) : ℂ) = zetaCenteredZero ρ := by
    have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
      exact Complex.ofReal_div 1 2
    have hneg : ((-(1 / 2 : ℝ)) : ℂ) = -(1 / 2 : ℂ) := by
      calc
        ((-(1 / 2 : ℝ)) : ℂ) = -((1 / 2 : ℝ) : ℂ) := by
          rfl
        _ = -(1 / 2 : ℂ) := congrArg Neg.neg hhalf
    exact Eq.trans
      (congrArg (fun value : ℂ => ρ + value) hneg)
      hshiftCore
  have heval := zetaSpectralEval_exponentialModulate
    (-(1 / 2 : ℝ)) f ρ
  have harg :
      ρ + Complex.ofReal (-(1 / 2 : ℝ)) =
        ρ + (-(1 / 2 : ℂ)) := by
    have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
      exact Complex.ofReal_div 1 2
    have hnegCast := Complex.ofReal_neg (1 / 2 : ℝ)
    exact Eq.trans
      (congrArg (fun value : ℂ => ρ + value) hnegCast)
      (congrArg (fun value : ℂ => ρ + value)
        (congrArg Neg.neg hhalf))
  exact Eq.trans heval
      (Eq.trans
        (congrArg (fun z : ℂ => zetaSpectralEval f z) harg)
        (congrArg (fun z : ℂ => zetaSpectralEval f z) hshiftCore))

theorem positiveModulation_window_of_raw_window
    (f : ZetaAdmissibleFunction) (T : Finset ℂ)
    (hwindow : ∀ ρ : ℂ, ρ ∈ T →
      zetaSpectralEval (convolutionAutocorrelation f) ρ = 0) :
    ∀ ρ : ℂ, ρ ∈ T →
      zetaSpectralEval
        (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
        (zetaCenteredZero ρ) = 0 := by
  intro ρ hρ
  exact Eq.trans
    (zetaSpectralEval_positiveModulation_at_centeredZero f ρ)
    (hwindow ρ hρ)

theorem positiveModulation_inverse_cancel
    (f : ZetaAdmissibleFunction) :
    exponentialModulate (1 / 2 : ℝ)
        (exponentialModulate (-(1 / 2 : ℝ)) f) = f := by
  have hcomp := exponentialModulate_comp
    (1 / 2 : ℝ) (-(1 / 2 : ℝ)) f
  have hcancel : (1 / 2 : ℝ) + (-(1 / 2 : ℝ)) = 0 := by
    exact add_neg_cancel (1 / 2 : ℝ)
  have hzero := exponentialModulate_zero f
  calc
    exponentialModulate (1 / 2 : ℝ)
        (exponentialModulate (-(1 / 2 : ℝ)) f) =
        exponentialModulate
          ((1 / 2 : ℝ) + (-(1 / 2 : ℝ))) f := hcomp
    _ = exponentialModulate 0 f := by
      exact congrArg (fun c : ℝ => exponentialModulate c f) hcancel
    _ = f := hzero

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
