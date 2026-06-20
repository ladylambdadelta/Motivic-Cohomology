import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Binet.LogArctangent.Owner
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Binet formula: branch and integral representations

This file owns the branch-correct formulas and integral representations
of Binet's second formula on the positive real axis.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

/-- Multiplying the upper and lower vertical factors gives the quadratic
denominator used in the Binet derivative kernel. -/
theorem Complex.add_mul_I_mul_sub_mul_I_eq_sq_add_sq
    (z : ℂ)
    (t : ℝ) :
    (z + (t : ℂ) * Complex.I) * (z - (t : ℂ) * Complex.I) =
      z ^ 2 + (t : ℂ) ^ 2 := by
  calc
    (z + (t : ℂ) * Complex.I) * (z - (t : ℂ) * Complex.I)
        = z ^ 2 - ((t : ℂ) * Complex.I) ^ 2 :=
      Eq.symm (sq_sub_sq z ((t : ℂ) * Complex.I))
    _ = z ^ 2 - (-((t : ℂ) ^ 2)) := by
      exact congrArg (fun u : ℂ => z ^ 2 - u)
        (Complex.real_mul_I_sq t)
    _ = z ^ 2 + (t : ℂ) ^ 2 :=
      sub_neg_eq_add (z ^ 2) ((t : ℂ) ^ 2)

/-- The derivative kernel obtained by differentiating
`arctan ((t : ℂ) / w)` in Binet's second-formula remainder. -/
noncomputable def Complex.binetSecondFormulaDerivativeKernel
    (t : ℝ) (w : ℂ) : ℂ :=
  (-(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2)) /
    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- The candidate derivative of the Binet second-formula remainder after
differentiating under the integral sign. -/
noncomputable def Complex.binetSecondFormulaRemainderDerivative
    (w : ℂ) : ℂ :=
  2 * ∫ t : ℝ in Set.Ioi (0 : ℝ),
    Complex.binetSecondFormulaDerivativeKernel t w

/-- Branch-correct Binet formula on the open right half-plane.

The global Abel-Plana output is an analytic logarithm branch, not Lean's
principal `Complex.log (Complex.Gamma w)`. -/
theorem Complex.Gamma_binetSecondFormula_branchExponential :
    ∀ {w : ℂ},
      0 < w.re →
        (∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
            Complex.binetAbelPlanaFiniteMainTerm N w +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
                Complex.binetAbelPlanaFiniteContourRemainder N w) →
        Complex.exp (Complex.binetLogGammaBranch w) =
          Complex.Gamma w := by
  intro w hw hfinite
  exact
    Complex.exp_binetLogGammaBranch_eq_Gamma_from_AbelPlana w hw hfinite

/-- The Binet main term is real-valued on the positive real axis. -/
theorem Complex.binetLogGammaMainTerm_posReal_im_eq_zero
    {x : ℝ}
    (hx : 0 < x) :
    (Complex.binetLogGammaMainTerm (x : ℂ)).im = 0 := by
  have hlog :
      Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) :=
    (Complex.ofReal_log hx.le).symm
  have hreal :
      Complex.binetLogGammaMainTerm (x : ℂ) =
        (((x - (1 / 2 : ℝ)) * Real.log x - x +
          Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) := by
    calc
      Complex.binetLogGammaMainTerm (x : ℂ) =
          ((x : ℂ) - (1 / 2 : ℂ)) * Complex.log (x : ℂ) - (x : ℂ) +
            (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2 := by
        exact Complex.binetLogGammaMainTerm_unfold (x : ℂ)
      _ =
          ((x : ℂ) - (1 / 2 : ℂ)) * ((Real.log x : ℝ) : ℂ) - (x : ℂ) +
            (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2 := by
        exact
          congrArg
            (fun z : ℂ =>
              ((x : ℂ) - (1 / 2 : ℂ)) * z - (x : ℂ) +
                (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2)
            hlog
      _ =
          (((x - (1 / 2 : ℝ)) * Real.log x - x +
            Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) := by
        have hshift :
            (x : ℂ) - (1 / 2 : ℂ) = ((x - (1 / 2 : ℝ) : ℝ) : ℂ) := by
          have hhalf : (((1 / 2 : ℝ) : ℝ) : ℂ) = (1 / 2 : ℂ) := by
            exact Complex.ofReal_div 1 2
          exact
            Eq.trans
              (congrArg (fun u : ℂ => (x : ℂ) - u) hhalf.symm)
              (Eq.symm (Complex.ofReal_sub x (1 / 2 : ℝ)))
        exact
          Eq.trans
            (congrArg
              (fun u : ℂ =>
                u * ((Real.log x : ℝ) : ℂ) - (x : ℂ) +
                  (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2)
              hshift)
            (Eq.trans
              (congrArg
              (fun u : ℂ =>
                u - (x : ℂ) + (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2)
              (Eq.symm (Complex.ofReal_mul (x - (1 / 2 : ℝ)) (Real.log x))))
            (Eq.trans
              (congrArg
                (fun u : ℂ => u + (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2)
                (Eq.symm
                  (Complex.ofReal_sub
                    ((x - (1 / 2 : ℝ)) * Real.log x)
                    x)))
              (Eq.trans
                (congrArg
                  (fun u : ℂ =>
                    (((x - (1 / 2 : ℝ)) * Real.log x - x : ℝ) : ℂ) + u)
                  (Eq.symm
                    (Complex.ofReal_div (Real.log (2 * Real.pi)) 2)))
                (Eq.symm
                  (Complex.ofReal_add
                    (((x - (1 / 2 : ℝ)) * Real.log x - x))
                    (Real.log (2 * Real.pi) / 2))))))
  exact
    Complex.im_eq_zero_of_eq_ofReal
      hreal

/-- The Binet arctangent kernel is real-valued on the positive real axis. -/
theorem Complex.binetSecondFormulaKernel_posReal_im_eq_zero
    {x t : ℝ}
    (_hx : 0 < x)
    (_ht : 0 < t) :
    (Complex.arctan ((t : ℂ) / (x : ℂ)) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)).im = 0 := by
  have harg :
      (t : ℂ) / (x : ℂ) = ((t / x : ℝ) : ℂ) := by
    exact (Complex.ofReal_div t x).symm
  have harctan :
      Complex.arctan ((t : ℂ) / (x : ℂ)) =
        ((Real.arctan (t / x) : ℝ) : ℂ) := by
    calc
      Complex.arctan ((t : ℂ) / (x : ℂ)) =
          Complex.arctan ((t / x : ℝ) : ℂ) := by
        exact congrArg Complex.arctan harg
      _ = ((Real.arctan (t / x) : ℝ) : ℂ) :=
        (Complex.ofReal_arctan (t / x)).symm
  have hden :
      Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1 =
        ((Real.exp ((2 : ℝ) * Real.pi * t) - 1 : ℝ) : ℂ) := by
    exact
      by
        calc
          Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1 =
              ((Real.exp ((2 : ℝ) * Real.pi * t) : ℝ) : ℂ) - 1 := by
            exact congrArg (fun z : ℂ => z - 1) (Complex.ofReal_exp _).symm
          _ = ((Real.exp ((2 : ℝ) * Real.pi * t) - 1 : ℝ) : ℂ) := by
            exact
              Eq.symm
                (Complex.ofReal_sub (Real.exp ((2 : ℝ) * Real.pi * t)) 1)
  have hquot :
      Complex.arctan ((t : ℂ) / (x : ℂ)) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) =
        ((Real.arctan (t / x) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) : ℝ) : ℂ) := by
    calc
      Complex.arctan ((t : ℂ) / (x : ℂ)) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) =
        ((Real.arctan (t / x) : ℝ) : ℂ) /
          ((Real.exp ((2 : ℝ) * Real.pi * t) - 1 : ℝ) : ℂ) := by
        exact congrArg₂ (fun a b : ℂ => a / b) harctan hden
      _ =
        ((Real.arctan (t / x) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) : ℝ) : ℂ) := by
        exact Eq.symm (Complex.ofReal_div
          (Real.arctan (t / x))
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
  exact Complex.im_eq_zero_of_eq_ofReal hquot

/-- The Binet second-formula remainder is real-valued on the positive real
axis. -/
theorem Complex.binetSecondFormulaRemainder_posReal_im_eq_zero
    {x : ℝ}
    (hx : 0 < x) :
    (Complex.binetSecondFormulaRemainder (x : ℂ)).im = 0 := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / (x : ℂ)) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hK_integrable :
      Integrable K (volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact
      Complex.binetSecondFormula_arctanKernel_integrable_owner
        (w := (x : ℂ)) hx
  have hK_im_zero :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        (K t).im = 0 := by
    exact
      Filter.mem_of_superset
        (MeasureTheory.self_mem_ae_restrict
          (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ))))
        (fun t ht =>
          Complex.binetSecondFormulaKernel_posReal_im_eq_zero
            hx ht)
  have hintegral_im_zero :
      (∫ t : ℝ in Set.Ioi (0 : ℝ), K t).im = 0 := by
    have him_integral :
        ∫ t : ℝ in Set.Ioi (0 : ℝ), (K t).im =
          (∫ t : ℝ in Set.Ioi (0 : ℝ), K t).im := by
      exact integral_im hK_integrable
    have him_integrand_zero :
        ∫ t : ℝ in Set.Ioi (0 : ℝ), (K t).im = 0 := by
      exact integral_eq_zero_of_ae hK_im_zero
    exact Eq.trans him_integral.symm him_integrand_zero
  have hremainder_def :
      (Complex.binetSecondFormulaRemainder (x : ℂ)).im =
        (2 * ∫ t : ℝ in Set.Ioi (0 : ℝ), K t).im :=
    rfl
  have hmul_im :
      (2 * ∫ t : ℝ in Set.Ioi (0 : ℝ), K t).im =
        2 * (∫ t : ℝ in Set.Ioi (0 : ℝ), K t).im := by
    exact Complex.im_ofReal_mul 2 (∫ t : ℝ in Set.Ioi (0 : ℝ), K t)
  exact
    Eq.subst
      (motive := fun y : ℝ => y = 0)
      (Eq.symm hremainder_def)
      (calc
        (2 * ∫ t : ℝ in Set.Ioi (0 : ℝ), K t).im =
        2 * (∫ t : ℝ in Set.Ioi (0 : ℝ), K t).im := hmul_im
        _ = 2 * 0 := by
          exact congrArg (fun y : ℝ => 2 * y) hintegral_im_zero
        _ = 0 := mul_zero 2)

/-- The Binet logarithm branch is real-valued on the positive real axis. -/
theorem Complex.binetLogGammaBranch_posReal_im_eq_zero_owner
    {x : ℝ}
    (hx : 0 < x) :
    (Complex.binetLogGammaBranch (x : ℂ)).im = 0 := by
  have hmain := Complex.binetLogGammaMainTerm_posReal_im_eq_zero hx
  have hrem := Complex.binetSecondFormulaRemainder_posReal_im_eq_zero hx
  have hbranch_def :
      (Complex.binetLogGammaBranch (x : ℂ)).im =
        (Complex.binetLogGammaMainTerm (x : ℂ) +
          Complex.binetSecondFormulaRemainder (x : ℂ)).im :=
    rfl
  exact
    Eq.subst
      (motive := fun y : ℝ => y = 0)
      (Eq.symm hbranch_def)
      (calc
        (Complex.binetLogGammaMainTerm (x : ℂ) +
            Complex.binetSecondFormulaRemainder (x : ℂ)).im =
        (Complex.binetLogGammaMainTerm (x : ℂ)).im +
          (Complex.binetSecondFormulaRemainder (x : ℂ)).im := by
          exact Complex.add_im _ _
        _ = 0 + (Complex.binetSecondFormulaRemainder (x : ℂ)).im := by
          exact congrArg
            (fun y : ℝ =>
              y + (Complex.binetSecondFormulaRemainder (x : ℂ)).im)
            hmain
        _ = 0 + 0 := by
          exact congrArg (fun y : ℝ => 0 + y) hrem
        _ = 0 := zero_add 0)

/-- On the positive real axis, the analytic Binet branch agrees with Lean's
principal logarithm of Gamma. -/
theorem Complex.binetLogGammaBranch_eq_principalLog_Gamma_of_posReal_owner
    {x : ℝ}
    (hx : 0 < x)
    (hfinite :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
          Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
              Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ)) :
    Complex.binetLogGammaBranch (x : ℂ) =
      Complex.log (Complex.Gamma (x : ℂ)) := by
  have hbranch_exp :
      Complex.exp (Complex.binetLogGammaBranch (x : ℂ)) =
        Complex.Gamma (x : ℂ) :=
    Complex.Gamma_binetSecondFormula_branchExponential
      (w := (x : ℂ)) hx hfinite
  have hgamma_pos : 0 < Real.Gamma x :=
    Real.Gamma_pos_of_pos hx
  have hgamma_real :
      Complex.Gamma (x : ℂ) = (Real.Gamma x : ℂ) :=
    Complex.Gamma_ofReal x
  have hlog_gamma :
      ((Real.log (Real.Gamma x) : ℝ) : ℂ) =
        Complex.log (Complex.Gamma (x : ℂ)) := by
    exact by
      have h' : Complex.Gamma (x : ℂ) = ((Real.Gamma x : ℝ) : ℂ) := hgamma_real
      exact h'.symm ▸ Complex.ofReal_log hgamma_pos.le
  have hlog_im :
      (Complex.log (Complex.Gamma (x : ℂ))).im = 0 := by
    have hofReal_im :
        (((Real.log (Real.Gamma x) : ℝ) : ℂ)).im = 0 := rfl
    exact Eq.trans (congrArg Complex.im hlog_gamma).symm hofReal_im
  have hbranch_im :
      (Complex.binetLogGammaBranch (x : ℂ)).im = 0 :=
    Complex.binetLogGammaBranch_posReal_im_eq_zero_owner hx
  have hlog_exp :
      Complex.exp (Complex.log (Complex.Gamma (x : ℂ))) =
        Complex.Gamma (x : ℂ) :=
    Complex.exp_log
      (by
        exact hgamma_real.symm ▸ (Complex.ofReal_ne_zero.mpr (ne_of_gt hgamma_pos)))
  exact
    Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (by exact hbranch_im ▸ neg_lt_zero.mpr Real.pi_pos)
      (by exact hbranch_im ▸ Real.pi_pos.le)
      (by exact hlog_im ▸ neg_lt_zero.mpr Real.pi_pos)
      (by exact hlog_im ▸ Real.pi_pos.le)
      (Eq.trans hbranch_exp hlog_exp.symm)

/-- Positive-real principal-log normalization for Binet's second formula.

This is a real-axis branch comparison theorem.  It is separate from the global
open-half-plane Abel-Plana output, which is the branch-exponential theorem
above. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_positiveReal
    {x : ℝ}
    (hx : 0 < x)
    (hfinite :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
          Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
              Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ)) :
    Complex.log (Complex.Gamma (x : ℂ)) =
      Complex.binetLogGammaMainTerm (x : ℂ) +
        Complex.binetSecondFormulaRemainder (x : ℂ) := by
  have hbranch :
      Complex.binetLogGammaBranch (x : ℂ) =
        Complex.log (Complex.Gamma (x : ℂ)) :=
    Complex.binetLogGammaBranch_eq_principalLog_Gamma_of_posReal_owner
      hx hfinite
  exact hbranch.symm

end

end LFunctions
end Boundary
