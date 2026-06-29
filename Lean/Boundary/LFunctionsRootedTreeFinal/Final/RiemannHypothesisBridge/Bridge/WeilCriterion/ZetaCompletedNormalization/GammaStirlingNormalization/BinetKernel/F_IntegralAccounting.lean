import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.D_PointwiseMajorants
import Mathlib

import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.SetIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteFormula
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetTailContour
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.FiniteOrderAlgebra.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.RightCriticalStripCompact.Owner

/-!
# Binet kernel and sectorial Gamma seed estimates

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.GammaStirlingNormalization.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

theorem Complex.binetSecondFormula_decayingTailKernel_integrableOn_tail
    (w : ℂ) :
    IntegrableOn
      (fun t : ℝ => Complex.binetSecondFormulaDecayingTailKernel w t)
      (Set.Ioi (‖w‖ / 2)) := by
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let S : Set ℝ := Set.Ioi (‖w‖ / 2)
  have hhalf_nonneg : 0 ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) zero_le_two
  have hM_integrable :
      IntegrableOn M S :=
    Real.binetSecondFormula_kernel_majorant_integrableOn.mono_set
      (fun t ht => lt_of_le_of_lt hhalf_nonneg ht)
  have hscaled_integrable :
      IntegrableOn
        (fun t : ℝ => ((1 : ℝ) / ‖w‖) * M t)
        S :=
    hM_integrable.const_mul ((1 : ℝ) / ‖w‖)
  have hbase :
      Integrable
        (fun t : ℝ => ((((1 : ℝ) / ‖w‖) * M t : ℝ) : ℂ))
        (volume.restrict S) :=
    Complex.ofRealCLM.integrable_comp hscaled_integrable
  exact
    hbase.congr
      (Filter.Eventually.of_forall
        (fun _t => Eq.refl _))

/-- Historical wrapper name for the genuine decaying tail kernel majorant. -/
theorem Complex.binetSecondFormula_branchUniform_tail_absorption_of_decayingTailKernel_bound
    {R C : ℝ}
    (hR : 0 < R)
    (hC : 0 < C)
    (htail :
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))) :
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
  ⟨R, C, hR, hC, htail⟩

/-- Owner-level constructor reducing branch-uniform tail absorption to a
contour-majorant integral decay estimate. -/
theorem Complex.binetSecondFormula_branchUniform_tail_absorption_of_contourTailMajorantKernel_integral_decay
    {C : ℝ}
    (hC : 0 < C)
    (hdecay :
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))) :
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
  Complex.binetSecondFormula_branchUniform_tail_absorption_of_decayingTailKernel_bound
    two_pos
    hC
    (Complex.binetSecondFormula_tailRemainder_norm_le_of_contourTailMajorantKernel_integral_decay
      hdecay)

/-- The principal-tail norm is integrable on the split-tail range.

This is only the norm-integrability consequence of the existing principal-tail
integrability theorem; it is not the principal-tail decay estimate. -/
theorem Complex.binetSecondFormula_principalTailKernel_norm_integrableOn_tail
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ => ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖)
      (Set.Ioi (‖w‖ / 2)) := by
  exact
    (Complex.binetSecondFormulaPrincipalTailKernel_integrableOn_tail
      (w := w) hw_re_pos).norm

/-- The explicit scalar summand in the contour-tail majorant is integrable on
the split-tail range. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integrableOn_tail
    {w : ℂ}
    (hw_norm : 2 ≤ ‖w‖) :
    IntegrableOn
      (fun t : ℝ =>
        |((1 : ℝ) / ‖w‖) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))|)
      (Set.Ioi (‖w‖ / 2)) := by
  have hhalf_ge_one : (1 : ℝ) ≤ ‖w‖ / 2 :=
    (le_div_iff₀ two_pos).mpr
      (Eq.subst
        (motive := fun x : ℝ => x ≤ ‖w‖)
        (one_mul (2 : ℝ)).symm
        hw_norm)
  have htail_integrable :
      IntegrableOn
        (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
        (Set.Ioi (‖w‖ / 2)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty.mono_set
      (fun t ht => lt_of_le_of_lt hhalf_ge_one ht)
  have hscaled_integrable :
      IntegrableOn
        (fun t : ℝ =>
          ((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))
        (Set.Ioi (‖w‖ / 2)) :=
    htail_integrable.const_mul ((1 : ℝ) / ‖w‖)
  exact hscaled_integrable.abs

/-- Integral identity for the explicit decaying summand in the contour-tail
majorant. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_eq
    (w : ℂ)
    (hw_norm : 2 ≤ ‖w‖) :
    ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        |((1 : ℝ) / ‖w‖) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| =
      ((1 : ℝ) / ‖w‖) *
        (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  have hhalf_ge_one : (1 : ℝ) ≤ ‖w‖ / 2 :=
    (le_div_iff₀ two_pos).mpr
      (Eq.subst
        (motive := fun x : ℝ => x ≤ ‖w‖)
        (one_mul (2 : ℝ)).symm
        hw_norm)
  have hcoeff_nonneg : 0 ≤ (1 : ℝ) / ‖w‖ :=
    div_nonneg zero_le_one (norm_nonneg w)
  have hpoint :
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          |((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| =
            ((1 : ℝ) / ‖w‖) *
              (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
    fun t ht =>
      let ht_pos : 0 < t :=
        lt_of_le_of_lt
          (le_trans zero_le_one hhalf_ge_one)
          ht
      let htail_nonneg :
          0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
        le_of_lt (Real.binetSecondFormula_kernel_majorant_pos ht_pos)
      let hprod_nonneg :
          0 ≤
            ((1 : ℝ) / ‖w‖) *
              (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
        mul_nonneg hcoeff_nonneg htail_nonneg
      abs_of_nonneg hprod_nonneg
  calc
    ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        |((1 : ℝ) / ‖w‖) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| =
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          ((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
      exact setIntegral_congr_fun measurableSet_Ioi hpoint
    _ =
        ((1 : ℝ) / ‖w‖) *
          (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
      exact MeasureTheory.integral_smul
        ((1 : ℝ) / ‖w‖)
        (fun t : ℝ =>
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))

/-- Multiplying the decaying-summand integral identity by the contour symmetry
factor gives exactly the constant `2 / ‖w‖`. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_le
    (w : ℂ)
    (hw_norm : 2 ≤ ‖w‖) :
    2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        |((1 : ℝ) / ‖w‖) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| ≤
      ((2 : ℝ) / ‖w‖) *
        (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  let J : ℝ :=
    ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  have hdecay_eq :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          |((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| =
        ((1 : ℝ) / ‖w‖) * J :=
    Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_eq
      w hw_norm
  have hconst :
      2 * (((1 : ℝ) / ‖w‖) * J) = ((2 : ℝ) / ‖w‖) * J := by
    calc
      2 * (((1 : ℝ) / ‖w‖) * J) =
          (2 * ((1 : ℝ) / ‖w‖)) * J := by
        exact (mul_assoc (2 : ℝ) ((1 : ℝ) / ‖w‖) J).symm
      _ = ((2 * (1 : ℝ)) / ‖w‖) * J := by
        exact congrArg (fun x : ℝ => x * J)
          (mul_div_assoc (2 : ℝ) (1 : ℝ) ‖w‖).symm
      _ = ((2 : ℝ) / ‖w‖) * J := by
        exact congrArg (fun x : ℝ => (x / ‖w‖) * J) (mul_one (2 : ℝ))
  have htarget_eq :
      2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          |((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| =
        ((2 : ℝ) / ‖w‖) * J := by
    exact Eq.trans (congrArg (fun x : ℝ => 2 * x) hdecay_eq) hconst
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ ((2 : ℝ) / ‖w‖) * J)
    htarget_eq.symm
    (le_refl (((2 : ℝ) / ‖w‖) * J))

/-- Elementary integral normalization for the decaying summand included in the
contour-tail majorant kernel. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_le_ownerGap :
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            |((1 : ℝ) / ‖w‖) *
              (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| ≤
          ((2 : ℝ) / ‖w‖) *
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  exact fun w _hw_re_pos hw_norm =>
    Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_le
      w hw_norm

/-- Integral decay for the genuine scalar decaying tail kernel. -/
theorem Complex.binetSecondFormula_decayingTailKernel_integral_decay :
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            ‖Complex.binetSecondFormulaDecayingTailKernel w t‖ ≤
          ((2 : ℝ) / ‖w‖) *
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  intro w _hw_re_pos hw_norm
  have hpoint :
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.binetSecondFormulaDecayingTailKernel w t‖ =
            |((1 : ℝ) / ‖w‖) *
              (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| := by
    intro t _ht
    let m : ℝ :=
      ((1 : ℝ) / ‖w‖) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
    have hkernel_cast :
        Complex.binetSecondFormulaDecayingTailKernel w t = (m : ℂ) := by
      rfl
    calc
      ‖Complex.binetSecondFormulaDecayingTailKernel w t‖ =
          ‖(m : ℂ)‖ := by
        exact congrArg norm hkernel_cast
      _ = |m| := RCLike.norm_ofReal (K := ℂ) m
      _ =
          |((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| := rfl
  have hintegral_eq :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          ‖Complex.binetSecondFormulaDecayingTailKernel w t‖ =
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          |((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| := by
    exact setIntegral_congr_fun measurableSet_Ioi hpoint
  have hsummand :
      2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          |((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| ≤
        ((2 : ℝ) / ‖w‖) *
          (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
    Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_le
      w hw_norm
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        2 * x ≤
          ((2 : ℝ) / ‖w‖) *
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))
      hintegral_eq.symm
      hsummand

/-- Pointwise unfolding of the contour-tail majorant kernel norm. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_norm_eq_principal_add_decaying
    (w : ℂ)
    (t : ℝ) :
    ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
      ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ +
        |((1 : ℝ) / ‖w‖) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| := by
  let A : ℝ := ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
  let B : ℝ :=
    |((1 : ℝ) / ‖w‖) *
      (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))|
  have hAB_nonneg : 0 ≤ A + B :=
    add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hkernel :
      Complex.binetSecondFormulaContourTailMajorantKernel w t =
        ((A + B : ℝ) : ℂ) := by
    rfl
  calc
    ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
        ‖((A + B : ℝ) : ℂ)‖ := by
      exact congrArg norm hkernel
    _ = |A + B| := Complex.norm_real (A + B)
    _ = A + B := abs_of_nonneg hAB_nonneg
    _ =
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ +
          |((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| := rfl

/-- Contour-deformed Binet tail kernel integral decomposition for the full
right half-plane. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_integral_decomposition_ownerGap :
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
          (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖) +
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              |((1 : ℝ) / ‖w‖) *
                (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))|) := by
  exact fun w hw_re_pos hw_norm =>
    let A : ℝ → ℝ := fun t : ℝ =>
      ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
    let B : ℝ → ℝ := fun t : ℝ =>
      |((1 : ℝ) / ‖w‖) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))|
    let hprincipal_integrable :
        IntegrableOn A (Set.Ioi (‖w‖ / 2)) :=
      Complex.binetSecondFormula_principalTailKernel_norm_integrableOn_tail
        (w := w) hw_re_pos
    let hdecaying_integrable :
        IntegrableOn B (Set.Ioi (‖w‖ / 2)) :=
      Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integrableOn_tail
        (w := w) hw_norm
    let hpoint :
        ∀ t : ℝ,
          t ∈ Set.Ioi (‖w‖ / 2) →
            ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
              A t + B t :=
      fun t _ht =>
        Complex.binetSecondFormula_contourTailMajorantKernel_norm_eq_principal_add_decaying
          w t
    calc
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
          ∫ t : ℝ in Set.Ioi (‖w‖ / 2), A t + B t := by
        exact setIntegral_congr_fun measurableSet_Ioi hpoint
      _ =
          (∫ t : ℝ in Set.Ioi (‖w‖ / 2), A t) +
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2), B t) := by
        exact integral_add hprincipal_integrable hdecaying_integrable

/-- Set-integral decomposition for the unfolded contour-tail majorant.

This is the remaining elementary bookkeeping condition behind the accounting
lemma: after the pointwise norm unfolding, the set integral of the full
majorant is the sum of the principal-tail norm integral and the explicit
decaying-summand integral.  Its proof should be the ordinary `integral_add`
transport after the local integrability facts for the two summands are in
scope. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_integral_accounting
    {C : ℝ}
    (hprincipal :
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))
    (hdecaying :
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              |((1 : ℝ) / ‖w‖) *
                (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| ≤
            ((2 : ℝ) / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))) :
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ ≤
            ((C + 2) / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  exact fun w hw_re_pos hw_norm =>
    let J : ℝ :=
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
    let P : ℝ :=
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
    let D : ℝ :=
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        |((1 : ℝ) / ‖w‖) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))|
    have hdecomp :
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
          P + D :=
      Complex.binetSecondFormula_contourTailMajorantKernel_integral_decomposition_ownerGap
        w hw_re_pos hw_norm
    have hprincipal_w :
        2 * P ≤ (C / ‖w‖) * J :=
      hprincipal w hw_re_pos hw_norm
    have hdecaying_w :
        2 * D ≤ ((2 : ℝ) / ‖w‖) * J :=
      hdecaying w hw_re_pos hw_norm
    have hsum :
        2 * (P + D) ≤
          (C / ‖w‖) * J + ((2 : ℝ) / ‖w‖) * J := by
      have hleft :
          2 * (P + D) = 2 * P + 2 * D := by
        exact mul_add (2 : ℝ) P D
      exact
        Eq.subst
          (motive := fun x : ℝ =>
            x ≤ (C / ‖w‖) * J + ((2 : ℝ) / ‖w‖) * J)
          hleft.symm
          (add_le_add hprincipal_w hdecaying_w)
    have hconst :
        (C / ‖w‖) * J + ((2 : ℝ) / ‖w‖) * J =
          ((C + 2) / ‖w‖) * J := by
      calc
        (C / ‖w‖) * J + ((2 : ℝ) / ‖w‖) * J =
            (C / ‖w‖ + (2 : ℝ) / ‖w‖) * J := by
          exact (add_mul (C / ‖w‖) ((2 : ℝ) / ‖w‖) J).symm
        _ = (((C + 2 : ℝ) / ‖w‖)) * J := by
          exact congrArg (fun x : ℝ => x * J) (add_div C (2 : ℝ) ‖w‖).symm
        _ = ((C + 2) / ‖w‖) * J := rfl
    have hfull :
        2 *
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖) ≤
          ((C + 2) / ‖w‖) * J := by
      exact
        Eq.subst
          (motive := fun x : ℝ =>
            2 * x ≤ ((C + 2) / ‖w‖) * J)
          hdecomp.symm
          (le_trans hsum (le_of_eq hconst))
    hfull

/-- Integral accounting for the contour-tail majorant kernel.

This is the exact real-variable comparison needed after unfolding the kernel:
the raw principal-tail integral contributes the supplied constant `C`, and the
extra decaying summand contributes the additional constant `2`.

The proof is intentionally separated from the analytic principal-tail decay
because the latter is a contour deformation/cancellation theorem, not a
pointwise domination by the decaying scalar kernel. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_integral_decay_of_principalTailKernel_integral_decay
    {C : ℝ}
    (hC : 0 < C)
    (hprincipal :
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  exact
    ⟨C + 2, add_pos hC two_pos,
      Complex.binetSecondFormula_contourTailMajorantKernel_integral_accounting
        hprincipal
        Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_le_ownerGap⟩

/-- The standard scalar Binet decaying-tail integral beginning at `‖w‖ / 2`. -/
noncomputable def Complex.binetSecondFormulaDecayingTailIntegral
    (w : ℂ) : ℝ :=
  ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)

/-- Exponential lower bound for the standard Binet decaying-tail integral. -/
def Complex.BinetSecondFormulaDecayingTailIntegralExpLower : Prop :=
  ∃ c : ℝ,
    0 < c ∧
    ∀ w : ℂ,
      2 ≤ ‖w‖ →
        c * ‖w‖ * Real.exp (-Real.pi * ‖w‖) ≤
          Complex.binetSecondFormulaDecayingTailIntegral w

/-- Full tail lower bound from the unit-interval lower bound and interval-tail
monotonicity. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_expLower_of_unitInterval
    (hunit : Real.BinetSecondFormulaKernelMajorantUnitIntervalExpLower)
    (hle : Real.BinetSecondFormulaKernelMajorantUnitIntervalLeTail) :
    Real.BinetSecondFormulaKernelMajorantTailExpLower := by
  match hunit with
  | ⟨c, hc_pos, hunit_lower⟩ =>
      exact
        ⟨c, hc_pos,
          fun a ha =>
            le_trans
              (hunit_lower a ha)
              (hle a ha)⟩

/-- Owner real-variable leaf: exponential lower bound for the Binet scalar tail. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_expLower_owner :
    Real.BinetSecondFormulaKernelMajorantTailExpLower := by
  exact
    Real.binetSecondFormula_kernel_majorant_tail_expLower_of_unitInterval
      Real.binetSecondFormula_kernel_majorant_unitInterval_expLower_owner
      Real.binetSecondFormula_kernel_majorant_unitInterval_le_tail_owner

theorem Complex.binetSecondFormula_decayingTailIntegral_expLower_of_realTailLower
    (hlower : Real.BinetSecondFormulaKernelMajorantTailExpLower) :
    Complex.BinetSecondFormulaDecayingTailIntegralExpLower := by
  match hlower with
  | ⟨c, hc_pos, htail_lower⟩ =>
      exact
        ⟨c / 2, half_pos hc_pos,
          fun w hw_norm_two =>
            have hhalf_ge_one : (1 : ℝ) ≤ ‖w‖ / 2 :=
              (le_div_iff₀ two_pos).mpr
                (Eq.subst
                  (motive := fun x : ℝ => x ≤ ‖w‖)
                  (one_mul (2 : ℝ)).symm
                  hw_norm_two)
            have hexponent :
                -((2 : ℝ) * Real.pi) * (‖w‖ / 2) =
                  -Real.pi * ‖w‖ := by
              calc
                -((2 : ℝ) * Real.pi) * (‖w‖ / 2) =
                    -(((2 : ℝ) * Real.pi) * (‖w‖ / 2)) := by
                  exact neg_mul ((2 : ℝ) * Real.pi) (‖w‖ / 2)
                _ = -(Real.pi * ‖w‖) := by
                  have hinside :
                      ((2 : ℝ) * Real.pi) * (‖w‖ / 2) =
                        Real.pi * ‖w‖ := by
                    calc
                      ((2 : ℝ) * Real.pi) * (‖w‖ / 2) =
                          (((2 : ℝ) * Real.pi) * ‖w‖) / 2 := by
                        exact (mul_div_assoc ((2 : ℝ) * Real.pi) ‖w‖ 2).symm
                      _ = ((Real.pi * ‖w‖) * 2) / 2 := by
                        exact
                          congrArg (fun x : ℝ => x / 2)
                            (calc
                              ((2 : ℝ) * Real.pi) * ‖w‖ =
                                  2 * (Real.pi * ‖w‖) := by
                                exact mul_assoc 2 Real.pi ‖w‖
                              _ = (Real.pi * ‖w‖) * 2 := by
                                exact mul_comm 2 (Real.pi * ‖w‖))
                      _ = Real.pi * ‖w‖ := by
                        exact mul_div_cancel_right₀ (Real.pi * ‖w‖) two_ne_zero
                  exact congrArg Neg.neg hinside
                _ = -Real.pi * ‖w‖ := by
                  exact (neg_mul Real.pi ‖w‖).symm
            have hcoeff :
                (c / 2) * ‖w‖ * Real.exp (-Real.pi * ‖w‖) =
                  c * (‖w‖ / 2) *
                    Real.exp (-Real.pi * ‖w‖) := by
              calc
                (c / 2) * ‖w‖ * Real.exp (-Real.pi * ‖w‖) =
                    (c * ‖w‖ / 2) * Real.exp (-Real.pi * ‖w‖) := by
                  exact
                    congrArg (fun x : ℝ => x * Real.exp (-Real.pi * ‖w‖))
                      (div_mul_eq_mul_div c 2 ‖w‖)
                _ = c * (‖w‖ / 2) * Real.exp (-Real.pi * ‖w‖) := by
                  exact
                    congrArg (fun x : ℝ => x * Real.exp (-Real.pi * ‖w‖))
                      (mul_div_assoc c ‖w‖ 2)
            have htail_at_half :
                c * (‖w‖ / 2) * Real.exp (-Real.pi * ‖w‖) ≤
                  Complex.binetSecondFormulaDecayingTailIntegral w :=
              Eq.subst
                (motive := fun x : ℝ =>
                  c * (‖w‖ / 2) * Real.exp x ≤
                    Complex.binetSecondFormulaDecayingTailIntegral w)
                hexponent
                (htail_lower (‖w‖ / 2) hhalf_ge_one)
            le_trans (le_of_eq hcoeff) htail_at_half⟩

/-- Owner real-variable leaf: exponential lower bound for the Binet decaying
tail integral. -/
theorem Complex.binetSecondFormula_decayingTailIntegral_expLower_owner :
    Complex.BinetSecondFormulaDecayingTailIntegralExpLower := by
  exact
    Complex.binetSecondFormula_decayingTailIntegral_expLower_of_realTailLower
      Real.binetSecondFormula_kernel_majorant_tail_expLower_owner

end
end LFunctions
end Boundary
