import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionAffineValues
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaAffineKernelEstimate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanBinetKernelIntegrals

/-!
# Archimedean Gamma/Binet line values

This file owns the two individual Gamma/Binet affine-line value theorems used
to assemble the right-minus-left archimedean contribution.  It is above the
right-minus-left assembly theorem: this file proves the two one-line limits,
while `ArchimedeanGammaBinetValue.lean` only subtracts them and checks the
normalization.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The elementary `π` contribution in the `Gammaℝ` logarithmic derivative.

With the completed-zeta normalization used in this lane,
`Gammaℝ'/Gammaℝ = gammaRealPiLogDerivativeTerm + (1/2) * Gamma'/Gamma(s/2)`. -/
noncomputable def zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm : ℂ :=
  Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))

/-- Right affine-line Binet main kernel for the archimedean logarithmic
derivative.

The sign is forced by
`explicitFormulaArchimedeanLogDerivative = inverseGammaCompletionLogDeriv -
explicitFormulaCorrectionLogDerivative` and
`inverseGammaCompletionLogDeriv = - Gammaℝ'/Gammaℝ`. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) (t / 2)) -
      explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaRightAffineLine F t)) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)

/-- Right affine-line Binet remainder kernel for the archimedean logarithmic
derivative. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (-((1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalRemainder
        (F.c / 2) (t / 2))) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)

/-- The canonical finite Gamma-recurrence shift used on the left affine
archimedean half-line. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat
    (F : ExplicitFormulaContourFamily) : ℕ :=
  Complex.GammaLogDerivativeFixedVerticalPositiveShiftNat
    ((1 - F.c) / 2)

/-- Left affine-line Binet main kernel for the archimedean logarithmic
derivative. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
    (-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatMain
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2)) -
      explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaLeftAffineLine F t)) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- Left affine-line Binet remainder kernel for the archimedean logarithmic
derivative. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (-((1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
        ((1 - F.c) / 2)
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
        (t / 2))) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- Coupled whole-line right Gamma/Binet transform integral.

The main and differentiated-remainder terms are deliberately kept together:
the owner value theorem evaluates this coupled transform, not either summand
separately. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) : ℂ :=
  (∫ t : ℝ,
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F t) +
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel f F t

/-- Coupled whole-line shifted-left Gamma/Binet transform integral.

The finite Gamma-recurrence shift is part of the coupled left transform and must
not be peeled into a downstream correction term. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) : ℂ :=
  (∫ t : ℝ,
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F t) +
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel f F t

/-- The right coupled whole-line Gamma/Binet transform integral unfolds to the
sum of the main and differentiated-remainder integrals. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral
        f F =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F t :=
  rfl

/-- The shifted-left coupled whole-line Gamma/Binet transform integral unfolds to
the sum of the shifted main and differentiated-remainder integrals. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral
        f F =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F t :=
  rfl

/-- A linearly bounded factor times the right centered test transform has an
integrable majorant.  The Gamma/Binet owner layer supplies the factor
measurability and the factor bound; this theorem owns only the reusable
Paley-Wiener multiplication step. -/
theorem zetaCompletedExplicitFormulaRightCenteredAffineProduct_majorantPackage_of_linear_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A : ℝ → ℂ) (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hA_meas : AEStronglyMeasurable A (volume : Measure ℝ))
    (hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ =>
        A t *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 4
  let majorant : ℝ → ℝ := fun t : ℝ => B * C * (1 + ‖t‖) ^ (-(3 : ℤ))
  have hC_nonneg : 0 ≤ C :=
    h.phi_control.verticalStripRapidDecayConstant_nonneg
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 4
  have hintegrable :
      Integrable majorant (volume : Measure ℝ) := by
    have hfinrank : finrank ℝ ℝ = 1 :=
      Module.finrank_self ℝ
    have hfinrank_cast : ((finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
      congrArg (fun n : ℕ => (n : ℝ)) hfinrank
    have hdim : (finrank ℝ ℝ : ℝ) < 3 :=
      Eq.subst
        (motive := fun x : ℝ => x < 3)
        hfinrank_cast.symm
        (one_lt_of_lt two_lt_three)
    have hbase :
        Integrable
          (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      integrable_one_add_norm (E := ℝ) (μ := volume) hdim
    have hscaled :
        Integrable
          (fun t : ℝ => B * C * (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      (hbase.const_mul C).const_mul B
    have hfun :
        majorant =
          (fun t : ℝ => B * C * (1 + ‖t‖) ^ (-(3 : ℝ))) := by
      funext t
      have hpow :
          (1 + ‖t‖) ^ (-(3 : ℤ)) =
            (1 + ‖t‖) ^ (-(3 : ℝ)) :=
        (Real.rpow_intCast (1 + ‖t‖) (-(3 : ℤ))).symm
      exact congrArg (fun x : ℝ => B * C * x) hpow
    exact
      Eq.subst
        (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
        hfun.symm
        hscaled
  have hphi_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_aestronglyMeasurable
      f F h
  have hbound :
      ∀ᵐ t ∂(volume : Measure ℝ),
        ‖A t‖ *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖ ≤
          majorant t :=
    Filter.Eventually.of_forall
      (fun t : ℝ =>
        have hfactor : ‖A t‖ ≤ B * (1 + ‖t‖) :=
          hA_bound t
        have hphi :
            ‖zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖ ≤
              C * (1 + ‖t‖) ^ (-(4 : ℤ)) :=
          zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_decay_bound
            f F h 4 t
        have hphi_nonneg :
            0 ≤ ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖ :=
          norm_nonneg
            (zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))
        have hfactor_rhs_nonneg : 0 ≤ B * (1 + ‖t‖) :=
          mul_nonneg hB_nonneg (Real.zero_le_one_add_norm t)
        have hprod :
            ‖A t‖ *
                ‖zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖ ≤
              (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) :=
          mul_le_mul hfactor hphi hphi_nonneg hfactor_rhs_nonneg
        have hbase_nonzero : (1 + ‖t‖ : ℝ) ≠ 0 :=
          ne_of_gt (lt_of_lt_of_le zero_lt_one (Real.one_le_one_add_norm t))
        have hweight :
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
              (1 + ‖t‖) ^ (-(3 : ℤ)) := by
          calc
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
                (1 + ‖t‖) ^ ((1 : ℤ) + (-(4 : ℤ))) := by
              exact (zpow_add₀ hbase_nonzero (1 : ℤ) (-(4 : ℤ))).symm
            _ = (1 + ‖t‖) ^ (-(3 : ℤ)) := by
              rfl
        have hassoc :
            (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) =
              B * C * (1 + ‖t‖) ^ (-(3 : ℤ)) := by
          let a : ℝ := 1 + ‖t‖
          let b : ℝ := (1 + ‖t‖) ^ (-(4 : ℤ))
          have hscalar :
              (B * a) * (C * b) = B * C * (a * b) := by
            calc
              (B * a) * (C * b) = B * (a * (C * b)) :=
                mul_assoc B a (C * b)
              _ = B * ((a * C) * b) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc a C b).symm
              _ = B * ((C * a) * b) := by
                exact congrArg (fun x : ℝ => B * (x * b)) (mul_comm a C)
              _ = B * (C * (a * b)) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc C a b)
              _ = B * C * (a * b) := by
                exact (mul_assoc B C (a * b)).symm
          have hrewrite : a * b = (1 + ‖t‖) ^ (-(3 : ℤ)) :=
            hweight
          exact
            Eq.trans hscalar
              (congrArg (fun x : ℝ => B * C * x) hrewrite)
        hprod.trans_eq hassoc)
  exact
    ExplicitFormulaAffineKernelMajorantPackage.of_mul_le
      majorant hintegrable hA_meas hphi_meas hbound

/-- A linearly bounded factor times the left centered test transform has an
integrable majorant. -/
theorem zetaCompletedExplicitFormulaLeftCenteredAffineProduct_majorantPackage_of_linear_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A : ℝ → ℂ) (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hA_meas : AEStronglyMeasurable A (volume : Measure ℝ))
    (hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ =>
        A t *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 4
  let majorant : ℝ → ℝ := fun t : ℝ => B * C * (1 + ‖t‖) ^ (-(3 : ℤ))
  have hC_nonneg : 0 ≤ C :=
    h.phi_control.verticalStripRapidDecayConstant_nonneg
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 4
  have hintegrable :
      Integrable majorant (volume : Measure ℝ) := by
    have hfinrank : finrank ℝ ℝ = 1 :=
      Module.finrank_self ℝ
    have hfinrank_cast : ((finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
      congrArg (fun n : ℕ => (n : ℝ)) hfinrank
    have hdim : (finrank ℝ ℝ : ℝ) < 3 :=
      Eq.subst
        (motive := fun x : ℝ => x < 3)
        hfinrank_cast.symm
        (one_lt_of_lt two_lt_three)
    have hbase :
        Integrable
          (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      integrable_one_add_norm (E := ℝ) (μ := volume) hdim
    have hscaled :
        Integrable
          (fun t : ℝ => B * C * (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      (hbase.const_mul C).const_mul B
    have hfun :
        majorant =
          (fun t : ℝ => B * C * (1 + ‖t‖) ^ (-(3 : ℝ))) := by
      funext t
      have hpow :
          (1 + ‖t‖) ^ (-(3 : ℤ)) =
            (1 + ‖t‖) ^ (-(3 : ℝ)) :=
        (Real.rpow_intCast (1 + ‖t‖) (-(3 : ℤ))).symm
      exact congrArg (fun x : ℝ => B * C * x) hpow
    exact
      Eq.subst
        (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
        hfun.symm
        hscaled
  have hphi_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_aestronglyMeasurable
      f F h
  have hbound :
      ∀ᵐ t ∂(volume : Measure ℝ),
        ‖A t‖ *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ ≤
          majorant t :=
    Filter.Eventually.of_forall
      (fun t : ℝ =>
        have hfactor : ‖A t‖ ≤ B * (1 + ‖t‖) :=
          hA_bound t
        have hphi :
            ‖zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ ≤
              C * (1 + ‖t‖) ^ (-(4 : ℤ)) :=
          zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_decay_bound
            f F h 4 t
        have hphi_nonneg :
            0 ≤ ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ :=
          norm_nonneg
            (zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
        have hfactor_rhs_nonneg : 0 ≤ B * (1 + ‖t‖) :=
          mul_nonneg hB_nonneg (Real.zero_le_one_add_norm t)
        have hprod :
            ‖A t‖ *
                ‖zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ ≤
              (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) :=
          mul_le_mul hfactor hphi hphi_nonneg hfactor_rhs_nonneg
        have hbase_nonzero : (1 + ‖t‖ : ℝ) ≠ 0 :=
          ne_of_gt (lt_of_lt_of_le zero_lt_one (Real.one_le_one_add_norm t))
        have hweight :
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
              (1 + ‖t‖) ^ (-(3 : ℤ)) := by
          calc
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
                (1 + ‖t‖) ^ ((1 : ℤ) + (-(4 : ℤ))) := by
              exact (zpow_add₀ hbase_nonzero (1 : ℤ) (-(4 : ℤ))).symm
            _ = (1 + ‖t‖) ^ (-(3 : ℤ)) := by
              rfl
        have hassoc :
            (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) =
              B * C * (1 + ‖t‖) ^ (-(3 : ℤ)) := by
          let a : ℝ := 1 + ‖t‖
          let b : ℝ := (1 + ‖t‖) ^ (-(4 : ℤ))
          have hscalar :
              (B * a) * (C * b) = B * C * (a * b) := by
            calc
              (B * a) * (C * b) = B * (a * (C * b)) :=
                mul_assoc B a (C * b)
              _ = B * ((a * C) * b) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc a C b).symm
              _ = B * ((C * a) * b) := by
                exact congrArg (fun x : ℝ => B * (x * b)) (mul_comm a C)
              _ = B * (C * (a * b)) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc C a b)
              _ = B * C * (a * b) := by
                exact (mul_assoc B C (a * b)).symm
          have hrewrite : a * b = (1 + ‖t‖) ^ (-(3 : ℤ)) :=
            hweight
          exact
            Eq.trans hscalar
              (congrArg (fun x : ℝ => B * C * x) hrewrite)
        hprod.trans_eq hassoc)
  exact
    ExplicitFormulaAffineKernelMajorantPackage.of_mul_le
      majorant hintegrable hA_meas hphi_meas hbound

/-- Strong measurability of the elementary correction logarithmic derivative
on the right affine line. -/
theorem zetaCompletedExplicitFormulaCorrectionLogDerivative_rightAffineLine_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine F t))
      (volume : Measure ℝ) := by
  let line : ℝ → ℂ := fun t : ℝ => zetaCompletedExplicitFormulaRightAffineLine F t
  have hline : Measurable line :=
    (zetaCompletedExplicitFormulaRightAffineLine_continuous F).measurable
  have hzero :
      Measurable (fun t : ℝ => (-1 : ℂ) / line t) :=
    measurable_const.div hline
  have hone :
      Measurable (fun t : ℝ => (1 : ℂ) / (line t - 1)) :=
    measurable_const.div (hline.sub measurable_const)
  have hpole :
      (fun t : ℝ => explicitFormulaCorrectionLogDerivative (line t)) =
        (fun t : ℝ => (-1 : ℂ) / line t - (1 : ℂ) / (line t - 1)) := by
    funext t
    exact explicitFormulaCorrectionLogDerivative_eq_poleCorrection (line t)
  have hmeas :
      Measurable
        (fun t : ℝ => (-1 : ℂ) / line t - (1 : ℂ) / (line t - 1)) :=
    hzero.sub hone
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        AEStronglyMeasurable φ (volume : Measure ℝ))
      hpole.symm
      hmeas.aestronglyMeasurable

/-- Strong measurability of the elementary correction logarithmic derivative
on the left affine line. -/
theorem zetaCompletedExplicitFormulaCorrectionLogDerivative_leftAffineLine_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftAffineLine F t))
      (volume : Measure ℝ) := by
  let line : ℝ → ℂ := fun t : ℝ => zetaCompletedExplicitFormulaLeftAffineLine F t
  have hline : Measurable line :=
    (zetaCompletedExplicitFormulaLeftAffineLine_continuous F).measurable
  have hzero :
      Measurable (fun t : ℝ => (-1 : ℂ) / line t) :=
    measurable_const.div hline
  have hone :
      Measurable (fun t : ℝ => (1 : ℂ) / (line t - 1)) :=
    measurable_const.div (hline.sub measurable_const)
  have hpole :
      (fun t : ℝ => explicitFormulaCorrectionLogDerivative (line t)) =
        (fun t : ℝ => (-1 : ℂ) / line t - (1 : ℂ) / (line t - 1)) := by
    funext t
    exact explicitFormulaCorrectionLogDerivative_eq_poleCorrection (line t)
  have hmeas :
      Measurable
        (fun t : ℝ => (-1 : ℂ) / line t - (1 : ℂ) / (line t - 1)) :=
    hzero.sub hone
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        AEStronglyMeasurable φ (volume : Measure ℝ))
      hpole.symm
      hmeas.aestronglyMeasurable

/-- Strong measurability of the right archimedean Binet main factor before
multiplication by the centered test transform. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainFactor_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        -(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalMain
                (F.c / 2) (t / 2)) -
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t))
      (volume : Measure ℝ) := by
  have hscale : Measurable (fun t : ℝ => t / 2) :=
    measurable_id.div_const 2
  have hgamma :
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.GammaLogDerivativeFixedVerticalMain (F.c / 2) (t / 2))
        (volume : Measure ℝ) :=
    (Complex.GammaLogDerivativeFixedVerticalMain_aestronglyMeasurable
      (F.c / 2)).comp_measurable hscale
  have hhalf :
      AEStronglyMeasurable
        (fun t : ℝ =>
          (1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalMain (F.c / 2) (t / 2))
        (volume : Measure ℝ) :=
    hgamma.const_mul (1 / 2 : ℂ)
  have hwith_pi :
      AEStronglyMeasurable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalMain (F.c / 2) (t / 2))
        (volume : Measure ℝ) :=
    aestronglyMeasurable_const.add hhalf
  have hcorr :
      AEStronglyMeasurable
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLogDerivative_rightAffineLine_aestronglyMeasurable
      F
  exact hwith_pi.neg.sub hcorr

/-- Strong measurability of the left archimedean Binet main factor before
multiplication by the centered test transform. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainFactor_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        -(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                ((1 - F.c) / 2)
                (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
                (t / 2)) -
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftAffineLine F t))
      (volume : Measure ℝ) := by
  have hscale : Measurable (fun t : ℝ => t / 2) :=
    measurable_id.div_const 2
  have hgamma :
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.GammaLogDerivativeFixedVerticalShiftNatMain
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2))
        (volume : Measure ℝ) :=
    (Complex.GammaLogDerivativeFixedVerticalShiftNatMain_aestronglyMeasurable
      ((1 - F.c) / 2)
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)).comp_measurable
        hscale
  have hhalf :
      AEStronglyMeasurable
        (fun t : ℝ =>
          (1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalShiftNatMain
              ((1 - F.c) / 2)
              (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
              (t / 2))
        (volume : Measure ℝ) :=
    hgamma.const_mul (1 / 2 : ℂ)
  have hwith_pi :
      AEStronglyMeasurable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                ((1 - F.c) / 2)
                (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
                (t / 2))
        (volume : Measure ℝ) :=
    aestronglyMeasurable_const.add hhalf
  have hcorr :
      AEStronglyMeasurable
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLogDerivative_leftAffineLine_aestronglyMeasurable
      F
  exact hwith_pi.neg.sub hcorr

/-- Strong measurability of the right archimedean Binet main kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanRightBinetMainFactor_aestronglyMeasurable
    F).mul
    (zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_aestronglyMeasurable
      f F h)

/-- Strong measurability of the left archimedean Binet main kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainFactor_aestronglyMeasurable
    F).mul
    (zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_aestronglyMeasurable
      f F h)

/-- Strong measurability of the right archimedean Binet remainder factor before
multiplication by the centered test transform. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderFactor_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        -((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2)))
      (volume : Measure ℝ) := by
  have hscale : Measurable (fun t : ℝ => t / 2) :=
    measurable_id.div_const 2
  have hgamma :
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.GammaLogDerivativeFixedVerticalRemainder (F.c / 2) (t / 2))
        (volume : Measure ℝ) :=
    (Complex.GammaLogDerivativeFixedVerticalRemainder_aestronglyMeasurable
      (F.c / 2)).comp_measurable hscale
  exact (hgamma.const_mul (1 / 2 : ℂ)).neg

/-- Strong measurability of the left archimedean Binet remainder factor before
multiplication by the centered test transform. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderFactor_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        -((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2)))
      (volume : Measure ℝ) := by
  have hscale : Measurable (fun t : ℝ => t / 2) :=
    measurable_id.div_const 2
  have hgamma :
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2))
        (volume : Measure ℝ) :=
    (Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder_aestronglyMeasurable
      ((1 - F.c) / 2)
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)).comp_measurable
        hscale
  exact (hgamma.const_mul (1 / 2 : ℂ)).neg

/-- Strong measurability of the right archimedean Binet remainder kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderFactor_aestronglyMeasurable
    F).mul
    (zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_aestronglyMeasurable
      f F h)

/-- Strong measurability of the left archimedean Binet remainder kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderFactor_aestronglyMeasurable
    F).mul
    (zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_aestronglyMeasurable
      f F h)

/-- Half-height rescaling does not increase the affine linear weight. -/
theorem real_one_add_norm_div_two_le_one_add_norm
    (t : ℝ) :
    1 + ‖t / 2‖ ≤ 1 + ‖t‖ := by
  have htwo_abs : |(2 : ℝ)| = 2 :=
    abs_of_nonneg zero_le_two
  have htwo_inv_le_one : (2 : ℝ)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ one_le_two
  have hnorm_div :
      ‖t / 2‖ = ‖t‖ * (2 : ℝ)⁻¹ := by
    calc
      ‖t / 2‖ = |t / 2| := by
        exact Real.norm_eq_abs (t / 2)
      _ = |t| / |(2 : ℝ)| := by
        exact abs_div t 2
      _ = |t| / 2 := by
        exact congrArg (fun x : ℝ => |t| / x) htwo_abs
      _ = |t| * (2 : ℝ)⁻¹ := by
        exact div_eq_mul_inv |t| 2
      _ = ‖t‖ * (2 : ℝ)⁻¹ := by
        exact congrArg (fun x : ℝ => x * (2 : ℝ)⁻¹) (Real.norm_eq_abs t).symm
  have hhalf_le : ‖t / 2‖ ≤ ‖t‖ := by
    calc
      ‖t / 2‖ = ‖t‖ * (2 : ℝ)⁻¹ := hnorm_div
      _ ≤ ‖t‖ * 1 :=
        mul_le_mul_of_nonneg_left htwo_inv_le_one (norm_nonneg t)
      _ = ‖t‖ := mul_one ‖t‖
  exact add_le_add_left hhalf_le 1

/-- A nonnegative constant is bounded by the corresponding affine linear
weight. -/
theorem real_nonneg_le_mul_one_add_norm
    {B : ℝ} (hB : 0 ≤ B) (t : ℝ) :
    B ≤ B * (1 + ‖t‖) := by
  calc
    B = B * 1 := (mul_one B).symm
    _ ≤ B * (1 + ‖t‖) :=
      mul_le_mul_of_nonneg_left (Real.one_le_one_add_norm t) hB

/-- The elementary correction logarithmic derivative on the right line has a
uniform, hence linear, bound. -/
theorem zetaCompletedExplicitFormulaCorrectionLogDerivative_rightAffineLine_linear_bound
    (F : ExplicitFormulaContourFamily) :
    ∀ t : ℝ,
      ‖explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
        ((1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1)) *
          (1 + ‖t‖) := by
  intro t
  let line : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
  let Z : ℂ := -1 / line
  let O : ℂ := -(1 / (line - 1))
  have hpole :
      explicitFormulaCorrectionLogDerivative line = Z + O := by
    calc
      explicitFormulaCorrectionLogDerivative line =
          (-1 : ℂ) / line - (1 : ℂ) / (line - 1) := by
        exact explicitFormulaCorrectionLogDerivative_eq_poleCorrection line
      _ = Z + O := by
        exact sub_eq_add_neg ((-1 : ℂ) / line) ((1 : ℂ) / (line - 1))
  have hZ : ‖Z‖ ≤ (1 : ℝ) / F.c :=
    zetaCompletedExplicitFormulaRightAffineLine_zeroPoleCoefficient_norm_le
      F t
  have hO : ‖O‖ ≤ (1 : ℝ) / (F.c - 1) :=
    zetaCompletedExplicitFormulaRightAffineLine_onePoleCoefficient_norm_le
      F t
  have hsum :
      ‖Z‖ + ‖O‖ ≤ (1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1) :=
    add_le_add hZ hO
  have hconst_nonneg :
      0 ≤ (1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1) :=
    add_nonneg
      (div_nonneg zero_le_one F.c_pos.le)
      (div_nonneg zero_le_one (sub_pos.mpr F.c_gt_one).le)
  calc
    ‖explicitFormulaCorrectionLogDerivative line‖ = ‖Z + O‖ := by
      exact congrArg norm hpole
    _ ≤ ‖Z‖ + ‖O‖ :=
      norm_add_le Z O
    _ ≤ (1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1) :=
      hsum
    _ ≤ ((1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1)) *
        (1 + ‖t‖) :=
      real_nonneg_le_mul_one_add_norm hconst_nonneg t

/-- The elementary correction logarithmic derivative on the left line has a
uniform, hence linear, bound. -/
theorem zetaCompletedExplicitFormulaCorrectionLogDerivative_leftAffineLine_linear_bound
    (F : ExplicitFormulaContourFamily) :
    ∀ t : ℝ,
      ‖explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
        ((1 : ℝ) / (-(1 - F.c)) +
            (1 : ℝ) / (-((1 - F.c) - 1))) *
          (1 + ‖t‖) := by
  intro t
  let line : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  let Z : ℂ := -1 / line
  let O : ℂ := -(1 / (line - 1))
  have hpole :
      explicitFormulaCorrectionLogDerivative line = Z + O := by
    calc
      explicitFormulaCorrectionLogDerivative line =
          (-1 : ℂ) / line - (1 : ℂ) / (line - 1) := by
        exact explicitFormulaCorrectionLogDerivative_eq_poleCorrection line
      _ = Z + O := by
        exact sub_eq_add_neg ((-1 : ℂ) / line) ((1 : ℂ) / (line - 1))
  have hZ : ‖Z‖ ≤ (1 : ℝ) / (-(1 - F.c)) :=
    zetaCompletedExplicitFormulaLeftAffineLine_zeroPoleCoefficient_norm_le
      F t
  have hO : ‖O‖ ≤ (1 : ℝ) / (-((1 - F.c) - 1)) :=
    zetaCompletedExplicitFormulaLeftAffineLine_onePoleCoefficient_norm_le
      F t
  have hsum :
      ‖Z‖ + ‖O‖ ≤
        (1 : ℝ) / (-(1 - F.c)) +
          (1 : ℝ) / (-((1 - F.c) - 1)) :=
    add_le_add hZ hO
  have hzero_den_pos : 0 < -(1 - F.c) :=
    neg_pos.mpr F.one_sub_c_neg
  have hone_den_pos : 0 < -((1 - F.c) - 1) := by
    have hneg : (1 - F.c) - 1 < 0 := by
      calc
        (1 - F.c) - 1 < 0 - 1 := by
          exact sub_lt_sub_right F.one_sub_c_neg 1
        _ < 0 := by
          exact neg_lt_zero.mpr zero_lt_one
    exact neg_pos.mpr hneg
  have hconst_nonneg :
      0 ≤
        (1 : ℝ) / (-(1 - F.c)) +
          (1 : ℝ) / (-((1 - F.c) - 1)) :=
    add_nonneg
      (div_nonneg zero_le_one hzero_den_pos.le)
      (div_nonneg zero_le_one hone_den_pos.le)
  calc
    ‖explicitFormulaCorrectionLogDerivative line‖ = ‖Z + O‖ := by
      exact congrArg norm hpole
    _ ≤ ‖Z‖ + ‖O‖ :=
      norm_add_le Z O
    _ ≤
        (1 : ℝ) / (-(1 - F.c)) +
          (1 : ℝ) / (-((1 - F.c) - 1)) :=
      hsum
    _ ≤
        ((1 : ℝ) / (-(1 - F.c)) +
            (1 : ℝ) / (-((1 - F.c) - 1))) *
          (1 + ‖t‖) :=
      real_nonneg_le_mul_one_add_norm hconst_nonneg t

/-- The right Binet main factor has linear growth on the scheduled right
affine half-line. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainFactor_linear_bound
    (F : ExplicitFormulaContourFamily) :
    ∀ t : ℝ,
      ‖-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalMain
                (F.c / 2) (t / 2)) -
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
        (‖zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm‖ +
            ‖(1 / 2 : ℂ)‖ *
              ((|Real.log (F.c / 2)| + (F.c / 2 + 1) + Real.pi) +
                1 / (F.c / 2)) +
            ((1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1))) *
          (1 + ‖t‖) := by
  intro t
  let P : ℂ := zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm
  let G : ℂ :=
    (1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalMain (F.c / 2) (t / 2)
  let C : ℂ :=
    explicitFormulaCorrectionLogDerivative
      (zetaCompletedExplicitFormulaRightAffineLine F t)
  let M : ℝ :=
    (|Real.log (F.c / 2)| + (F.c / 2 + 1) + Real.pi) +
      1 / (F.c / 2)
  let K : ℝ := (1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1)
  have hσ : 0 < F.c / 2 :=
    div_pos F.c_pos zero_lt_two
  have hM_nonneg : 0 ≤ M :=
    Complex.GammaLogDerivativeFixedVerticalMainLinearConstant_nonneg hσ
  have hP_nonneg : 0 ≤ ‖P‖ :=
    norm_nonneg P
  have hhalf_nonneg : 0 ≤ ‖(1 / 2 : ℂ)‖ :=
    norm_nonneg (1 / 2 : ℂ)
  have hhalfM_nonneg : 0 ≤ ‖(1 / 2 : ℂ)‖ * M :=
    mul_nonneg hhalf_nonneg hM_nonneg
  have hK_nonneg : 0 ≤ K :=
    add_nonneg
      (div_nonneg zero_le_one F.c_pos.le)
      (div_nonneg zero_le_one (sub_pos.mpr F.c_gt_one).le)
  have hG_raw :
      ‖G‖ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t / 2‖)) := by
    have hmain :
        ‖Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) (t / 2)‖ ≤
          M * (1 + ‖t / 2‖) :=
      Complex.GammaLogDerivativeFixedVerticalMain_polynomial_bound
        hσ (t / 2)
    calc
      ‖G‖ =
          ‖(1 / 2 : ℂ)‖ *
            ‖Complex.GammaLogDerivativeFixedVerticalMain
              (F.c / 2) (t / 2)‖ := by
        exact norm_mul (1 / 2 : ℂ)
          (Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) (t / 2))
      _ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t / 2‖)) :=
        mul_le_mul_of_nonneg_left hmain hhalf_nonneg
  have hG :
      ‖G‖ ≤ (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) := by
    have hweight :
        M * (1 + ‖t / 2‖) ≤ M * (1 + ‖t‖) :=
      mul_le_mul_of_nonneg_left
        (real_one_add_norm_div_two_le_one_add_norm t)
        hM_nonneg
    calc
      ‖G‖ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t / 2‖)) :=
        hG_raw
      _ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t‖)) :=
        mul_le_mul_of_nonneg_left hweight hhalf_nonneg
      _ = (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) := by
        exact (mul_assoc ‖(1 / 2 : ℂ)‖ M (1 + ‖t‖)).symm
  have hP :
      ‖P‖ ≤ ‖P‖ * (1 + ‖t‖) :=
    real_nonneg_le_mul_one_add_norm hP_nonneg t
  have hC :
      ‖C‖ ≤ K * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaCorrectionLogDerivative_rightAffineLine_linear_bound
      F t
  have hsum :
      ‖P‖ + ‖G‖ + ‖C‖ ≤
        ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) :=
    add_le_add (add_le_add hP hG) hC
  have hfactor :
      ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) =
        (‖P‖ + ‖(1 / 2 : ℂ)‖ * M + K) * (1 + ‖t‖) := by
    calc
      ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) =
        (‖P‖ + ‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) := by
          exact congrArg
            (fun x : ℝ => x + K * (1 + ‖t‖))
            (add_mul ‖P‖ (‖(1 / 2 : ℂ)‖ * M) (1 + ‖t‖)).symm
      _ = (‖P‖ + ‖(1 / 2 : ℂ)‖ * M + K) * (1 + ‖t‖) := by
          exact (add_mul (‖P‖ + ‖(1 / 2 : ℂ)‖ * M) K (1 + ‖t‖)).symm
  calc
    ‖-(P + G) - C‖ ≤ ‖-(P + G)‖ + ‖C‖ :=
      norm_sub_le (-(P + G)) C
    _ = ‖P + G‖ + ‖C‖ := by
      exact congrArg (fun x : ℝ => x + ‖C‖) (norm_neg (P + G))
    _ ≤ (‖P‖ + ‖G‖) + ‖C‖ := by
      have hpg : ‖P + G‖ ≤ ‖P‖ + ‖G‖ :=
        norm_add_le P G
      exact add_le_add_right hpg ‖C‖
    _ = ‖P‖ + ‖G‖ + ‖C‖ :=
      add_assoc ‖P‖ ‖G‖ ‖C‖
    _ ≤
        ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) :=
      hsum
    _ =
        (‖P‖ + ‖(1 / 2 : ℂ)‖ * M + K) * (1 + ‖t‖) :=
      hfactor

/-- The right Binet remainder factor has linear growth on the scheduled
right affine half-line. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderFactor_linear_bound
    (F : ExplicitFormulaContourFamily) :
    ∀ t : ℝ,
      ‖-((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2))‖ ≤
        (‖(1 / 2 : ℂ)‖ *
          |‖(2 : ℂ)‖ *
            ∫ u : ℝ in Set.Ioi (0 : ℝ),
              (1 / (F.c / 2) ^ 2) *
                (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))|) *
          (1 + ‖t‖) := by
  intro t
  let C : ℝ :=
    |‖(2 : ℂ)‖ *
      ∫ u : ℝ in Set.Ioi (0 : ℝ),
        (1 / (F.c / 2) ^ 2) *
          (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))|
  have hσ : 0 < F.c / 2 :=
    div_pos F.c_pos zero_lt_two
  have hR :
      ‖Complex.GammaLogDerivativeFixedVerticalRemainder
          (F.c / 2) (t / 2)‖ ≤
        C * (1 + ‖t / 2‖) :=
    Complex.GammaLogDerivativeFixedVerticalRemainder_linear_bound
      hσ (t / 2)
  have hC_nonneg : 0 ≤ C :=
    abs_nonneg
      (‖(2 : ℂ)‖ *
        ∫ u : ℝ in Set.Ioi (0 : ℝ),
          (1 / (F.c / 2) ^ 2) *
            (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1)))
  have hhalf_nonneg : 0 ≤ ‖(1 / 2 : ℂ)‖ :=
    norm_nonneg (1 / 2 : ℂ)
  have hweight :
      C * (1 + ‖t / 2‖) ≤ C * (1 + ‖t‖) :=
    mul_le_mul_of_nonneg_left
      (real_one_add_norm_div_two_le_one_add_norm t)
      hC_nonneg
  have hscaled :
      ‖(1 / 2 : ℂ)‖ *
          ‖Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2)‖ ≤
        ‖(1 / 2 : ℂ)‖ * (C * (1 + ‖t‖)) :=
    mul_le_mul_of_nonneg_left (hR.trans hweight) hhalf_nonneg
  calc
    ‖-((1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalRemainder
          (F.c / 2) (t / 2))‖ =
        ‖(1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2)‖ := by
      exact norm_neg
        ((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2))
    _ =
        ‖(1 / 2 : ℂ)‖ *
          ‖Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2)‖ := by
      exact norm_mul (1 / 2 : ℂ)
        (Complex.GammaLogDerivativeFixedVerticalRemainder
          (F.c / 2) (t / 2))
    _ ≤ ‖(1 / 2 : ℂ)‖ * (C * (1 + ‖t‖)) :=
      hscaled
    _ =
        (‖(1 / 2 : ℂ)‖ * C) * (1 + ‖t‖) := by
      exact (mul_assoc ‖(1 / 2 : ℂ)‖ C (1 + ‖t‖)).symm

/-- The right Binet main kernel has the standard affine integrable majorant
package. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    -(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) (t / 2)) -
      explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaRightAffineLine F t)
  let B : ℝ :=
    ‖zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm‖ +
      ‖(1 / 2 : ℂ)‖ *
        ((|Real.log (F.c / 2)| + (F.c / 2 + 1) + Real.pi) +
          1 / (F.c / 2)) +
      ((1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1))
  have hσ : 0 < F.c / 2 :=
    div_pos F.c_pos zero_lt_two
  have hM_nonneg :
      0 ≤
        (|Real.log (F.c / 2)| + (F.c / 2 + 1) + Real.pi) +
          1 / (F.c / 2) :=
    Complex.GammaLogDerivativeFixedVerticalMainLinearConstant_nonneg hσ
  have hB_nonneg : 0 ≤ B :=
    add_nonneg
      (add_nonneg
        (norm_nonneg zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm)
        (mul_nonneg (norm_nonneg (1 / 2 : ℂ)) hM_nonneg))
      (add_nonneg
        (div_nonneg zero_le_one F.c_pos.le)
        (div_nonneg zero_le_one (sub_pos.mpr F.c_gt_one).le))
  have hA_meas :
      AEStronglyMeasurable A (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainFactor_aestronglyMeasurable
      F
  have hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainFactor_linear_bound
      F
  exact
    zetaCompletedExplicitFormulaRightCenteredAffineProduct_majorantPackage_of_linear_factor_bound
      f F h A B hB_nonneg hA_meas hA_bound

/-- Half of the right affine line is the fixed-vertical line with real part
`F.c / 2` and height `t / 2`. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_div_two_eq_fixedVertical
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaRightAffineLine F t / 2 =
      ((F.c / 2 : ℝ) + (t / 2 : ℝ) * Complex.I : ℂ) := by
  calc
    zetaCompletedExplicitFormulaRightAffineLine F t / 2 =
        ((F.c : ℂ) + t * Complex.I) / 2 := by
      exact congrArg (fun z : ℂ => z / 2)
        (zetaCompletedExplicitFormulaRightAffineLine_eq F t)
    _ = ((F.c : ℂ) / 2) + (t * Complex.I) / 2 := by
      exact add_div ((F.c : ℂ)) (t * Complex.I) (2 : ℂ)
    _ = (F.c / 2 : ℂ) + (t * Complex.I) / 2 := by
      exact congrArg
        (fun z : ℂ => z + (t * Complex.I) / 2)
        (Complex.ofReal_div F.c 2)
    _ = (F.c / 2 : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
      have ht :
          (t * Complex.I) / 2 = ((t / 2 : ℝ) : ℂ) * Complex.I := by
        calc
          (t * Complex.I) / 2 =
              ((t : ℂ) / 2) * Complex.I := by
            exact (div_mul_eq_mul_div (t : ℂ) Complex.I (2 : ℂ)).symm
          _ = ((t / 2 : ℝ) : ℂ) * Complex.I := by
            exact congrArg (fun z : ℂ => z * Complex.I)
              (Complex.ofReal_div t 2)
      exact congrArg (fun z : ℂ => (F.c / 2 : ℂ) + z) ht
    _ = ((F.c / 2 : ℝ) + (t / 2 : ℝ) * Complex.I : ℂ) := by
      rfl

/-- Half of the left affine line is the fixed-vertical line with real part
`(1 - F.c) / 2` and height `t / 2`. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_div_two_eq_fixedVertical
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaLeftAffineLine F t / 2 =
      (((1 - F.c) / 2 : ℝ) + (t / 2 : ℝ) * Complex.I : ℂ) := by
  calc
    zetaCompletedExplicitFormulaLeftAffineLine F t / 2 =
        (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) / 2 := by
      exact congrArg (fun z : ℂ => z / 2)
        (zetaCompletedExplicitFormulaLeftAffineLine_eq F t)
    _ = (((1 : ℂ) - (F.c : ℂ)) / 2) + (t * Complex.I) / 2 := by
      exact add_div (((1 : ℂ) - (F.c : ℂ))) (t * Complex.I) (2 : ℂ)
    _ = ((1 - F.c) / 2 : ℂ) + (t * Complex.I) / 2 := by
      have hreal :
          (((1 : ℂ) - (F.c : ℂ)) / 2) =
            (((1 - F.c) / 2 : ℝ) : ℂ) := by
        calc
          (((1 : ℂ) - (F.c : ℂ)) / 2) =
              (((1 - F.c : ℝ) : ℂ) / 2) := by
            rfl
          _ = (((1 - F.c) / 2 : ℝ) : ℂ) := by
            exact Complex.ofReal_div (1 - F.c) 2
      exact congrArg
        (fun z : ℂ => z + (t * Complex.I) / 2)
        hreal
    _ = ((1 - F.c) / 2 : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
      have ht :
          (t * Complex.I) / 2 = ((t / 2 : ℝ) : ℂ) * Complex.I := by
        calc
          (t * Complex.I) / 2 =
              ((t : ℂ) / 2) * Complex.I := by
            exact (div_mul_eq_mul_div (t : ℂ) Complex.I (2 : ℂ)).symm
          _ = ((t / 2 : ℝ) : ℂ) * Complex.I := by
            exact congrArg (fun z : ℂ => z * Complex.I)
              (Complex.ofReal_div t 2)
      exact congrArg (fun z : ℂ => ((1 - F.c) / 2 : ℂ) + z) ht
    _ = (((1 - F.c) / 2 : ℝ) + (t / 2 : ℝ) * Complex.I : ℂ) := by
      rfl

/-- The fixed-vertical form of the left half-line avoids the ordinary Gamma
pole locus whenever the left affine line satisfies the completed-Gamma
regularity condition. -/
theorem zetaCompletedExplicitFormulaLeftFixedVertical_ne_Gamma_zero_locus_of_gammaRegular
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (t : ℝ) :
    ∀ n : ℕ,
      (((1 - F.c) / 2 : ℝ) + (t / 2 : ℝ) * Complex.I : ℂ) ≠
        -(n : ℂ) := by
  intro n hn
  have hline :
      zetaCompletedExplicitFormulaLeftAffineLine F t / 2 =
        (((1 - F.c) / 2 : ℝ) + (t / 2 : ℝ) * Complex.I : ℂ) :=
    zetaCompletedExplicitFormulaLeftAffineLine_div_two_eq_fixedVertical F t
  exact
    (zetaCompletedExplicitFormulaLeftAffineLine_half_ne_Gamma_zero_locus_of_gammaRegular
      F hregular t n)
      (hline.trans hn)

/-- The left fixed-vertical half-line avoids ordinary Gamma poles for every
Binet height parameter.  This is the same pole-avoidance statement as above,
with the affine parameter rescaled by `2`. -/
theorem zetaCompletedExplicitFormulaLeftFixedVertical_ne_Gamma_zero_locus_of_gammaRegular'
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (τ : ℝ) :
    ∀ n : ℕ,
      (((1 - F.c) / 2 : ℝ) + τ * Complex.I : ℂ) ≠
        -(n : ℂ) := by
  intro n hn
  have hraw :
      (((1 - F.c) / 2 : ℝ) + ((2 * τ) / 2 : ℝ) * Complex.I : ℂ) ≠
        -(n : ℂ) :=
    zetaCompletedExplicitFormulaLeftFixedVertical_ne_Gamma_zero_locus_of_gammaRegular
      F hregular (2 * τ) n
  have hτ : (2 * τ) / 2 = τ := by
    exact mul_div_cancel_left₀ τ (show (2 : ℝ) ≠ 0 from two_ne_zero)
  have hline :
      (((1 - F.c) / 2 : ℝ) + ((2 * τ) / 2 : ℝ) * Complex.I : ℂ) =
        (((1 - F.c) / 2 : ℝ) + τ * Complex.I : ℂ) := by
    exact congrArg
      (fun x : ℝ => (((1 - F.c) / 2 : ℝ) + x * Complex.I : ℂ))
      hτ
  exact hraw (hline.trans hn)

/-- The left finite-shift Binet main factor has linear growth on the scheduled
left affine half-line, provided the left line avoids Gamma poles. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainFactor_linear_bound
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ∀ t : ℝ,
      ‖-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                ((1 - F.c) / 2)
                (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
                (t / 2)) -
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
        (‖zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm‖ +
            ‖(1 / 2 : ℂ)‖ *
              Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant
                ((1 - F.c) / 2)
                (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F) +
            ((1 : ℝ) / (-(1 - F.c)) +
              (1 : ℝ) / (-((1 - F.c) - 1)))) *
          (1 + ‖t‖) := by
  intro t
  let σ : ℝ := (1 - F.c) / 2
  let N : ℕ := zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F
  let P : ℂ := zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm
  let G : ℂ :=
    (1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalShiftNatMain σ N (t / 2)
  let C : ℂ :=
    explicitFormulaCorrectionLogDerivative
      (zetaCompletedExplicitFormulaLeftAffineLine F t)
  let M : ℝ :=
    Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant σ N
  let K : ℝ :=
    (1 : ℝ) / (-(1 - F.c)) +
      (1 : ℝ) / (-((1 - F.c) - 1))
  have hshift_pos : 0 < σ + (N : ℝ) :=
    Complex.GammaLogDerivativeFixedVerticalPositiveShiftNat_pos σ
  have hnot_pole :
      ∀ τ : ℝ, ∀ n : ℕ,
        (σ + τ * Complex.I : ℂ) ≠ -n :=
    zetaCompletedExplicitFormulaLeftFixedVertical_ne_Gamma_zero_locus_of_gammaRegular'
      F hregular
  have hM_nonneg : 0 ≤ M :=
    Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant_nonneg
      N hshift_pos
  have hP_nonneg : 0 ≤ ‖P‖ :=
    norm_nonneg P
  have hhalf_nonneg : 0 ≤ ‖(1 / 2 : ℂ)‖ :=
    norm_nonneg (1 / 2 : ℂ)
  have hzero_den_pos : 0 < -(1 - F.c) :=
    neg_pos.mpr F.one_sub_c_neg
  have hone_den_pos : 0 < -((1 - F.c) - 1) := by
    have hneg : (1 - F.c) - 1 < 0 := by
      calc
        (1 - F.c) - 1 < 0 - 1 := by
          exact sub_lt_sub_right F.one_sub_c_neg 1
        _ < 0 := by
          exact neg_lt_zero.mpr zero_lt_one
    exact neg_pos.mpr hneg
  have hK_nonneg : 0 ≤ K :=
    add_nonneg
      (div_nonneg zero_le_one hzero_den_pos.le)
      (div_nonneg zero_le_one hone_den_pos.le)
  have hG_raw :
      ‖G‖ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t / 2‖)) := by
    have hmain :
        ‖Complex.GammaLogDerivativeFixedVerticalShiftNatMain
            σ N (t / 2)‖ ≤
          M * (1 + ‖t / 2‖) :=
      Complex.GammaLogDerivativeFixedVerticalShiftNatMain_linear_bound
        N hshift_pos hnot_pole (t / 2)
    calc
      ‖G‖ =
          ‖(1 / 2 : ℂ)‖ *
            ‖Complex.GammaLogDerivativeFixedVerticalShiftNatMain
              σ N (t / 2)‖ := by
        exact norm_mul (1 / 2 : ℂ)
          (Complex.GammaLogDerivativeFixedVerticalShiftNatMain
            σ N (t / 2))
      _ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t / 2‖)) :=
        mul_le_mul_of_nonneg_left hmain hhalf_nonneg
  have hG :
      ‖G‖ ≤ (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) := by
    have hweight :
        M * (1 + ‖t / 2‖) ≤ M * (1 + ‖t‖) :=
      mul_le_mul_of_nonneg_left
        (real_one_add_norm_div_two_le_one_add_norm t)
        hM_nonneg
    calc
      ‖G‖ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t / 2‖)) :=
        hG_raw
      _ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t‖)) :=
        mul_le_mul_of_nonneg_left hweight hhalf_nonneg
      _ = (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) := by
        exact (mul_assoc ‖(1 / 2 : ℂ)‖ M (1 + ‖t‖)).symm
  have hP :
      ‖P‖ ≤ ‖P‖ * (1 + ‖t‖) :=
    real_nonneg_le_mul_one_add_norm hP_nonneg t
  have hC :
      ‖C‖ ≤ K * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaCorrectionLogDerivative_leftAffineLine_linear_bound
      F t
  have hsum :
      ‖P‖ + ‖G‖ + ‖C‖ ≤
        ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) :=
    add_le_add (add_le_add hP hG) hC
  have hfactor :
      ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) =
        (‖P‖ + ‖(1 / 2 : ℂ)‖ * M + K) * (1 + ‖t‖) := by
    calc
      ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) =
        (‖P‖ + ‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) := by
          exact congrArg
            (fun x : ℝ => x + K * (1 + ‖t‖))
            (add_mul ‖P‖ (‖(1 / 2 : ℂ)‖ * M) (1 + ‖t‖)).symm
      _ = (‖P‖ + ‖(1 / 2 : ℂ)‖ * M + K) * (1 + ‖t‖) := by
          exact (add_mul (‖P‖ + ‖(1 / 2 : ℂ)‖ * M) K (1 + ‖t‖)).symm
  calc
    ‖-(P + G) - C‖ ≤ ‖-(P + G)‖ + ‖C‖ :=
      norm_sub_le (-(P + G)) C
    _ = ‖P + G‖ + ‖C‖ := by
      exact congrArg (fun x : ℝ => x + ‖C‖) (norm_neg (P + G))
    _ ≤ (‖P‖ + ‖G‖) + ‖C‖ := by
      have hpg : ‖P + G‖ ≤ ‖P‖ + ‖G‖ :=
        norm_add_le P G
      exact add_le_add_right hpg ‖C‖
    _ = ‖P‖ + ‖G‖ + ‖C‖ :=
      add_assoc ‖P‖ ‖G‖ ‖C‖
    _ ≤
        ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) :=
      hsum
    _ =
        (‖P‖ + ‖(1 / 2 : ℂ)‖ * M + K) * (1 + ‖t‖) :=
      hfactor

/-- The left finite-shift Binet remainder factor has linear growth on the
scheduled left affine half-line, provided the left line avoids Gamma poles. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderFactor_linear_bound
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ∀ t : ℝ,
      ‖-((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2))‖ ≤
        (‖(1 / 2 : ℂ)‖ *
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainderLinearConstant
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)) *
          (1 + ‖t‖) := by
  intro t
  let σ : ℝ := (1 - F.c) / 2
  let N : ℕ := zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F
  let C : ℝ :=
    Complex.GammaLogDerivativeFixedVerticalShiftNatRemainderLinearConstant σ N
  have hshift_pos : 0 < σ + (N : ℝ) :=
    Complex.GammaLogDerivativeFixedVerticalPositiveShiftNat_pos σ
  have hnot_pole :
      ∀ τ : ℝ, ∀ n : ℕ,
        (σ + τ * Complex.I : ℂ) ≠ -n :=
    zetaCompletedExplicitFormulaLeftFixedVertical_ne_Gamma_zero_locus_of_gammaRegular'
      F hregular
  have hR :
      ‖Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
          σ N (t / 2)‖ ≤
        C * (1 + ‖t / 2‖) :=
    Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder_linear_bound
      N hshift_pos hnot_pole (t / 2)
  have hC_nonneg : 0 ≤ C :=
    Complex.GammaLogDerivativeFixedVerticalShiftNatRemainderLinearConstant_nonneg
      σ N
  have hhalf_nonneg : 0 ≤ ‖(1 / 2 : ℂ)‖ :=
    norm_nonneg (1 / 2 : ℂ)
  have hweight :
      C * (1 + ‖t / 2‖) ≤ C * (1 + ‖t‖) :=
    mul_le_mul_of_nonneg_left
      (real_one_add_norm_div_two_le_one_add_norm t)
      hC_nonneg
  have hscaled :
      ‖(1 / 2 : ℂ)‖ *
          ‖Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            σ N (t / 2)‖ ≤
        ‖(1 / 2 : ℂ)‖ * (C * (1 + ‖t‖)) :=
    mul_le_mul_of_nonneg_left (hR.trans hweight) hhalf_nonneg
  calc
    ‖-((1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
          σ N (t / 2))‖ =
        ‖(1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            σ N (t / 2)‖ := by
      exact norm_neg
        ((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            σ N (t / 2))
    _ =
        ‖(1 / 2 : ℂ)‖ *
          ‖Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            σ N (t / 2)‖ := by
      exact norm_mul (1 / 2 : ℂ)
        (Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
          σ N (t / 2))
    _ ≤ ‖(1 / 2 : ℂ)‖ * (C * (1 + ‖t‖)) :=
      hscaled
    _ = (‖(1 / 2 : ℂ)‖ * C) * (1 + ‖t‖) := by
      exact (mul_assoc ‖(1 / 2 : ℂ)‖ C (1 + ‖t‖)).symm

/-- The right Binet remainder kernel has the standard affine integrable
majorant package. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel f F) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    -((1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalRemainder
        (F.c / 2) (t / 2))
  let B : ℝ :=
    ‖(1 / 2 : ℂ)‖ *
      |‖(2 : ℂ)‖ *
        ∫ u : ℝ in Set.Ioi (0 : ℝ),
          (1 / (F.c / 2) ^ 2) *
            (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))|
  have hB_nonneg : 0 ≤ B :=
    mul_nonneg
      (norm_nonneg (1 / 2 : ℂ))
      (abs_nonneg
        (‖(2 : ℂ)‖ *
          ∫ u : ℝ in Set.Ioi (0 : ℝ),
            (1 / (F.c / 2) ^ 2) *
              (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))))
  have hA_meas :
      AEStronglyMeasurable A (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderFactor_aestronglyMeasurable
      F
  have hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderFactor_linear_bound
      F
  exact
    zetaCompletedExplicitFormulaRightCenteredAffineProduct_majorantPackage_of_linear_factor_bound
      f F h A B hB_nonneg hA_meas hA_bound

/-- The left Binet remainder kernel has the standard affine integrable
majorant package, once the left line is known Gamma-regular. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel f F) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    -((1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
        ((1 - F.c) / 2)
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
        (t / 2))
  let B : ℝ :=
    ‖(1 / 2 : ℂ)‖ *
      Complex.GammaLogDerivativeFixedVerticalShiftNatRemainderLinearConstant
        ((1 - F.c) / 2)
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
  have hB_nonneg : 0 ≤ B :=
    mul_nonneg
      (norm_nonneg (1 / 2 : ℂ))
      (Complex.GammaLogDerivativeFixedVerticalShiftNatRemainderLinearConstant_nonneg
        ((1 - F.c) / 2)
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F))
  have hA_meas :
      AEStronglyMeasurable A (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderFactor_aestronglyMeasurable
      F
  have hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderFactor_linear_bound
      F hregular
  exact
    zetaCompletedExplicitFormulaLeftCenteredAffineProduct_majorantPackage_of_linear_factor_bound
      f F h A B hB_nonneg hA_meas hA_bound

/-- The left Binet main kernel has the standard affine integrable majorant
package, once the left line is Gamma-regular. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    -(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatMain
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2)) -
      explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaLeftAffineLine F t)
  let B : ℝ :=
    ‖zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm‖ +
      ‖(1 / 2 : ℂ)‖ *
        Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant
          ((1 - F.c) / 2)
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F) +
      ((1 : ℝ) / (-(1 - F.c)) +
        (1 : ℝ) / (-((1 - F.c) - 1)))
  let σ : ℝ := (1 - F.c) / 2
  let N : ℕ := zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F
  have hshift_pos : 0 < σ + (N : ℝ) :=
    Complex.GammaLogDerivativeFixedVerticalPositiveShiftNat_pos σ
  have hM_nonneg :
      0 ≤
        Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant
          σ N :=
    Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant_nonneg
      N hshift_pos
  have hzero_den_pos : 0 < -(1 - F.c) :=
    neg_pos.mpr F.one_sub_c_neg
  have hone_den_pos : 0 < -((1 - F.c) - 1) := by
    have hneg : (1 - F.c) - 1 < 0 := by
      calc
        (1 - F.c) - 1 < 0 - 1 := by
          exact sub_lt_sub_right F.one_sub_c_neg 1
        _ < 0 := by
          exact neg_lt_zero.mpr zero_lt_one
    exact neg_pos.mpr hneg
  have hB_nonneg : 0 ≤ B :=
    add_nonneg
      (add_nonneg
        (norm_nonneg zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm)
        (mul_nonneg (norm_nonneg (1 / 2 : ℂ)) hM_nonneg))
      (add_nonneg
        (div_nonneg zero_le_one hzero_den_pos.le)
        (div_nonneg zero_le_one hone_den_pos.le))
  have hA_meas :
      AEStronglyMeasurable A (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainFactor_aestronglyMeasurable
      F
  have hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainFactor_linear_bound
      F hregular
  exact
    zetaCompletedExplicitFormulaLeftCenteredAffineProduct_majorantPackage_of_linear_factor_bound
      f F h A B hB_nonneg hA_meas hA_bound

/-- Full-line integrability of the right Binet main kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_majorantPackage
    f F h).integrable

/-- Full-line integrability of the left Binet main kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_majorantPackage
    f F h hregular).integrable

/-- Restricted-window integrability of the right Binet main kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable_restrict_Icc
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (a b : ℝ) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F)
      (volume.restrict (Set.Icc a b)) :=
  (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable
    f F h).mono_measure Measure.restrict_le_self

/-- Restricted-window integrability of the left Binet main kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable_restrict_Icc
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (a b : ℝ) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F)
      (volume.restrict (Set.Icc a b)) :=
  (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable
    f F h hregular).mono_measure Measure.restrict_le_self

/-- Full-line integrability of the right Binet remainder kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_majorantPackage
    f F h).integrable

/-- Full-line integrability of the left Binet remainder kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_majorantPackage
    f F h hregular).integrable

/-- Restricted-window integrability of the right Binet remainder kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable_restrict_Icc
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (a b : ℝ) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel f F)
      (volume.restrict (Set.Icc a b)) :=
  (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable
    f F h).mono_measure Measure.restrict_le_self

/-- Restricted-window integrability of the left Binet remainder kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable_restrict_Icc
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (a b : ℝ) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel f F)
      (volume.restrict (Set.Icc a b)) :=
  (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable
    f F h hregular).mono_measure Measure.restrict_le_self

/-- Scheduled right Binet-main windows converge to the full-line Binet-main
integral. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_scheduledWindow_tendsto_integral
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t)) :=
  explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral_of_majorantPackage
    F.toContourFamily h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
      f F.toContourFamily)
    h.height_schedule.cofinal
    (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_majorantPackage
      f F.toContourFamily h)

/-- Scheduled left Binet-main windows converge to the full-line Binet-main
integral. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_scheduledWindow_tendsto_integral
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
      F.toContourFamily) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t)) :=
  explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral_of_majorantPackage
    F.toContourFamily h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
      f F.toContourFamily)
    h.height_schedule.cofinal
    (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_majorantPackage
      f F.toContourFamily h hregular)

/-- Scheduled right Binet-remainder windows converge to the full-line
Binet-remainder integral. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_tendsto_integral
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t)) :=
  explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral_of_majorantPackage
    F.toContourFamily h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
      f F.toContourFamily)
    h.height_schedule.cofinal
    (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_majorantPackage
      f F.toContourFamily h)

/-- Scheduled left Binet-remainder windows converge to the full-line
Binet-remainder integral. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_tendsto_integral
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
      F.toContourFamily) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t)) :=
  explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral_of_majorantPackage
    F.toContourFamily h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
      f F.toContourFamily)
    h.height_schedule.cofinal
    (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_majorantPackage
      f F.toContourFamily h hregular)

/-- Algebraic transport from a Gamma logarithmic-derivative Binet
decomposition to the half-weighted derivative appearing in `Gammaℝ'/Gammaℝ`. -/
theorem zetaCompletedExplicitFormula_halfGammaLogDeriv_binet_algebra
    (D G M R : ℂ) :
    D / G = M + R →
      (D * (1 / 2 : ℂ)) / G =
        (1 / 2 : ℂ) * M + (1 / 2 : ℂ) * R := by
  intro h
  calc
    (D * (1 / 2 : ℂ)) / G =
        (D / G) * (1 / 2 : ℂ) := by
      exact (mul_div_right_comm D (1 / 2 : ℂ) G).symm
    _ = (M + R) * (1 / 2 : ℂ) := by
      exact congrArg (fun z : ℂ => z * (1 / 2 : ℂ)) h
    _ = M * (1 / 2 : ℂ) + R * (1 / 2 : ℂ) := by
      exact add_mul M R (1 / 2 : ℂ)
    _ = (1 / 2 : ℂ) * M + (1 / 2 : ℂ) * R := by
      exact congrArg₂ HAdd.hAdd
        (mul_comm M (1 / 2 : ℂ))
        (mul_comm R (1 / 2 : ℂ))

/-- Additive algebra for the archimedean Binet split:
the inverse-Gamma sign and the elementary correction are assigned to the main
piece, while the differentiated Binet remainder keeps the inverse-Gamma sign. -/
theorem zetaCompletedExplicitFormula_archimedeanBinet_logDerivative_algebra
    (P M R C : ℂ) :
    -(P + (M + R)) - C =
      (-(P + M) - C) + -R := by
  have hassoc : P + (M + R) = (P + M) + R :=
    add_assoc P M R
  calc
    -(P + (M + R)) - C =
        -(P + (M + R)) + -C := by
      exact sub_eq_add_neg (-(P + (M + R))) C
    _ = -((P + M) + R) + -C := by
      exact congrArg (fun z : ℂ => -z + -C) hassoc
    _ = (-(P + M) + -R) + -C := by
      exact congrArg (fun z : ℂ => z + -C) (neg_add (P + M) R)
    _ = (-(P + M) + -C) + -R := by
      exact add_right_comm (-(P + M)) (-R) (-C)
    _ = (-(P + M) - C) + -R := by
      exact congrArg (fun z : ℂ => z + -R)
        (sub_eq_add_neg (-(P + M)) C).symm

/-- Pointwise Binet decomposition of the right archimedean affine-line kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_eq_binetMain_add_remainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) (t : ℝ) :
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t =
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F t +
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F t := by
  let s : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
  let w : ℂ := s / 2
  let σ : ℝ := F.c / 2
  let τ : ℝ := t / 2
  let P : ℂ := zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm
  let M : ℂ := (1 / 2 : ℂ) *
    Complex.GammaLogDerivativeFixedVerticalMain σ τ
  let R : ℂ := (1 / 2 : ℂ) *
    Complex.GammaLogDerivativeFixedVerticalRemainder σ τ
  let C : ℂ := explicitFormulaCorrectionLogDerivative s
  let Φ : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
  have hσ_pos : 0 < σ := by
    exact div_pos F.c_pos zero_lt_two
  have hline : w = (σ + τ * Complex.I : ℂ) := by
    exact zetaCompletedExplicitFormulaRightAffineLine_div_two_eq_fixedVertical
      F t
  have hgamma_fixed :
      deriv Complex.Gamma w / Complex.Gamma w =
        Complex.GammaLogDerivativeFixedVerticalMain σ τ +
          Complex.GammaLogDerivativeFixedVerticalRemainder σ τ := by
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          deriv Complex.Gamma z / Complex.Gamma z =
            Complex.GammaLogDerivativeFixedVerticalMain σ τ +
              Complex.GammaLogDerivativeFixedVerticalRemainder σ τ)
        hline.symm
        (Complex.Gamma_logDerivative_fixedRealPartLine_eq_main_add_remainder
          hcoh hσ_pos τ)
  have hhalf :
      (deriv Complex.Gamma w * (1 / 2 : ℂ)) / Complex.Gamma w =
        M + R := by
    exact
      zetaCompletedExplicitFormula_halfGammaLogDeriv_binet_algebra
        (deriv Complex.Gamma w)
        (Complex.Gamma w)
        (Complex.GammaLogDerivativeFixedVerticalMain σ τ)
        (Complex.GammaLogDerivativeFixedVerticalRemainder σ τ)
        hgamma_fixed
  have hgammaR :
      deriv Gammaℝ s / Gammaℝ s = P + (M + R) := by
    have hraw :
        deriv Gammaℝ s / Gammaℝ s =
          P + (deriv Complex.Gamma w * (1 / 2 : ℂ)) /
            Complex.Gamma w :=
      zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_logDeriv_eq F t
    calc
      deriv Gammaℝ s / Gammaℝ s =
          P + (deriv Complex.Gamma w * (1 / 2 : ℂ)) /
            Complex.Gamma w := hraw
      _ = P + (M + R) := by
        exact congrArg (fun z : ℂ => P + z) hhalf
  have hinverse :
      inverseGammaCompletionLogDeriv s = -(P + (M + R)) := by
    have hraw :
        inverseGammaCompletionLogDeriv s =
          -deriv Gammaℝ s / Gammaℝ s :=
      zetaCompletedExplicitFormulaInverseGammaLogDeriv_rightAffineLine_eq_neg_Gammaℝ_logDeriv
        F t
    calc
      inverseGammaCompletionLogDeriv s =
          -deriv Gammaℝ s / Gammaℝ s := hraw
      _ = -(deriv Gammaℝ s / Gammaℝ s) := by
        exact neg_div (Gammaℝ s) (deriv Gammaℝ s)
      _ = -(P + (M + R)) := by
        exact congrArg Neg.neg hgammaR
  have hlog :
      explicitFormulaArchimedeanLogDerivative s =
        (-(P + M) - C) + -R := by
    calc
      explicitFormulaArchimedeanLogDerivative s =
          inverseGammaCompletionLogDeriv s - C := by
        rfl
      _ = -(P + (M + R)) - C := by
        exact congrArg (fun z : ℂ => z - C) hinverse
      _ = (-(P + M) - C) + -R := by
        exact
          zetaCompletedExplicitFormula_archimedeanBinet_logDerivative_algebra
            P M R C
  calc
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t =
        explicitFormulaArchimedeanLogDerivative s * Φ := by
      rfl
    _ = ((-(P + M) - C) + -R) * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hlog
    _ = (-(P + M) - C) * Φ + (-R) * Φ := by
      exact add_mul (-(P + M) - C) (-R) Φ
    _ =
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F t +
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F t := by
      rfl

/-- Pointwise Binet decomposition of the left archimedean affine-line kernel.

The left half-line can have negative real part, so this theorem uses the
finite-shift Gamma/Binet decomposition rather than the positive-line Binet
formula directly. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_eq_binetMain_add_remainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) (t : ℝ) :
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t =
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F t +
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F t := by
  let s : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  let w : ℂ := s / 2
  let σ : ℝ := (1 - F.c) / 2
  let τ : ℝ := t / 2
  let N : ℕ := zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F
  let P : ℂ := zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm
  let M : ℂ := (1 / 2 : ℂ) *
    Complex.GammaLogDerivativeFixedVerticalShiftNatMain σ N τ
  let R : ℂ := (1 / 2 : ℂ) *
    Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder σ N τ
  let C : ℂ := explicitFormulaCorrectionLogDerivative s
  let Φ : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  have hline : w = (σ + τ * Complex.I : ℂ) := by
    exact zetaCompletedExplicitFormulaLeftAffineLine_div_two_eq_fixedVertical
      F t
  have hσ_shift_pos : 0 < σ + (N : ℝ) := by
    exact
      Complex.GammaLogDerivativeFixedVerticalPositiveShiftNat_pos
        ((1 - F.c) / 2)
  have hnot_pole :
      ∀ u : ℝ, ∀ n : ℕ,
        (σ + u * Complex.I : ℂ) ≠ -n := by
    intro u n
    exact
      zetaCompletedExplicitFormulaLeftFixedVertical_ne_Gamma_zero_locus_of_gammaRegular'
        F hregular u n
  have hgamma_fixed :
      deriv Complex.Gamma w / Complex.Gamma w =
        Complex.GammaLogDerivativeFixedVerticalShiftNatMain σ N τ +
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder σ N τ := by
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          deriv Complex.Gamma z / Complex.Gamma z =
            Complex.GammaLogDerivativeFixedVerticalShiftNatMain σ N τ +
              Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder σ N τ)
        hline.symm
        (Complex.Gamma_logDerivative_fixedRealPartLine_eq_shiftNat_main_add_remainder
          hcoh N hσ_shift_pos hnot_pole τ)
  have hhalf :
      (deriv Complex.Gamma w * (1 / 2 : ℂ)) / Complex.Gamma w =
        M + R := by
    exact
      zetaCompletedExplicitFormula_halfGammaLogDeriv_binet_algebra
        (deriv Complex.Gamma w)
        (Complex.Gamma w)
        (Complex.GammaLogDerivativeFixedVerticalShiftNatMain σ N τ)
        (Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder σ N τ)
        hgamma_fixed
  have hgammaR :
      deriv Gammaℝ s / Gammaℝ s = P + (M + R) := by
    have hraw :
        deriv Gammaℝ s / Gammaℝ s =
          P + (deriv Complex.Gamma w * (1 / 2 : ℂ)) /
            Complex.Gamma w :=
      zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_logDeriv_eq_of_gammaRegular
        F hregular t
    calc
      deriv Gammaℝ s / Gammaℝ s =
          P + (deriv Complex.Gamma w * (1 / 2 : ℂ)) /
            Complex.Gamma w := hraw
      _ = P + (M + R) := by
        exact congrArg (fun z : ℂ => P + z) hhalf
  have hinverse :
      inverseGammaCompletionLogDeriv s = -(P + (M + R)) := by
    have hraw :
        inverseGammaCompletionLogDeriv s =
          -deriv Gammaℝ s / Gammaℝ s :=
      zetaCompletedExplicitFormulaInverseGammaLogDeriv_leftAffineLine_eq_neg_Gammaℝ_logDeriv_of_gammaRegular
        F hregular t
    calc
      inverseGammaCompletionLogDeriv s =
          -deriv Gammaℝ s / Gammaℝ s := hraw
      _ = -(deriv Gammaℝ s / Gammaℝ s) := by
        exact neg_div (Gammaℝ s) (deriv Gammaℝ s)
      _ = -(P + (M + R)) := by
        exact congrArg Neg.neg hgammaR
  have hlog :
      explicitFormulaArchimedeanLogDerivative s =
        (-(P + M) - C) + -R := by
    calc
      explicitFormulaArchimedeanLogDerivative s =
          inverseGammaCompletionLogDeriv s - C := by
        rfl
      _ = -(P + (M + R)) - C := by
        exact congrArg (fun z : ℂ => z - C) hinverse
      _ = (-(P + M) - C) + -R := by
        exact
          zetaCompletedExplicitFormula_archimedeanBinet_logDerivative_algebra
            P M R C
  calc
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t =
        explicitFormulaArchimedeanLogDerivative s * Φ := by
      rfl
    _ = ((-(P + M) - C) + -R) * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hlog
    _ = (-(P + M) - C) * Φ + (-R) * Φ := by
      exact add_mul (-(P + M) - C) (-R) Φ
    _ =
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F t +
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F t := by
      rfl

/-- Additive assembly for a scheduled Gamma/Binet line value.

This lemma contains no analytic estimate: it only turns a pointwise
main-plus-remainder decomposition, a scheduled main-term limit, and a scheduled
remainder decay theorem into the scheduled limit for the original affine-line
kernel. -/
theorem zetaCompletedExplicitFormula_scheduledWindow_tendsto_of_binetMain_add_remainder
    (F : ExplicitFormulaContourFamily)
    (height : ℝ → ℝ)
    (K M R : ℝ → ℂ)
    (value : ℂ)
    (hdecomp : ∀ t : ℝ, K t = M t + R t)
    (hM_integrable :
      ∀ u : ℝ,
        Integrable M
          (volume.restrict
            (Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T)))
    (hR_integrable :
      ∀ u : ℝ,
        Integrable R
          (volume.restrict
            (Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T)))
    (hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T,
            M t)
        atTop
        (𝓝 value))
    (hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T,
            R t)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (height u)).T)
            (F.rectangle (height u)).T,
          K t)
      atTop
      (𝓝 value) := by
  let A : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (height u)).T)
        (F.rectangle (height u)).T,
      K t
  let B : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (height u)).T)
        (F.rectangle (height u)).T,
      M t
  let C : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (height u)).T)
        (F.rectangle (height u)).T,
      R t
  have hsum :
      Tendsto (fun u : ℝ => B u + C u) atTop (𝓝 (value + 0)) :=
    hmain.add hremainder
  have hvalue : value + 0 = value :=
    add_zero value
  have hsum_value :
      Tendsto (fun u : ℝ => B u + C u) atTop (𝓝 value) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => B u + C u) atTop (𝓝 z))
      hvalue
      hsum
  have hwindow :
      ∀ u : ℝ, A u = B u + C u := by
    intro u
    have hpoint :
        (fun t : ℝ => K t) = fun t : ℝ => M t + R t := by
      funext t
      exact hdecomp t
    have hintegral :
        A u =
          ∫ t in Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T,
            M t + R t := by
      exact congrArg
        (fun φ : ℝ → ℂ =>
          ∫ t in Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T,
            φ t)
        hpoint
    have hsplit :
        (∫ t in Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T,
            M t + R t) =
          B u + C u := by
      exact
        integral_add
          (μ := volume.restrict
            (Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T))
          (hM_integrable u)
          (hR_integrable u)
    exact Eq.trans hintegral hsplit
  have hfun :
      A = fun u : ℝ => B u + C u := by
    funext u
    exact hwindow u
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 value))
      hfun.symm
      hsum_value

/-- Scheduled right archimedean line value from the right Binet main/remainder
inputs.  This theorem is pure assembly: all analytic estimates are explicit
arguments. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_binetMain_remainder
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hmain_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)))
    (hremainder_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)))
    (hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
    (hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) :=
  zetaCompletedExplicitFormula_scheduledWindow_tendsto_of_binetMain_add_remainder
    F.toContourFamily
    h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
      f F.toContourFamily)
    (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
      f F.toContourFamily)
    (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
      f F.toContourFamily)
    (zetaCompletedExplicitFormulaPhi f 0)
    (fun t : ℝ =>
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_eq_binetMain_add_remainder
        f F.toContourFamily hcoh t)
    hmain_integrable
    hremainder_integrable
    hmain
    hremainder

/-- Scheduled left archimedean line value from the finite-shift left Binet
main/remainder inputs.  This theorem is pure assembly; the only left-line
regularity used here is for the pointwise Binet decomposition. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_binetMain_remainder
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hmain_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)))
    (hremainder_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)))
    (hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))))
    (hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  exact
    zetaCompletedExplicitFormula_scheduledWindow_tendsto_of_binetMain_add_remainder
      F.toContourFamily
      h.height_schedule.height
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily)
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily)
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
        f F.toContourFamily)
      (-(zetaCompletedExplicitFormulaPhi f 0))
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_eq_binetMain_add_remainder
          f F.toContourFamily hregular hcoh t)
      hmain_integrable
      hremainder_integrable
      hmain
      hremainder

/-- Scheduled right archimedean Gamma/Binet line value from full-line Binet
main and remainder value identities.

This theorem isolates the remaining analytic content to two whole-line
identities: the Binet main integral evaluates to `Φ_f(0)` and the Binet
remainder integral vanishes. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_fullLineBinetValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hmain_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0)
    (hremainder_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t) =
        0) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) := by
  have hmain_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) := by
    intro u
    exact
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable_restrict_Icc
        f F.toContourFamily h
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
  have hremainder_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) := by
    intro u
    exact
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable_restrict_Icc
        f F.toContourFamily h
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
  have hmain_integral :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_scheduledWindow_tendsto_integral
      f F h
  have hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
                f F.toContourFamily t)
          atTop
          (𝓝 z))
      hmain_value
      hmain_integral
  have hremainder_integral :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h
  have hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
                f F.toContourFamily t)
          atTop
          (𝓝 z))
      hremainder_value
      hremainder_integral
  exact
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_binetMain_remainder
      f F h hcoh hmain_integrable hremainder_integrable hmain hremainder

/-- Scheduled left archimedean Gamma/Binet line value from full-line Binet
main and remainder value identities. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_fullLineBinetValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hmain_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0))
    (hremainder_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t) =
        0) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hmain_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) := by
    intro u
    exact
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable_restrict_Icc
        f F.toContourFamily h hregular
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
  have hremainder_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) := by
    intro u
    exact
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable_restrict_Icc
        f F.toContourFamily h hregular
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
  have hmain_integral :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_scheduledWindow_tendsto_integral
      f F h hregular
  have hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
                f F.toContourFamily t)
          atTop
          (𝓝 z))
      hmain_value
      hmain_integral
  have hremainder_integral :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h hregular
  have hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
                f F.toContourFamily t)
          atTop
          (𝓝 z))
      hremainder_value
      hremainder_integral
  exact
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_binetMain_remainder
      f F h hcoh hmain_integrable hremainder_integrable hmain hremainder

/-- Integrability of the right archimedean affine kernel from its Gamma/Binet
main-plus-remainder decomposition. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integrable_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) := by
  have hmain :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable
      f F.toContourFamily h
  have hremainder :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable
      f F.toContourFamily h
  have hsum :
      Integrable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        (volume : Measure ℝ) :=
    hmain.add hremainder
  have hpoint :
      (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_eq_binetMain_add_remainder
          f F.toContourFamily hcoh t)
  exact hsum.congr hpoint.symm

/-- Integrability of the left archimedean affine kernel from its Gamma/Binet
main-plus-remainder decomposition. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integrable_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hmain :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable
      f F.toContourFamily h hregular
  have hremainder :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable
      f F.toContourFamily h hregular
  have hsum :
      Integrable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        (volume : Measure ℝ) :=
    hmain.add hremainder
  have hpoint :
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_eq_binetMain_add_remainder
          f F.toContourFamily hregular hcoh t)
  exact hsum.congr hpoint.symm

/-- Scheduled right archimedean line exhaustion to its whole-line affine
integral. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_integral_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t)) :=
  explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
    F.toContourFamily
    h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
      f F.toContourFamily)
    h.height_schedule.cofinal
    (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integrable_ownerGammaBinetLineValue
      f F h hcoh)

/-- Scheduled left archimedean line exhaustion to its whole-line affine
integral. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_integral_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t)) :=
  explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
    F.toContourFamily
    h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
      f F.toContourFamily)
    h.height_schedule.cofinal
    (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integrable_ownerGammaBinetLineValue
      f F h hcoh)

/-- Scheduled right archimedean line value from the whole-line affine value. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_fullLineAffineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) :=
  Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 z))
    hvalue
    (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_integral_ownerGammaBinetLineValue
      f F h hcoh)

/-- Scheduled left archimedean line value from the whole-line affine value. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_fullLineAffineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) :=
  Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 z))
    hvalue
    (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_integral_ownerGammaBinetLineValue
      f F h hcoh)

/-- Integrability of the right elementary correction affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightAffineKernel_integrable_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F)
      (volume : Measure ℝ) := by
  have hzero :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrable_ownerBounds
      f F h
  have hone :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integrable_ownerBounds
      f F h
  have hsum :
      Integrable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
            f F t +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
              f F t)
        (volume : Measure ℝ) :=
    hzero.add hone
  have hpoint :
      (zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
            f F t +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
              f F t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaCorrectionRightAffineKernel_eq_zeroPole_add_onePole
          f F t)
  exact hsum.congr hpoint.symm

/-- Integrability of the left elementary correction affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftAffineKernel_integrable_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F)
      (volume : Measure ℝ) := by
  have hzero :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integrable_ownerBounds
      f F h
  have hone :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integrable_ownerBounds
      f F h
  have hsum :
      Integrable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
            f F t +
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
              f F t)
        (volume : Measure ℝ) :=
    hzero.add hone
  have hpoint :
      (zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
            f F t +
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
              f F t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaCorrectionLeftAffineKernel_eq_zeroPole_add_onePole
          f F t)
  exact hsum.congr hpoint.symm

/-- Right archimedean affine whole-line value from the four Gamma/Binet
full-line value identities.

This is pure conditional assembly from component values.  It should only be
used when the separate Binet component values have actually been proved; the
unconditional owner route evaluates the full affine value without assuming a
separate remainder vanishing theorem. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_of_fullLineBinetValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hmain_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0)
    (hremainder_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t) =
        0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 := by
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t)
      (zetaCompletedExplicitFormulaPhi f 0)
      (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_integral_ownerGammaBinetLineValue
        f F h hcoh)
      (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_fullLineBinetValues
        f F h hcoh hmain_value hremainder_value)

/-- Left archimedean affine whole-line value from the four Gamma/Binet
full-line value identities.

This is pure conditional assembly from component values.  It should only be
used when the separate shifted Binet component values have actually been
proved; the unconditional owner route evaluates the full affine value without
assuming a separate shifted remainder vanishing theorem. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_of_fullLineBinetValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hmain_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0))
    (hremainder_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t) =
        0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t)
      (-(zetaCompletedExplicitFormulaPhi f 0))
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_integral_ownerGammaBinetLineValue
        f F h hcoh)
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_fullLineBinetValues
        f F h hcoh hmain_value hremainder_value)

/-- Whole-line right affine Gamma/Binet integral decomposes as the sum of the
main and differentiated-remainder whole-line integrals.

This is only measure-theoretic assembly from the pointwise Binet split.  It
does not assert that either component has a separate closed form. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_binetMain_add_remainder_integrals
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t := by
  have hmain :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable
      f F.toContourFamily h
  have hremainder :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable
      f F.toContourFamily h
  have hsum :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t +
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t :=
    integral_add hmain hremainder
  have hpoint :
      (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_eq_binetMain_add_remainder
          f F.toContourFamily hcoh t)
  exact Eq.trans (integral_congr_ae hpoint) hsum

/-- Whole-line left affine Gamma/Binet integral decomposes as the sum of the
shifted main and differentiated-remainder whole-line integrals.

This is only measure-theoretic assembly from the pointwise shifted-Binet split.
It does not assert that either component has a separate closed form. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_binetMain_add_remainder_integrals
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hmain :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable
      f F.toContourFamily h hregular
  have hremainder :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable
      f F.toContourFamily h hregular
  have hsum :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t +
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t :=
    integral_add hmain hremainder
  have hpoint :
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_eq_binetMain_add_remainder
              f F.toContourFamily hregular hcoh t)
  exact Eq.trans (integral_congr_ae hpoint) hsum

/-- Coupled right Gamma/Binet full-transform value from an independently
proved whole-line right affine value.

This is only decomposition transport.  It is useful if the affine value is
proved directly from a Binet inversion theorem; it must not be used with the
owner theorem below, which itself consumes the coupled Binet full-transform
value. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_affineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (haffine :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0 := by
  have hdecomp :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_binetMain_add_remainder_integrals
      f F h hcoh
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t := by
      exact hdecomp.symm
    _ = zetaCompletedExplicitFormulaPhi f 0 := by
      exact haffine

/-- Coupled shifted-left Gamma/Binet full-transform value from an
independently proved whole-line left affine value.

This is the left analogue of
`zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_affineValue`;
it only transports across the pointwise Binet decomposition. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_of_affineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (haffine :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  have hdecomp :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_binetMain_add_remainder_integrals
      f F h hcoh
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t := by
      exact hdecomp.symm
    _ = -(zetaCompletedExplicitFormulaPhi f 0) := by
      exact haffine

/-- Whole-line right coupled Gamma/Binet full-transform value from the
corresponding scheduled full-transform value.

This theorem removes only the exhaustion bookkeeping from the analytic leaf:
the remaining input is the scheduled fixed-vertical Gamma/Binet transform
identity itself. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_scheduledFullTransform
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0 := by
  let S : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
        f F.toContourFamily t
  let I : ℂ :=
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t
  have hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_scheduledWindow_tendsto_integral
      f F h
  have hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h
  have hsum : Tendsto S atTop (𝓝 I) :=
    hmain.add hremainder
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      S I (zetaCompletedExplicitFormulaPhi f 0) hsum hscheduled

/-- Whole-line shifted-left coupled Gamma/Binet full-transform value from the
corresponding scheduled full-transform value. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_of_scheduledFullTransform
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
      F.toContourFamily)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  let S : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
        f F.toContourFamily t
  let I : ℂ :=
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t
  have hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_scheduledWindow_tendsto_integral
      f F h hregular
  have hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h hregular
  have hsum : Tendsto S atTop (𝓝 I) :=
    hmain.add hremainder
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      S I (-(zetaCompletedExplicitFormulaPhi f 0)) hsum hscheduled

/-- Scheduled full right Binet transform value from the coupled whole-line
Binet value.

This is only exhaustion transport: the analytic content is the whole-line
coupled Gamma/Binet value supplied as `hvalue`. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_scheduledWindow_tendsto_phiZero_of_integral_eq
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t =
        zetaCompletedExplicitFormulaPhi f 0) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) := by
  let S : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
        f F.toContourFamily t
  let I : ℂ :=
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t
  have hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_scheduledWindow_tendsto_integral
      f F h
  have hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h
  have hsum : Tendsto S atTop (𝓝 I) :=
    hmain.add hremainder
  exact
    Eq.subst
      (motive := fun z : ℂ => Tendsto S atTop (𝓝 z))
      hvalue
      hsum

/-- Scheduled full shifted-left Binet transform value from the coupled
whole-line shifted-left Binet value.

This is only exhaustion transport: the analytic content is the whole-line
coupled shifted-left Gamma/Binet value supplied as `hvalue`. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_scheduledWindow_tendsto_neg_phiZero_of_integral_eq
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
      F.toContourFamily)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  let S : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
        f F.toContourFamily t
  let I : ℂ :=
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t
  have hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_scheduledWindow_tendsto_integral
      f F h hregular
  have hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h hregular
  have hsum : Tendsto S atTop (𝓝 I) :=
    hmain.add hremainder
  exact
    Eq.subst
      (motive := fun z : ℂ => Tendsto S atTop (𝓝 z))
      hvalue
      hsum

/-- Right Gamma/Binet source value from the named coupled whole-line transform
value.

This is only definitional transport from the named owner integral to the long
main-plus-remainder expression used by downstream wrappers. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_namedIntegralValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hvalue :
      zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral
          f F.toContourFamily =
        zetaCompletedExplicitFormulaPhi f 0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0 := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral_eq
        f F.toContourFamily).symm
      hvalue

/-- Shifted-left Gamma/Binet source value from the named coupled whole-line
transform value.

This is only definitional transport from the named owner integral to the long
shifted main-plus-remainder expression used by downstream wrappers. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_of_namedIntegralValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hvalue :
      zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral
          f F.toContourFamily =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral_eq
        f F.toContourFamily).symm
      hvalue

/-- Owner analytic leaf: whole-line full right Binet transform value.

This is the true Gamma/Binet value theorem.  It should be proved directly from
the fixed-vertical Binet transform against `Phi_f`, not from scheduled
exhaustion or downstream inverse-Gamma wrappers. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_sourceGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0 := by
  have hvalue :
      zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral
          f F.toContourFamily =
        zetaCompletedExplicitFormulaPhi f 0 := by
    have hmain_value :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) =
          zetaCompletedExplicitFormulaPhi f 0 :=
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integral_eq_phiZero
        f F h hcoh
    have hremainder_value :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t) =
          0 :=
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integral_eq_zero
        f F h hcoh
    have h_affine_eq :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t) =
          zetaCompletedExplicitFormulaPhi f 0 :=
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_of_fullLineBinetValues
        f F h hcoh hmain_value hremainder_value
    have h_decomp :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t) =
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
                f F.toContourFamily t :=
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_binetMain_add_remainder_integrals
        f F h hcoh
    calc zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral
          f F.toContourFamily
        = (∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
              ∫ t : ℝ,
                zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
                  f F.toContourFamily t := by rfl
        _ = ∫ t : ℝ,
              zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
                f F.toContourFamily t := by exact h_decomp.symm
        _ = zetaCompletedExplicitFormulaPhi f 0 := h_affine_eq
  exact
    zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_namedIntegralValue
      f F hvalue

/-- Owner analytic leaf: whole-line full shifted-left Binet transform value.

This is the true shifted-left Gamma/Binet value theorem.  It should be proved
directly from the fixed-vertical shifted Binet transform against `Phi_f`, not
from scheduled exhaustion or downstream inverse-Gamma wrappers. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_sourceGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  have hvalue :
      zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral
          f F.toContourFamily =
        -(zetaCompletedExplicitFormulaPhi f 0) := by
    have hmain_value :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) =
          -(zetaCompletedExplicitFormulaPhi f 0) :=
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integral_eq_neg_phiZero
        f F h hcoh
    have hremainder_value :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t) =
          0 :=
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integral_eq_zero
        f F h hcoh
    have h_affine_eq :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t) =
          -(zetaCompletedExplicitFormulaPhi f 0) :=
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_of_fullLineBinetValues
        f F h hcoh hmain_value hremainder_value
    have h_decomp :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t) =
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
                f F.toContourFamily t :=
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_binetMain_add_remainder_integrals
        f F h hcoh
    calc zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral
          f F.toContourFamily
        = (∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
              ∫ t : ℝ,
                zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
                  f F.toContourFamily t := by rfl
        _ = ∫ t : ℝ,
              zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
                f F.toContourFamily t := by exact h_decomp.symm
        _ = -(zetaCompletedExplicitFormulaPhi f 0) := h_affine_eq
  exact
    zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_of_namedIntegralValue
      f F hvalue

/-- Owner scheduled wrapper: scheduled full right Binet transform value. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_scheduledWindow_tendsto_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_scheduledWindow_tendsto_phiZero_of_integral_eq
      f F h
      (zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_sourceGammaBinetLineCore
        f F h hcoh)

/-- Owner scheduled wrapper: scheduled full shifted-left Binet transform value. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_scheduledWindow_tendsto_neg_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  exact
    zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_scheduledWindow_tendsto_neg_phiZero_of_integral_eq
      f F h hregular
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_sourceGammaBinetLineCore
        f F h hcoh)

/-- Scheduled right affine Gamma/Binet value from the scheduled coupled
Gamma/Binet full-transform value.

This is only window-level transport across the pointwise Binet decomposition.
It is deliberately oriented from the scheduled full-transform owner leaf to
the affine line value, not conversely. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_scheduledFullTransform
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) := by
  let A : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t
  let S : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
        f F.toContourFamily t
  have hA_eq_S : A = S := by
    funext u
    have hmain :
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) :=
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable_restrict_Icc
        f F.toContourFamily h
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
    have hremainder :
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) :=
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable_restrict_Icc
        f F.toContourFamily h
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
    have hpoint :
        (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily) =ᵐ[
            volume.restrict
              (Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)]
          fun t : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t :=
      Filter.Eventually.of_forall
        (fun t =>
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_eq_binetMain_add_remainder
            f F.toContourFamily hcoh t)
    calc
      A u =
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t := by
        exact integral_congr_ae hpoint
      _ = S u := by
        exact integral_add hmain hremainder
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
      hA_eq_S.symm
      hscheduled

/-- Scheduled shifted-left affine Gamma/Binet value from the scheduled
coupled shifted-left Gamma/Binet full-transform value. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_scheduledFullTransform
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  let A : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t
  let S : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
        f F.toContourFamily t
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hA_eq_S : A = S := by
    funext u
    have hmain :
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) :=
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable_restrict_Icc
        f F.toContourFamily h hregular
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
    have hremainder :
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) :=
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable_restrict_Icc
        f F.toContourFamily h hregular
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
    have hpoint :
        (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily) =ᵐ[
            volume.restrict
              (Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)]
          fun t : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t :=
      Filter.Eventually.of_forall
        (fun t =>
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_eq_binetMain_add_remainder
            f F.toContourFamily hregular hcoh t)
    calc
      A u =
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t := by
        exact integral_congr_ae hpoint
      _ = S u := by
        exact integral_add hmain hremainder
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))))
      hA_eq_S.symm
      hscheduled

/-- Whole-line full right Binet transform value.

This is now an exhaustion wrapper over the scheduled full-transform owner
leaf.  It keeps the main and differentiated-remainder terms coupled; it does
not assert a separate vanishing theorem for the differentiated Binet
remainder. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0 := by
  exact
    zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_sourceGammaBinetLineCore
      f F h hcoh

/-- Whole-line full shifted-left Binet transform value.

As on the right side, this is now an exhaustion wrapper over the scheduled
full-transform owner leaf.  The finite Gamma-recurrence shift remains part of
the coupled scheduled value theorem, not a downstream algebraic correction. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_sourceGammaBinetLineCore
      f F h hcoh

/-- Whole-line value of the right Gamma/Binet archimedean affine line.

This is an algebraic wrapper over the coupled Binet full-transform value and
the pointwise Binet decomposition of the affine kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 := by
  have hdecomp :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_binetMain_add_remainder_integrals
      f F h hcoh
  have hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t =
        zetaCompletedExplicitFormulaPhi f 0 :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_ownerGammaBinetLineCore
      f F h hcoh
  exact Eq.trans hdecomp hvalue

/-- Whole-line value of the shifted-left Gamma/Binet archimedean affine line.

This is the shifted-left wrapper over the coupled Binet full-transform value
and the pointwise shifted-Binet decomposition of the affine kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  have hdecomp :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_binetMain_add_remainder_integrals
      f F h hcoh
  have hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t =
        -(zetaCompletedExplicitFormulaPhi f 0) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_ownerGammaBinetLineCore
      f F h hcoh
  exact Eq.trans hdecomp hvalue

/-- The right coupled Gamma/Binet full-transform source value is equivalent to
the whole-line right archimedean affine value.

This is only a bookkeeping equivalence across the pointwise Binet
decomposition.  It is useful for audits: an independent affine proof can close
the Gamma/Binet source leaf, but a proof routed through inverse-Gamma
one-sided values is cyclic because those one-sided values already consume this
owner theorem. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_iff_affineKernel_integral_eq_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0) ↔
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 := by
  constructor
  · intro hbinet
    have hdecomp :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t) =
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
                f F.toContourFamily t :=
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_binetMain_add_remainder_integrals
        f F h hcoh
    exact Eq.trans hdecomp hbinet
  · intro haffine
    exact
      zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_affineValue
        f F h hcoh haffine

/-- The shifted-left coupled Gamma/Binet full-transform source value is
equivalent to the whole-line left archimedean affine value. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_iff_affineKernel_integral_eq_neg_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0)) ↔
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  constructor
  · intro hbinet
    have hdecomp :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t) =
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
                f F.toContourFamily t :=
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_binetMain_add_remainder_integrals
        f F h hcoh
    exact Eq.trans hdecomp hbinet
  · intro haffine
    exact
      zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_of_affineValue
        f F h hcoh haffine

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
