import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffinePhiDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineCenteredProductMajorants
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineKernelMajorantPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaFactorBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftKernelReflection

/-!
# Reflected-left completed-log-derivative single-term kernel algebra

This file owns the definitional algebra for the reflected right-line
Dirichlet terms that occur in the left reflected completed kernel.  It is the
left/reflected analogue of `PrimeRightTermKernelAlgebra`; it deliberately does
not contain a Fourier value theorem or a sum-integral exchange theorem.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction

namespace ZetaAdmissibleFunction

/-- The single reflected Dirichlet term kernel carried by the left reflected
completed-log-derivative line.

The minus sign is the one in
`zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel`, namely
the kernel uses `- completedZetaNegLogDeriv (rightLine (-t))`. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) (t : ℝ) : ℂ :=
  (-(LSeries.term (↗Λ)
      (zetaCompletedExplicitFormulaRightAffineLine F (-t)) n)) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- The inverse-Gamma part left over after expanding the reflected completed
logarithmic derivative into right-line von Mangoldt terms.

This kernel is not the ordinary left inverse-Gamma affine kernel.  Its
right-line argument and left-centered test transform are forced by the
reflected completed kernel. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (-(inverseGammaCompletionLogDeriv
      (zetaCompletedExplicitFormulaRightAffineLine F (-t)))) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- The reflected archimedean part of the inverse-Gamma remainder in the
left reflected completed prime kernel. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (-(explicitFormulaArchimedeanLogDerivative
      (zetaCompletedExplicitFormulaRightAffineLine F (-t)))) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- The reflected rational correction part of the inverse-Gamma remainder in
the left reflected completed prime kernel. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (-(explicitFormulaCorrectionLogDerivative
      (zetaCompletedExplicitFormulaRightAffineLine F (-t)))) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- The reflected single-term kernel unfolds to the reflected right-line
Dirichlet term times the left-centered test-transform factor. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t =
      (-(LSeries.term (↗Λ)
        (zetaCompletedExplicitFormulaRightAffineLine F (-t)) n)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) :=
  rfl

/-- The reflected inverse-Gamma kernel unfolds to the right-line
inverse-Gamma logarithmic derivative against the left-centered test transform. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel f F t =
      (-(inverseGammaCompletionLogDeriv
        (zetaCompletedExplicitFormulaRightAffineLine F (-t)))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) :=
  rfl

/-- The reflected archimedean kernel unfolds to the right-line archimedean
logarithmic derivative against the left-centered test transform. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel f F t =
      (-(explicitFormulaArchimedeanLogDerivative
        (zetaCompletedExplicitFormulaRightAffineLine F (-t)))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) :=
  rfl

/-- The reflected correction kernel unfolds to the right-line rational
correction logarithmic derivative against the left-centered test transform. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel f F t =
      (-(explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaRightAffineLine F (-t)))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) :=
  rfl

/-- Pointwise reflected inverse-Gamma remainder split into the archimedean
logarithmic derivative and the rational correction. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_add_correction_eq_inverseGamma
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel f F t +
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel f F t =
      zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        f F t := by
  let s : ℂ := zetaCompletedExplicitFormulaRightAffineLine F (-t)
  let Φ : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  let A : ℂ := explicitFormulaArchimedeanLogDerivative s
  let C : ℂ := explicitFormulaCorrectionLogDerivative s
  let G : ℂ := inverseGammaCompletionLogDeriv s
  have hA : A = G - C :=
    explicitFormulaArchimedeanLogDerivative_eq_inverseGammaCorrection_sub_poleCorrection
      s
  have hsum : A + C = G := by
    calc
      A + C = (G - C) + C := by
        exact congrArg (fun z : ℂ => z + C) hA
      _ = G := by
        exact sub_add_cancel G C
  have hneg_sum_mul :
      (-A) * Φ + (-C) * Φ = (-(A + C)) * Φ := by
    calc
      (-A) * Φ + (-C) * Φ = ((-A) + (-C)) * Φ := by
        exact (add_mul (-A) (-C) Φ).symm
      _ = (-(A + C)) * Φ := by
        exact congrArg (fun z : ℂ => z * Φ) (neg_add A C).symm
  calc
    zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel f F t +
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel f F t =
        (-A) * Φ + (-C) * Φ := by
      exact Eq.refl _
    _ = (-(A + C)) * Φ := by
      exact hneg_sum_mul
    _ = (-G) * Φ := by
      exact congrArg (fun z : ℂ => (-z) * Φ) hsum
    _ = zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F t := by
      exact Eq.refl _

/-- Integral recombination for the reflected inverse-Gamma remainder from its
reflected archimedean and correction components. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integral_eq_archimedean_add_correction_integrals
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (harch :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
          f F)
        (volume : Measure ℝ))
    (hcorr :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
          f F)
        (volume : Measure ℝ)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        f F t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
          f F t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
            f F t := by
  have hsum :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
            f F t +
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
            f F t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
            f F t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
              f F t :=
    integral_add harch hcorr
  have hpoint :
      (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
              f F t +
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
              f F t :=
    Filter.Eventually.of_forall
      (fun t : ℝ =>
        (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_add_correction_eq_inverseGamma
          f F t).symm)
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        f F t) =
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
              f F t +
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
              f F t := by
      exact integral_congr_ae hpoint
    _ =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
            f F t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
              f F t := by
      exact hsum

/-- If the reflected inverse-Gamma and correction kernels are integrable, then
the reflected archimedean component is integrable. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_integrable_of_inverseGamma_and_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hinv :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F)
        (volume : Measure ℝ))
    (hcorr :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
          f F)
        (volume : Measure ℝ)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
        f F)
      (volume : Measure ℝ) := by
  have hdiff :
      Integrable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              f F t -
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
              f F t)
        (volume : Measure ℝ) :=
    hinv.sub hcorr
  have hpoint :
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
          f F) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              f F t -
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
              f F t :=
    Filter.Eventually.of_forall
      (fun t : ℝ =>
        let A : ℂ :=
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
            f F t
        let C : ℂ :=
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
            f F t
        let G : ℂ :=
          zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            f F t
        have hsum : A + C = G :=
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_add_correction_eq_inverseGamma
            f F t
        calc
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
              f F t = A := by
            exact Eq.refl _
          _ = (A + C) - C := by
            exact (add_sub_cancel A C).symm
          _ = G - C := by
            exact congrArg (fun z : ℂ => z - C) hsum
          _ =
              zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
                  f F t -
                zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
                  f F t := by
            exact Eq.refl _)
  exact hdiff.congr hpoint.symm

/-- A right-line correction factor bound packages the reflected correction
kernel.  This is deliberately stated at the factor-bound level so the
correction owner can supply the bound without this prime algebra file importing
downstream value files. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_majorantPackage_of_right_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          -(explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F (-t))))
        (volume : Measure ℝ))
    (hfactor_bound :
      ∀ t : ℝ,
        ‖explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
        f F) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    -(explicitFormulaCorrectionLogDerivative
      (zetaCompletedExplicitFormulaRightAffineLine F (-t)))
  have hA_bound :
      ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖) := by
    intro t
    have hraw :
        ‖explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F (-t))‖ ≤
          B * (1 + ‖-t‖) :=
      hfactor_bound (-t)
    have hneg_norm :
        ‖A t‖ =
          ‖explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F (-t))‖ :=
      norm_neg
        (explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine F (-t)))
    have ht_norm : ‖-t‖ = ‖t‖ :=
      norm_neg t
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ B * (1 + ‖t‖))
        hneg_norm.symm
        (hraw.trans_eq
          (congrArg (fun x : ℝ => B * (1 + x)) ht_norm))
  have hpackage :
      ExplicitFormulaAffineKernelMajorantPackage
        (fun t : ℝ =>
          A t *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) :=
    zetaCompletedExplicitFormulaLeftCenteredAffineProduct_majorantPackage_of_linear_factor_bound_common
      f F h A B hB_nonneg hfactor_meas hA_bound
  have hfun :
      (fun t : ℝ =>
        A t *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
          f F := by
    funext t
    exact Eq.refl _
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        ExplicitFormulaAffineKernelMajorantPackage φ)
      hfun
      hpackage

/-- Integrability of the reflected correction kernel from a right-line
correction factor bound. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integrable_of_right_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          -(explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F (-t))))
        (volume : Measure ℝ))
    (hfactor_bound :
      ∀ t : ℝ,
        ‖explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
        f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_majorantPackage_of_right_factor_bound
    f F h B hB_nonneg hfactor_meas hfactor_bound).integrable

/-- A right-line inverse-Gamma factor bound packages the reflected left
inverse-Gamma kernel.

This is the reflected analogue of the ordinary right inverse-Gamma majorant
package, but with the `Phi` factor on the left-centered line.  The statement is
kept at the factor-bound level so that the Gamma/Binet owner can supply the
bound without this file importing downstream inverse-Gamma value wrappers. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_majorantPackage_of_right_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hfactor_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        f F) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 4
  let majorant : ℝ → ℝ := fun t : ℝ =>
    B * C * (1 + ‖t‖) ^ (-(3 : ℤ))
  have hC_nonneg : 0 ≤ C :=
    h.phi_control.verticalStripRapidDecayConstant_nonneg
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 4
  have hintegrable :
      Integrable majorant (volume : Measure ℝ) := by
    have hfinrank : Module.finrank ℝ ℝ = 1 :=
      Module.finrank_self ℝ
    have hfinrank_cast : ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
      congrArg (fun n : ℕ => (n : ℝ)) hfinrank
    have hdim : (Module.finrank ℝ ℝ : ℝ) < 3 :=
      Eq.subst
        (motive := fun x : ℝ => x < 3)
        hfinrank_cast.symm
        (lt_trans one_lt_two two_lt_three)
    have hbase :
        Integrable
          (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      integrable_one_add_norm (E := ℝ) hdim
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
  have hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          -(inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F (-t))))
        (volume : Measure ℝ) := by
    have hraw :
        Continuous
          (fun t : ℝ =>
            inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaRightAffineLine F (-t))) :=
      (zetaCompletedExplicitFormulaInverseGammaLogDeriv_rightAffineLine_continuous
        F).comp continuous_neg
    exact hraw.aestronglyMeasurable.neg
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
        ‖-(inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)))‖ *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ ≤
          majorant t :=
    Filter.Eventually.of_forall
      (fun t : ℝ =>
        have hfactor_raw :
            ‖inverseGammaCompletionLogDeriv
                (zetaCompletedExplicitFormulaRightAffineLine F (-t))‖ ≤
              B * (1 + ‖-t‖) :=
          hfactor_bound (-t)
        have hneg_norm :
            ‖-(inverseGammaCompletionLogDeriv
                (zetaCompletedExplicitFormulaRightAffineLine F (-t)))‖ =
              ‖inverseGammaCompletionLogDeriv
                (zetaCompletedExplicitFormulaRightAffineLine F (-t))‖ :=
          norm_neg
            (inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaRightAffineLine F (-t)))
        have ht_norm : ‖-t‖ = ‖t‖ :=
          norm_neg t
        have hfactor :
            ‖-(inverseGammaCompletionLogDeriv
                (zetaCompletedExplicitFormulaRightAffineLine F (-t)))‖ ≤
              B * (1 + ‖t‖) := by
          exact
            Eq.subst
              (motive := fun x : ℝ => x ≤ B * (1 + ‖t‖))
              hneg_norm.symm
              (hfactor_raw.trans_eq
                (congrArg (fun x : ℝ => B * (1 + x)) ht_norm))
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
            ‖-(inverseGammaCompletionLogDeriv
                (zetaCompletedExplicitFormulaRightAffineLine F (-t)))‖ *
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
                exact
                  congrArg (fun x : ℝ => B * (x * b))
                    (mul_comm a C)
              _ = B * (C * (a * b)) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc C a b)
              _ = B * C * (a * b) :=
                (mul_assoc B C (a * b)).symm
          calc
            (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) =
                B * C *
                  ((1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ))) :=
              hscalar
            _ = B * C * (1 + ‖t‖) ^ (-(3 : ℤ)) :=
              congrArg (fun x : ℝ => B * C * x) hweight
        hprod.trans_eq hassoc)
  exact
    ExplicitFormulaAffineKernelMajorantPackage.of_mul_le
      majorant hintegrable hfactor_meas hphi_meas hbound

/-- Integrability of the reflected inverse-Gamma kernel from a right-line
inverse-Gamma factor bound. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_of_right_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hfactor_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_majorantPackage_of_right_factor_bound
    f F h B hB_nonneg hfactor_bound).integrable

/-- Integrability of the reflected inverse-Gamma kernel from the Gamma/Binet
right-line factor bound. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_of_gammaBinetCoherence
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel f F)
      (volume : Measure ℝ) := by
  match
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_gammaBinetCoherence_owner
      F hcoh with
  | ⟨B, hB_nonneg, hfactor_bound⟩ =>
      exact
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_of_right_factor_bound
          f F h B hB_nonneg hfactor_bound

/-- Pointwise reflected completed-log-derivative expansion into the reflected
von Mangoldt term series plus the reflected inverse-Gamma kernel.

The only analytic input is summability of the right-line Dirichlet terms at
the reflected point.  Sum-integral exchange is intentionally not part of this
lemma. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_eq_tsum_termKernel_add_reflectedInverseGamma
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ)
    (hterm :
      Summable
        (fun n : ℕ =>
          LSeries.term (↗Λ)
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)) n)) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel f F t =
      (∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) +
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F t := by
  let s : ℂ := zetaCompletedExplicitFormulaRightAffineLine F (-t)
  let Φ : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  let Lterm : ℕ → ℂ :=
    fun n : ℕ => LSeries.term (↗Λ) s n
  let G : ℂ := inverseGammaCompletionLogDeriv s
  have hL_eq_tsum :
      (L ↗Λ) s = ∑' n : ℕ, Lterm n := by
    rfl
  have hprime :
      explicitFormulaPrimeLogDerivative s = (L ↗Λ) s :=
    (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_eq_logDerivative
      F (-t)).symm
  have hprime_def :
      explicitFormulaPrimeLogDerivative s =
        completedZetaNegLogDeriv s - G := by
    rfl
  have hcompleted :
      completedZetaNegLogDeriv s = (∑' n : ℕ, Lterm n) + G := by
    calc
      completedZetaNegLogDeriv s =
          explicitFormulaPrimeLogDerivative s + G := by
        calc
          completedZetaNegLogDeriv s =
              (completedZetaNegLogDeriv s - G) + G := by
            exact (sub_add_cancel
              (completedZetaNegLogDeriv s) G).symm
          _ = explicitFormulaPrimeLogDerivative s + G := by
            exact congrArg (fun z : ℂ => z + G) hprime_def.symm
      _ = (L ↗Λ) s + G := by
        exact congrArg (fun z : ℂ => z + G) hprime
      _ = (∑' n : ℕ, Lterm n) + G := by
        exact congrArg (fun z : ℂ => z + G) hL_eq_tsum
  have hneg_mul :
      (-(∑' n : ℕ, Lterm n)) * Φ =
        ∑' n : ℕ, (-(Lterm n)) * Φ := by
    calc
      (-(∑' n : ℕ, Lterm n)) * Φ =
          (∑' n : ℕ, -(Lterm n)) * Φ := by
        exact congrArg (fun z : ℂ => z * Φ) (tsum_neg.symm)
      _ = ∑' n : ℕ, (-(Lterm n)) * Φ := by
        exact (Summable.tsum_mul_right Φ hterm.neg).symm
  have hterm_kernel :
      (fun n : ℕ => (-(Lterm n)) * Φ) =
        fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F n t := by
    funext n
    rfl
  calc
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel f F t =
        (-(completedZetaNegLogDeriv s)) * Φ := by
      rfl
    _ = (-((∑' n : ℕ, Lterm n) + G)) * Φ := by
      exact congrArg (fun z : ℂ => (-z) * Φ) hcompleted
    _ = ((-(∑' n : ℕ, Lterm n)) + (-G)) * Φ := by
      exact congrArg (fun z : ℂ => z * Φ)
        (neg_add (∑' n : ℕ, Lterm n) G)
    _ = (-(∑' n : ℕ, Lterm n)) * Φ + (-G) * Φ := by
      exact add_mul (-(∑' n : ℕ, Lterm n)) (-G) Φ
    _ =
        (∑' n : ℕ, (-(Lterm n)) * Φ) + (-G) * Φ := by
      exact congrArg (fun z : ℂ => z + (-G) * Φ) hneg_mul
    _ =
        (∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) +
          (-G) * Φ := by
      exact congrArg
        (fun φ : ℕ → ℂ => (∑' n : ℕ, φ n) + (-G) * Φ)
        hterm_kernel
    _ =
        (∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) +
          zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            f F t := by
      rfl

/-- Pointwise reflected completed-log-derivative expansion with the right-line
Dirichlet summability discharged by the affine-line von Mangoldt owner. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_eq_tsum_termKernel_add_reflectedInverseGamma_ownerSummable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel f F t =
      (∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) +
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F t := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_eq_tsum_termKernel_add_reflectedInverseGamma
      f F t
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_terms_complex_summable
        F (-t))

/-- At a positive natural index, the reflected single-term kernel unfolds to
the ordinary reflected Dirichlet monomial. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_eq_of_ne_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t =
      (-((↗Λ) n /
          (n : ℂ) ^
            zetaCompletedExplicitFormulaRightAffineLine F (-t))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
  unfold zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
  exact congrArg
    (fun z : ℂ =>
      (-z) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
    (LSeries.term_of_ne_zero hn (↗Λ)
      (zetaCompletedExplicitFormulaRightAffineLine F (-t)))

/-- The zeroth reflected term kernel vanishes because the zeroth
Dirichlet-series term is defined to be zero. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F 0 t =
      0 := by
  unfold zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
  calc
    (-(LSeries.term (↗Λ)
        (zetaCompletedExplicitFormulaRightAffineLine F (-t)) 0)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) =
        (-0) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
      exact congrArg
        (fun z : ℂ =>
          (-z) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
        (LSeries.term_zero (↗Λ)
          (zetaCompletedExplicitFormulaRightAffineLine F (-t)))
    _ = 0 *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
      exact congrArg
        (fun z : ℂ =>
          z *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
        (neg_zero : -(0 : ℂ) = 0)
    _ = 0 := by
      exact zero_mul
        (zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))

/-- The zeroth reflected term has zero whole-line integral. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
        f F 0 t) =
      0 := by
  have hfun :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
          f F 0 t) =
        fun _t : ℝ => (0 : ℂ) := by
    funext t
    exact zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_zero
      f F t
  exact
    Eq.trans
      (congrArg
        (fun φ : ℝ → ℂ => ∫ t : ℝ, φ t)
        hfun)
      (integral_zero (α := ℝ) (E := ℂ))

/-- The norm of a reflected term kernel factors into the norm of the
Dirichlet term and the norm of the left-centered test-transform factor. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_norm_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) (t : ℝ) :
    ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t‖ =
      ‖LSeries.term (↗Λ)
          (zetaCompletedExplicitFormulaRightAffineLine F (-t)) n‖ *
        ‖zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ := by
  calc
    ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t‖ =
        ‖-(LSeries.term (↗Λ)
          (zetaCompletedExplicitFormulaRightAffineLine F (-t)) n)‖ *
          ‖zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ := by
      exact
        norm_mul
          (-(LSeries.term (↗Λ)
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)) n))
          (zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
    _ =
        ‖LSeries.term (↗Λ)
          (zetaCompletedExplicitFormulaRightAffineLine F (-t)) n‖ *
          ‖zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ := by
      exact congrArg
        (fun r : ℝ =>
          r *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖)
        (norm_neg
          (LSeries.term (↗Λ)
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)) n))

/-- Strong measurability of each reflected Dirichlet-term kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (n : ℕ) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
          f F n t)
      (volume : Measure ℝ) := by
  have hterm_cont :
      Continuous
        (fun t : ℝ =>
          LSeries.term (↗Λ)
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)) n) :=
    (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_term_rightAffineLine_continuous
      F n).comp continuous_neg
  have hterm :
      AEStronglyMeasurable
        (fun t : ℝ =>
          -(LSeries.term (↗Λ)
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)) n))
        (volume : Measure ℝ) :=
    hterm_cont.aestronglyMeasurable.neg
  have hphi :
      AEStronglyMeasurable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_aestronglyMeasurable
      f F h
  exact hterm.mul hphi

/-- For each fixed height, the reflected term-kernel norm series is
summable. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_norm_summable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    Summable
      (fun n : ℕ =>
        ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
          f F n t‖) := by
  let phiNorm : ℝ :=
    ‖zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖
  let termNorm : ℕ → ℝ := fun n : ℕ =>
    ‖LSeries.term (↗Λ)
      (zetaCompletedExplicitFormulaRightAffineLine F (-t)) n‖
  have hterm : Summable termNorm :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_terms_summable
      F (-t)
  have hkernel :
      (fun n : ℕ =>
        ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
          f F n t‖) =
        fun n : ℕ => termNorm n * phiNorm := by
    funext n
    exact
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_norm_eq
        f F n t
  have hscaled : Summable (fun n : ℕ => termNorm n * phiNorm) :=
    Summable.mul_right phiNorm hterm
  exact
    Eq.subst
      (motive := fun ψ : ℕ → ℝ => Summable ψ)
      hkernel.symm
      hscaled

/-- The reflected pointwise norm series is controlled by the fixed right-line
Dirichlet-series bound and the left-centered rapid-decay majorant. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_tsum_norm_le_factorBound_mul_leftPhiMajorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (t : ℝ) :
    (∑' n : ℕ,
      ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
        f F n t‖)
      ≤ zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
        (h.phi_control.verticalStripRapidDecayConstant
          ((1 : ℝ) - F.c - (1 / 2 : ℝ))
          ((1 : ℝ) - F.c - (1 / 2 : ℝ)) N *
          (1 + ‖t‖) ^ (-(N : ℤ))) := by
  let phi : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  let termNorm : ℕ → ℝ := fun n : ℕ =>
    ‖LSeries.term (↗Λ)
      (zetaCompletedExplicitFormulaRightAffineLine F (-t)) n‖
  let baseNorm : ℕ → ℝ := fun n : ℕ =>
    ‖LSeries.term (↗Λ) (F.c : ℂ) n‖
  let majorant : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) N *
      (1 + ‖t‖) ^ (-(N : ℤ))
  have hterm_summable : Summable termNorm :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_terms_summable
      F (-t)
  have hkernel_norm :
      (fun n : ℕ =>
        ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
          f F n t‖) =
        fun n : ℕ => termNorm n * ‖phi‖ := by
    funext n
    exact
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_norm_eq
        f F n t
  have hsum_kernel :
      (∑' n : ℕ,
        ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
          f F n t‖) =
        ∑' n : ℕ, termNorm n * ‖phi‖ :=
    congrArg
      (fun ψ : ℕ → ℝ => ∑' n : ℕ, ψ n)
      hkernel_norm
  have hsum_mul :
      (∑' n : ℕ, termNorm n * ‖phi‖) =
        (∑' n : ℕ, termNorm n) * ‖phi‖ :=
    Summable.tsum_mul_right ‖phi‖ hterm_summable
  have hterm_base :
      termNorm = baseNorm := by
    funext n
    exact
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_term_norm_eq
        F (-t) n
  have hsum_base :
      (∑' n : ℕ, termNorm n) =
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F := by
    exact
      Eq.trans
        (congrArg
          (fun ψ : ℕ → ℝ => ∑' n : ℕ, ψ n)
          hterm_base)
        (Eq.refl _)
  have hphi : ‖phi‖ ≤ majorant :=
    zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_decay_bound
      f F h N t
  have hB_nonneg :
      0 ≤ zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound_nonneg F
  calc
    (∑' n : ℕ,
      ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
        f F n t‖) =
        ∑' n : ℕ, termNorm n * ‖phi‖ := hsum_kernel
    _ = (∑' n : ℕ, termNorm n) * ‖phi‖ := hsum_mul
    _ = zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
          ‖phi‖ := by
      exact
        congrArg
          (fun x : ℝ => x * ‖phi‖)
          hsum_base
    _ ≤ zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
          majorant := by
      exact mul_le_mul_of_nonneg_left hphi hB_nonneg

/-- The reflected inverse-quadratic majorant used for the term-kernel norm
series is integrable on the real line. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_majorant_two_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
          h.phi_control.verticalStripRapidDecayConstant
            ((1 : ℝ) - F.c - (1 / 2 : ℝ))
            ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2 *
          (1 + ‖t‖) ^ (-(2 : ℤ)))
      (volume : Measure ℝ) := by
  let B : ℝ :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2
  let majorantInt : ℝ → ℝ := fun t : ℝ =>
    B * C * (1 + ‖t‖) ^ (-(2 : ℤ))
  let majorantReal : ℝ → ℝ := fun t : ℝ =>
    B * C * (1 + ‖t‖) ^ (-(2 : ℝ))
  have hfinrank : Module.finrank ℝ ℝ = 1 :=
    Module.finrank_self ℝ
  have hfinrank_cast : ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
    congrArg (fun n : ℕ => (n : ℝ)) hfinrank
  have hdim : (Module.finrank ℝ ℝ : ℝ) < 2 :=
    Eq.subst
      (motive := fun x : ℝ => x < 2)
      hfinrank_cast.symm
      one_lt_two
  have hbase :
      Integrable
        (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ)))
        (volume : Measure ℝ) :=
    integrable_one_add_norm (E := ℝ) hdim
  have hreal : Integrable majorantReal (volume : Measure ℝ) :=
    (hbase.const_mul C).const_mul B
  have hint_eq_real : majorantInt = majorantReal := by
    funext t
    have hpow :
        (1 + ‖t‖) ^ (-(2 : ℤ)) =
          (1 + ‖t‖) ^ (-(2 : ℝ)) :=
      (Real.rpow_intCast (1 + ‖t‖) (-(2 : ℤ))).symm
    exact congrArg (fun x : ℝ => B * C * x) hpow
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
      hint_eq_real.symm
      hreal

/-- The reflected inverse-quadratic majorant is nonnegative pointwise. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_majorant_two_nonneg
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (t : ℝ) :
    0 ≤
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
        h.phi_control.verticalStripRapidDecayConstant
          ((1 : ℝ) - F.c - (1 / 2 : ℝ))
          ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2 *
        (1 + ‖t‖) ^ (-(2 : ℤ)) := by
  have hbound :
      (∑' n : ℕ,
        ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
          f F n t‖)
        ≤ zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
          (h.phi_control.verticalStripRapidDecayConstant
            ((1 : ℝ) - F.c - (1 / 2 : ℝ))
            ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2 *
            (1 + ‖t‖) ^ (-(2 : ℤ))) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_tsum_norm_le_factorBound_mul_leftPhiMajorant
      f F h 2 t
  have hleft_nonneg :
      0 ≤
        (∑' n : ℕ,
          ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F n t‖) :=
    tsum_nonneg
      (fun n : ℕ =>
        norm_nonneg
          (zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F n t))
  have hassoc :
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
          (h.phi_control.verticalStripRapidDecayConstant
            ((1 : ℝ) - F.c - (1 / 2 : ℝ))
            ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2 *
            (1 + ‖t‖) ^ (-(2 : ℤ))) =
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
          h.phi_control.verticalStripRapidDecayConstant
            ((1 : ℝ) - F.c - (1 / 2 : ℝ))
            ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2 *
          (1 + ‖t‖) ^ (-(2 : ℤ)) :=
    (mul_assoc
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F)
      (h.phi_control.verticalStripRapidDecayConstant
        ((1 : ℝ) - F.c - (1 / 2 : ℝ))
        ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2)
      ((1 + ‖t‖) ^ (-(2 : ℤ)))).symm
  exact hleft_nonneg.trans (hbound.trans_eq hassoc)

/-- Tonelli converts the summed `lintegral` of reflected term-kernel norms
into the `lintegral` of the pointwise norm series, bounded by the reflected
inverse-quadratic majorant. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_lintegral_norm_tsum_le_majorant_two_lintegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∑' n : ℕ,
      ∫⁻ t : ℝ,
        ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
          f F n t‖₊ ∂(volume : Measure ℝ))
      ≤
    ∫⁻ t : ℝ,
      ENNReal.ofReal
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
          h.phi_control.verticalStripRapidDecayConstant
            ((1 : ℝ) - F.c - (1 / 2 : ℝ))
            ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2 *
          (1 + ‖t‖) ^ (-(2 : ℤ))) ∂(volume : Measure ℝ) := by
  let kernel : ℕ → ℝ → ℂ := fun n t =>
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t
  let majorant : ℝ → ℝ := fun t : ℝ =>
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
      h.phi_control.verticalStripRapidDecayConstant
        ((1 : ℝ) - F.c - (1 / 2 : ℝ))
        ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2 *
      (1 + ‖t‖) ^ (-(2 : ℤ))
  have hmeas :
      ∀ n : ℕ,
        AEMeasurable (fun t : ℝ => (‖kernel n t‖₊ : ℝ≥0∞))
          (volume : Measure ℝ) := by
    intro n
    exact
      (zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_aestronglyMeasurable
        f F h n).ennnorm
  have htonelli :
      (∑' n : ℕ,
        ∫⁻ t : ℝ, (‖kernel n t‖₊ : ℝ≥0∞) ∂(volume : Measure ℝ)) =
        ∫⁻ t : ℝ,
          ∑' n : ℕ, (‖kernel n t‖₊ : ℝ≥0∞) ∂(volume : Measure ℝ) :=
    (MeasureTheory.lintegral_tsum hmeas).symm
  have hpointwise :
      ∀ t : ℝ,
        (∑' n : ℕ, (‖kernel n t‖₊ : ℝ≥0∞)) ≤
          ENNReal.ofReal (majorant t) := by
    intro t
    let normSeries : ℕ → ℝ := fun n : ℕ => ‖kernel n t‖
    have hnorm_nonneg : ∀ n : ℕ, 0 ≤ normSeries n :=
      fun n : ℕ => norm_nonneg (kernel n t)
    have hnorm_summable : Summable normSeries :=
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_norm_summable
        f F t
    have hcoe_terms :
        (fun n : ℕ => (‖kernel n t‖₊ : ℝ≥0∞)) =
          fun n : ℕ => ENNReal.ofReal (normSeries n) := by
      funext n
      exact (ofReal_norm_eq_coe_nnnorm (kernel n t)).symm
    have hcoe_tsum :
        (∑' n : ℕ, (‖kernel n t‖₊ : ℝ≥0∞)) =
          ENNReal.ofReal (∑' n : ℕ, normSeries n) := by
      exact
        Eq.trans
          (congrArg
            (fun φ : ℕ → ℝ≥0∞ => ∑' n : ℕ, φ n)
            hcoe_terms)
          (ENNReal.ofReal_tsum_of_nonneg hnorm_nonneg hnorm_summable)
    have hreal_bound :
        (∑' n : ℕ, normSeries n) ≤ majorant t := by
      have hbound :
          (∑' n : ℕ,
            ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F n t‖)
            ≤ zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
              (h.phi_control.verticalStripRapidDecayConstant
                ((1 : ℝ) - F.c - (1 / 2 : ℝ))
                ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2 *
                (1 + ‖t‖) ^ (-(2 : ℤ))) :=
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_tsum_norm_le_factorBound_mul_leftPhiMajorant
          f F h 2 t
      have hnorm_tsum :
          (∑' n : ℕ, normSeries n) =
            (∑' n : ℕ,
              ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                f F n t‖) :=
        Eq.refl _
      have hassoc :
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
              (h.phi_control.verticalStripRapidDecayConstant
                ((1 : ℝ) - F.c - (1 / 2 : ℝ))
                ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2 *
                (1 + ‖t‖) ^ (-(2 : ℤ))) =
            majorant t :=
        (mul_assoc
          (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F)
          (h.phi_control.verticalStripRapidDecayConstant
            ((1 : ℝ) - F.c - (1 / 2 : ℝ))
            ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2)
          ((1 + ‖t‖) ^ (-(2 : ℤ)))).symm
      exact hnorm_tsum.trans_le (hbound.trans_eq hassoc)
    exact hcoe_tsum.trans_le (ENNReal.ofReal_le_ofReal hreal_bound)
  exact
    htonelli.trans_le
      (MeasureTheory.lintegral_mono hpointwise)

/-- The summed `lintegral` of reflected term-kernel norms is finite. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_lintegral_norm_tsum_ne_top
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∑' n : ℕ,
      ∫⁻ t : ℝ,
        ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
          f F n t‖₊ ∂(volume : Measure ℝ)) ≠ ∞ := by
  let majorant : ℝ → ℝ := fun t : ℝ =>
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
      h.phi_control.verticalStripRapidDecayConstant
        ((1 : ℝ) - F.c - (1 / 2 : ℝ))
        ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2 *
      (1 + ‖t‖) ^ (-(2 : ℤ))
  have hle :
      (∑' n : ℕ,
        ∫⁻ t : ℝ,
          ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F n t‖₊ ∂(volume : Measure ℝ))
        ≤
      ∫⁻ t : ℝ, ENNReal.ofReal (majorant t) ∂(volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_lintegral_norm_tsum_le_majorant_two_lintegral
      f F h
  have hmajorant_integrable :
      Integrable majorant (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_majorant_two_integrable
      f F h
  have hmajorant_nonneg :
      0 ≤ᵐ[(volume : Measure ℝ)] majorant :=
    Eventually.of_forall
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_majorant_two_nonneg
          f F h t)
  have hmajorant_lintegral_eq :
      ENNReal.ofReal (∫ t : ℝ, majorant t ∂(volume : Measure ℝ)) =
        ∫⁻ t : ℝ, ENNReal.ofReal (majorant t) ∂(volume : Measure ℝ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      hmajorant_integrable hmajorant_nonneg
  have hmajorant_lintegral_ne_top :
      (∫⁻ t : ℝ, ENNReal.ofReal (majorant t) ∂(volume : Measure ℝ)) ≠ ∞ := by
    exact
      Eq.subst
        (motive := fun x : ℝ≥0∞ => x ≠ ∞)
        hmajorant_lintegral_eq
        ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hmajorant_lintegral_ne_top hle

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
