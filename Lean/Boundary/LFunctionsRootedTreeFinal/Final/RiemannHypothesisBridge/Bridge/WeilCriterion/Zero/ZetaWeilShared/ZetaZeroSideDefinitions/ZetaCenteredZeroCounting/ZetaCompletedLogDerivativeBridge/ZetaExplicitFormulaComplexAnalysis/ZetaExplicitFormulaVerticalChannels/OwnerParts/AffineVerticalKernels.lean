import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ChannelRemainderAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaLogDerivative.Owner

/-!
# Affine vertical-line kernels

This file owns the common affine-line parametrizations and the named kernels
used by the prime, archimedean, and isolated pole vertical-channel estimates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open LSeries ArithmeticFunction
open scoped ArithmeticFunction

namespace ZetaAdmissibleFunction

/-- The right vertical line `F.c + i t`. -/
noncomputable def zetaCompletedExplicitFormulaRightAffineLine
    (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  (F.c : ℂ) + t * Complex.I

/-- The shifted right vertical line `(F.c - 1/2) + i t`. -/
noncomputable def zetaCompletedExplicitFormulaRightCenteredAffineLine
    (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  ((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I

/-- The left vertical line `(1 - F.c) + i t`. -/
noncomputable def zetaCompletedExplicitFormulaLeftAffineLine
    (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  ((1 : ℂ) - (F.c : ℂ)) + t * Complex.I

/-- The shifted left vertical line `(1 - F.c - 1/2) + i t`. -/
noncomputable def zetaCompletedExplicitFormulaLeftCenteredAffineLine
    (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  ((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I

/-- Right-face von Mangoldt kernel on the affine line. -/
noncomputable def zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  L ↗Λ (zetaCompletedExplicitFormulaRightAffineLine F t) *
    zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)

/-- Left-face prime logarithmic-derivative kernel on the affine line. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  explicitFormulaPrimeLogDerivative (zetaCompletedExplicitFormulaLeftAffineLine F t) *
    zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- Right-face inverse-Gamma completion kernel on the affine line. -/
noncomputable def zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  inverseGammaCompletionLogDeriv (zetaCompletedExplicitFormulaRightAffineLine F t) *
    zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)

/-- Left-face inverse-Gamma completion kernel on the affine line. -/
noncomputable def zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  inverseGammaCompletionLogDeriv (zetaCompletedExplicitFormulaLeftAffineLine F t) *
    zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- Pointwise decomposition of the completed left affine-line kernel into
prime and inverse-Gamma packets. -/
theorem zetaCompletedExplicitFormula_completedLeftAffineKernel_eq_prime_add_inverseGamma
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    completedZetaNegLogDeriv (zetaCompletedExplicitFormulaLeftAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) =
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t +
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
  let Z : ℂ :=
    completedZetaNegLogDeriv (zetaCompletedExplicitFormulaLeftAffineLine F t)
  let G : ℂ :=
    inverseGammaCompletionLogDeriv (zetaCompletedExplicitFormulaLeftAffineLine F t)
  let Φ : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  calc
    Z * Φ = ((Z - G) + G) * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) (sub_add_cancel Z G).symm
    _ = (Z - G) * Φ + G * Φ := by
      exact add_mul (Z - G) G Φ
    _ =
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t +
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
      exact Eq.refl _

/-- Pointwise decomposition of the completed right affine-line kernel into the
right von Mangoldt prime packet and the right inverse-Gamma packet. -/
theorem zetaCompletedExplicitFormula_completedRightAffineKernel_eq_prime_add_inverseGamma
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    completedZetaNegLogDeriv (zetaCompletedExplicitFormulaRightAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) =
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t +
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t := by
  let Z : ℂ :=
    completedZetaNegLogDeriv (zetaCompletedExplicitFormulaRightAffineLine F t)
  let G : ℂ :=
    inverseGammaCompletionLogDeriv (zetaCompletedExplicitFormulaRightAffineLine F t)
  let Φ : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
  calc
    Z * Φ = ((Z - G) + G) * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) (sub_add_cancel Z G).symm
    _ = (Z - G) * Φ + G * Φ := by
      exact add_mul (Z - G) G Φ
    _ =
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t +
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t := by
      exact Eq.refl _

/-- Right-face archimedean logarithmic-derivative kernel on the affine line. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  explicitFormulaArchimedeanLogDerivative
      (zetaCompletedExplicitFormulaRightAffineLine F t) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)

/-- Right-face elementary pole-correction kernel on the affine line. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  explicitFormulaCorrectionLogDerivative
      (zetaCompletedExplicitFormulaRightAffineLine F t) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)

/-- Left-face archimedean logarithmic-derivative kernel on the affine line. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  explicitFormulaArchimedeanLogDerivative
      (zetaCompletedExplicitFormulaLeftAffineLine F t) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- Left-face elementary pole-correction kernel on the affine line. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  explicitFormulaCorrectionLogDerivative
      (zetaCompletedExplicitFormulaLeftAffineLine F t) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- Right-minus-left inverse-Gamma completion kernel on the paired affine
vertical lines. -/
noncomputable def zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t -
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t

/-- Right-minus-left archimedean logarithmic-derivative kernel on the paired
affine vertical lines. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t -
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t

/-- Right-minus-left elementary correction kernel on the paired affine vertical
lines. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F t -
    zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F t

/-- On the right affine line, the archimedean and elementary correction affine
kernels recombine to the inverse-Gamma completion affine kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_add_correction_eq_inverseGamma
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t +
        zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F t =
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t := by
  let s : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
  let Φ : ℂ := zetaCompletedExplicitFormulaPhi f
    (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
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
  calc
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t +
        zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F t =
        A * Φ + C * Φ := by
      exact Eq.refl _
    _ = (A + C) * Φ := by
      exact (add_mul A C Φ).symm
    _ = G * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hsum
    _ = zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t := by
      exact Eq.refl _

/-- On the left affine line, the archimedean and elementary correction affine
kernels recombine to the inverse-Gamma completion affine kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_add_correction_eq_inverseGamma
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t +
        zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F t =
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
  let s : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  let Φ : ℂ := zetaCompletedExplicitFormulaPhi f
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
  calc
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t +
        zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F t =
        A * Φ + C * Φ := by
      exact Eq.refl _
    _ = (A + C) * Φ := by
      exact (add_mul A C Φ).symm
    _ = G * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hsum
    _ = zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
      exact Eq.refl _

/-- The right-minus-left inverse-Gamma affine kernel splits pointwise into the
right-minus-left archimedean and elementary correction affine kernels. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_eq_archimedean_add_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t =
      zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F t +
        zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t := by
  let IR : ℂ := zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t
  let IL : ℂ := zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
  let AR : ℂ := zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t
  let AL : ℂ := zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t
  let CR : ℂ := zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F t
  let CL : ℂ := zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F t
  have hright : AR + CR = IR :=
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_add_correction_eq_inverseGamma
      f F t
  have hleft : AL + CL = IL :=
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_add_correction_eq_inverseGamma
      f F t
  calc
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t =
        IR - IL := by
      exact Eq.refl _
    _ = (AR + CR) - (AL + CL) := by
      exact congrArg₂ HSub.hSub hright.symm hleft.symm
    _ = (AR - AL) + (CR - CL) := by
      exact add_sub_add_comm AR CR AL CL
    _ =
        zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F t +
          zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t := by
      exact Eq.refl _

/-- The archimedean difference kernel is the inverse-Gamma difference kernel
minus the elementary correction difference kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_eq_inverseGamma_sub_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F t =
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t -
        zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t := by
  let A : ℂ := zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F t
  let C : ℂ := zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t
  let G : ℂ := zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t
  have hG : G = A + C :=
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_eq_archimedean_add_correction
      f F t
  calc
    zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F t =
        A := by
      exact Eq.refl _
    _ = (A + C) - C := by
      exact (add_sub_cancel A C).symm
    _ = G - C := by
      exact congrArg (fun z : ℂ => z - C) hG.symm
    _ =
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t -
          zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t := by
      exact Eq.refl _

/-- Right zero-pole inversion kernel on the affine line. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  (-1 / zetaCompletedExplicitFormulaRightAffineLine F t) *
    zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)

/-- Right one-pole correction kernel on the affine line. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  (-(1 / (zetaCompletedExplicitFormulaRightAffineLine F t - 1))) *
    zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)

/-- Left zero-pole correction kernel on the affine line. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  (-1 / zetaCompletedExplicitFormulaLeftAffineLine F t) *
    zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- Left one-pole correction kernel on the affine line. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  (-(1 / (zetaCompletedExplicitFormulaLeftAffineLine F t - 1))) *
    zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- The right elementary correction affine kernel is the sum of its zero-pole
and one-pole affine kernels. -/
theorem zetaCompletedExplicitFormulaCorrectionRightAffineKernel_eq_zeroPole_add_onePole
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F t =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t +
        zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t := by
  let s : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
  let Φ : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
  let A : ℂ := -1 / s
  let B : ℂ := 1 / (s - 1)
  have hcorr :
      explicitFormulaCorrectionLogDerivative s = A - B :=
    explicitFormulaCorrectionLogDerivative_eq_poleCorrection s
  have hmul :
      (A - B) * Φ = A * Φ + (-B) * Φ := by
    calc
      (A - B) * Φ = (A + -B) * Φ := by
        exact congrArg (fun z : ℂ => z * Φ) (sub_eq_add_neg A B)
      _ = A * Φ + (-B) * Φ := by
        exact add_mul A (-B) Φ
  have hone :
      (-B) * Φ =
        (-(1 / (zetaCompletedExplicitFormulaRightAffineLine F t - 1))) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
    exact Eq.refl _
  calc
    zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F t =
        explicitFormulaCorrectionLogDerivative s * Φ := by
      exact Eq.refl _
    _ = (A - B) * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hcorr
    _ = A * Φ + (-B) * Φ := hmul
    _ =
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t +
          zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t := by
      exact congrArg₂ HAdd.hAdd (Eq.refl _) hone

/-- The left elementary correction affine kernel is the sum of its zero-pole
and one-pole affine kernels. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftAffineKernel_eq_zeroPole_add_onePole
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F t =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t +
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t := by
  let s : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  let Φ : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  let A : ℂ := -1 / s
  let B : ℂ := 1 / (s - 1)
  have hcorr :
      explicitFormulaCorrectionLogDerivative s = A - B :=
    explicitFormulaCorrectionLogDerivative_eq_poleCorrection s
  have hmul :
      (A - B) * Φ = A * Φ + (-B) * Φ := by
    calc
      (A - B) * Φ = (A + -B) * Φ := by
        exact congrArg (fun z : ℂ => z * Φ) (sub_eq_add_neg A B)
      _ = A * Φ + (-B) * Φ := by
        exact add_mul A (-B) Φ
  have hone :
      (-B) * Φ =
        (-(1 / (zetaCompletedExplicitFormulaLeftAffineLine F t - 1))) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
    exact Eq.refl _
  calc
    zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F t =
        explicitFormulaCorrectionLogDerivative s * Φ := by
      exact Eq.refl _
    _ = (A - B) * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hcorr
    _ = A * Φ + (-B) * Φ := hmul
    _ =
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t +
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t := by
      exact congrArg₂ HAdd.hAdd (Eq.refl _) hone

/-- The right-minus-left elementary correction affine kernel decomposes into
zero-pole and one-pole difference kernels. -/
theorem zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel_eq_zeroPole_add_onePole
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t =
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t -
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) +
        (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t -
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t) := by
  let R0 : ℂ := zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t
  let R1 : ℂ := zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t
  let L0 : ℂ := zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t
  let L1 : ℂ := zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t
  let R : ℂ := zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F t
  let L : ℂ := zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F t
  have hright : R = R0 + R1 :=
    zetaCompletedExplicitFormulaCorrectionRightAffineKernel_eq_zeroPole_add_onePole
      f F t
  have hleft : L = L0 + L1 :=
    zetaCompletedExplicitFormulaCorrectionLeftAffineKernel_eq_zeroPole_add_onePole
      f F t
  calc
    zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t =
        R - L := by
      exact Eq.refl _
    _ = (R0 + R1) - (L0 + L1) := by
      exact congrArg₂ HSub.hSub hright hleft
    _ = (R0 - L0) + (R1 - L1) := by
      exact add_sub_add_comm R0 R1 L0 L1

theorem zetaCompletedExplicitFormulaRightAffineLine_eq
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaRightAffineLine F t =
      (F.c : ℂ) + t * Complex.I :=
  rfl

theorem zetaCompletedExplicitFormulaRightCenteredAffineLine_eq
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaRightCenteredAffineLine F t =
      ((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I :=
  rfl

theorem zetaCompletedExplicitFormulaLeftAffineLine_eq
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaLeftAffineLine F t =
      ((1 : ℂ) - (F.c : ℂ)) + t * Complex.I :=
  rfl

theorem zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaLeftCenteredAffineLine F t =
      ((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I :=
  rfl

/-- A real multiple of `I` has zero real part. -/
theorem zetaCompletedExplicitFormula_real_mul_I_re_zero (t : ℝ) :
    ((t : ℂ) * Complex.I).re = 0 :=
  Eq.trans
    (Complex.mul_I_re (t : ℂ))
    (Eq.trans
      (congrArg Neg.neg (Complex.ofReal_im t))
      (neg_zero : -(0 : ℝ) = 0))

/-- A real multiple of `I` has imaginary part equal to the real multiplier. -/
theorem zetaCompletedExplicitFormula_real_mul_I_im (t : ℝ) :
    ((t : ℂ) * Complex.I).im = t :=
  Eq.trans
    (Complex.mul_I_im (t : ℂ))
    (Complex.ofReal_re t)

/-- The right affine line has fixed real part `F.c`. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_re
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    (zetaCompletedExplicitFormulaRightAffineLine F t).re = F.c := by
  calc
    (zetaCompletedExplicitFormulaRightAffineLine F t).re =
        ((F.c : ℂ) + (t : ℂ) * Complex.I).re := by
      exact congrArg Complex.re
        (zetaCompletedExplicitFormulaRightAffineLine_eq F t)
    _ = (F.c : ℂ).re + ((t : ℂ) * Complex.I).re := by
      exact Complex.add_re (F.c : ℂ) ((t : ℂ) * Complex.I)
    _ = F.c + 0 := by
      exact congrArg₂ HAdd.hAdd
        (Complex.ofReal_re F.c)
        (zetaCompletedExplicitFormula_real_mul_I_re_zero t)
    _ = F.c := add_zero F.c

/-- The right affine line has imaginary part `t`. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_im
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    (zetaCompletedExplicitFormulaRightAffineLine F t).im = t := by
  calc
    (zetaCompletedExplicitFormulaRightAffineLine F t).im =
        ((F.c : ℂ) + (t : ℂ) * Complex.I).im := by
      exact congrArg Complex.im
        (zetaCompletedExplicitFormulaRightAffineLine_eq F t)
    _ = (F.c : ℂ).im + ((t : ℂ) * Complex.I).im := by
      exact Complex.add_im (F.c : ℂ) ((t : ℂ) * Complex.I)
    _ = 0 + t := by
      exact congrArg₂ HAdd.hAdd
        (Complex.ofReal_im F.c)
        (zetaCompletedExplicitFormula_real_mul_I_im t)
    _ = t := zero_add t

/-- The shifted right affine line has fixed real part `F.c - 1/2`. -/
theorem zetaCompletedExplicitFormulaRightCenteredAffineLine_re
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    (zetaCompletedExplicitFormulaRightCenteredAffineLine F t).re =
      F.c - (1 / 2 : ℝ) := by
  calc
    (zetaCompletedExplicitFormulaRightCenteredAffineLine F t).re =
        (((F.c : ℂ) - (1 / 2 : ℂ)) + (t : ℂ) * Complex.I).re := by
      exact congrArg Complex.re
        (zetaCompletedExplicitFormulaRightCenteredAffineLine_eq F t)
    _ = ((F.c : ℂ) - (1 / 2 : ℂ)).re +
          ((t : ℂ) * Complex.I).re := by
      exact Complex.add_re ((F.c : ℂ) - (1 / 2 : ℂ)) ((t : ℂ) * Complex.I)
    _ = ((F.c : ℂ).re - (1 / 2 : ℂ).re) + 0 := by
      exact congrArg₂ HAdd.hAdd
        (Complex.sub_re (F.c : ℂ) (1 / 2 : ℂ))
        (zetaCompletedExplicitFormula_real_mul_I_re_zero t)
    _ = (F.c - (1 / 2 : ℝ)) + 0 := by
      exact congrArg (fun x : ℝ => x + 0)
        (congrArg₂ HSub.hSub
          (Complex.ofReal_re F.c)
          (Complex.ofReal_re (1 / 2 : ℝ)))
    _ = F.c - (1 / 2 : ℝ) := add_zero (F.c - (1 / 2 : ℝ))

/-- The shifted right affine line has imaginary part `t`. -/
theorem zetaCompletedExplicitFormulaRightCenteredAffineLine_im
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    (zetaCompletedExplicitFormulaRightCenteredAffineLine F t).im = t := by
  calc
    (zetaCompletedExplicitFormulaRightCenteredAffineLine F t).im =
        (((F.c : ℂ) - (1 / 2 : ℂ)) + (t : ℂ) * Complex.I).im := by
      exact congrArg Complex.im
        (zetaCompletedExplicitFormulaRightCenteredAffineLine_eq F t)
    _ = ((F.c : ℂ) - (1 / 2 : ℂ)).im +
          ((t : ℂ) * Complex.I).im := by
      exact Complex.add_im ((F.c : ℂ) - (1 / 2 : ℂ)) ((t : ℂ) * Complex.I)
    _ = ((F.c : ℂ).im - (1 / 2 : ℂ).im) + t := by
      exact congrArg₂ HAdd.hAdd
        (Complex.sub_im (F.c : ℂ) (1 / 2 : ℂ))
        (zetaCompletedExplicitFormula_real_mul_I_im t)
    _ = (0 - 0) + t := by
      exact congrArg (fun x : ℝ => x + t)
        (congrArg₂ HSub.hSub
          (Complex.ofReal_im F.c)
          (Complex.ofReal_im (1 / 2 : ℝ)))
    _ = 0 + t := by
      exact congrArg (fun x : ℝ => x + t) (sub_self (0 : ℝ))
    _ = t := zero_add t

/-- The left affine line has fixed real part `1 - F.c`. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_re
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftAffineLine F t).re =
      (1 : ℝ) - F.c := by
  calc
    (zetaCompletedExplicitFormulaLeftAffineLine F t).re =
        (((1 : ℂ) - (F.c : ℂ)) + (t : ℂ) * Complex.I).re := by
      exact congrArg Complex.re
        (zetaCompletedExplicitFormulaLeftAffineLine_eq F t)
    _ = ((1 : ℂ) - (F.c : ℂ)).re +
          ((t : ℂ) * Complex.I).re := by
      exact Complex.add_re ((1 : ℂ) - (F.c : ℂ)) ((t : ℂ) * Complex.I)
    _ = ((1 : ℂ).re - (F.c : ℂ).re) + 0 := by
      exact congrArg₂ HAdd.hAdd
        (Complex.sub_re (1 : ℂ) (F.c : ℂ))
        (zetaCompletedExplicitFormula_real_mul_I_re_zero t)
    _ = ((1 : ℝ) - F.c) + 0 := by
      exact congrArg (fun x : ℝ => x + 0)
        (congrArg₂ HSub.hSub
          (Complex.ofReal_re (1 : ℝ))
          (Complex.ofReal_re F.c))
    _ = (1 : ℝ) - F.c := add_zero ((1 : ℝ) - F.c)

/-- The left affine line lies strictly in the negative real half-plane. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_re_lt_zero
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftAffineLine F t).re < 0 :=
  Eq.subst
    (motive := fun x : ℝ => x < 0)
    (zetaCompletedExplicitFormulaLeftAffineLine_re F t).symm
    (sub_neg.mpr F.c_gt_one)

/-- The left affine line avoids `0`. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_ne_zero
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaLeftAffineLine F t ≠ 0 := by
  intro hzero
  have hre :
      (zetaCompletedExplicitFormulaLeftAffineLine F t).re = (0 : ℂ).re :=
    congrArg Complex.re hzero
  have hzero_re : (0 : ℂ).re = (0 : ℝ) :=
    Complex.zero_re
  have hline_lt :
      (zetaCompletedExplicitFormulaLeftAffineLine F t).re < 0 :=
    zetaCompletedExplicitFormulaLeftAffineLine_re_lt_zero F t
  have hbad : (0 : ℝ) < 0 :=
    Eq.subst
      (motive := fun x : ℝ => x < 0)
      (hre.trans hzero_re)
      hline_lt
  exact (lt_irrefl (0 : ℝ)) hbad

/-- The left affine line avoids `1`. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_ne_one
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaLeftAffineLine F t ≠ 1 := by
  intro hone
  have hre :
      (zetaCompletedExplicitFormulaLeftAffineLine F t).re = (1 : ℂ).re :=
    congrArg Complex.re hone
  have hone_re : (1 : ℂ).re = (1 : ℝ) :=
    Complex.one_re
  have hline_lt :
      (zetaCompletedExplicitFormulaLeftAffineLine F t).re < 0 :=
    zetaCompletedExplicitFormulaLeftAffineLine_re_lt_zero F t
  have hbad : (1 : ℝ) < 0 :=
    Eq.subst
      (motive := fun x : ℝ => x < 0)
      (hre.trans hone_re)
      hline_lt
  exact (not_lt_of_ge zero_le_one) hbad

/-- Parameter-level regularity condition for the left affine line: its central
height does not meet the completed `Gammaℝ` nonpositive-even locus.  Away from
height `0`, the line misses this locus automatically by imaginary-part
separation. -/
def zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
    (F : ExplicitFormulaContourFamily) : Prop :=
  ∀ n : ℕ,
    zetaCompletedExplicitFormulaLeftAffineLine F 0 ≠
      -(2 * (n : ℂ))

/-- A vertically regular contour family avoids the left affine completed-Gamma
zero locus at central height, hence satisfies the left affine Gamma-regularity
condition used by the whole-line left affine estimates. -/
theorem zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
    (F : ExplicitFormulaVerticallyRegularContourFamily) :
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F.toContourFamily := by
  intro n hn
  let z : ℂ :=
    zetaCompletedExplicitFormulaLeftAffineLine F.toContourFamily 0
  have hpath :
      z =
        zetaCompletedExplicitFormulaLeftPath
          (F.toContourFamily.rectangle 1) 0 := by
    calc
      z =
          zetaCompletedExplicitFormulaLeftAffineLine F.toContourFamily 0 := by
        exact Eq.refl _
      _ = ((1 : ℂ) - (F.toContourFamily.c : ℂ)) +
            (0 : ℝ) * Complex.I := by
        exact zetaCompletedExplicitFormulaLeftAffineLine_eq
          F.toContourFamily 0
      _ = ((1 : ℂ) - (F.toContourFamily.c : ℂ)) + 0 := by
        exact congrArg
          (fun w : ℂ => ((1 : ℂ) - (F.toContourFamily.c : ℂ)) + w)
          (zero_mul Complex.I)
      _ = ((1 : ℂ) - (F.toContourFamily.c : ℂ)) := by
        exact add_zero ((1 : ℂ) - (F.toContourFamily.c : ℂ))
      _ =
          zetaCompletedExplicitFormulaLeftPath
            (F.toContourFamily.rectangle 1) 0 := by
        have hzero :
            zetaCompletedExplicitFormulaLeftPath
              (F.toContourFamily.rectangle 1) 0 =
              1 - (F.toContourFamily.rectangle 1).c :=
          zetaCompletedExplicitFormulaLeftPath_zero
            (F.toContourFamily.rectangle 1)
        have hc :
            ((1 : ℂ) - (F.toContourFamily.c : ℂ)) =
              1 - (F.toContourFamily.rectangle 1).c := by
          exact Eq.refl _
        exact hc.trans hzero.symm
  have hGamma_zero : Gammaℝ z = 0 :=
    Complex.Gammaℝ_eq_zero_iff.mpr ⟨n, hn⟩
  have hsingular : explicitFormulaContourSingularPoint z :=
    Or.inr (Or.inr (Or.inl hGamma_zero))
  have hinterval : (0 : ℝ) ∈ Set.Icc (-(1 : ℝ)) 1 :=
    ⟨neg_nonpos.mpr zero_le_one, zero_le_one⟩
  have hhit :
      (∃ t : ℝ,
        t ∈ Set.Icc (-(1 : ℝ)) 1 ∧
          z =
            zetaCompletedExplicitFormulaRightPath
              (F.toContourFamily.rectangle 1) t) ∨
       (∃ t : ℝ,
        t ∈ Set.Icc (-(1 : ℝ)) 1 ∧
          z =
            zetaCompletedExplicitFormulaLeftPath
              (F.toContourFamily.rectangle 1) t) :=
    Or.inr ⟨0, hinterval, hpath⟩
  exact F.vertical_avoids 1 z hsingular hhit

/-- The left affine line has imaginary part `t`. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_im
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftAffineLine F t).im = t := by
  calc
    (zetaCompletedExplicitFormulaLeftAffineLine F t).im =
        (((1 : ℂ) - (F.c : ℂ)) + (t : ℂ) * Complex.I).im := by
      exact congrArg Complex.im
        (zetaCompletedExplicitFormulaLeftAffineLine_eq F t)
    _ = ((1 : ℂ) - (F.c : ℂ)).im +
          ((t : ℂ) * Complex.I).im := by
      exact Complex.add_im ((1 : ℂ) - (F.c : ℂ)) ((t : ℂ) * Complex.I)
    _ = ((1 : ℂ).im - (F.c : ℂ).im) + t := by
      exact congrArg₂ HAdd.hAdd
        (Complex.sub_im (1 : ℂ) (F.c : ℂ))
        (zetaCompletedExplicitFormula_real_mul_I_im t)
    _ = (0 - 0) + t := by
      exact congrArg (fun x : ℝ => x + t)
        (congrArg₂ HSub.hSub
          (Complex.ofReal_im (1 : ℝ))
          (Complex.ofReal_im F.c))
    _ = 0 + t := by
      exact congrArg (fun x : ℝ => x + t) (sub_self (0 : ℝ))
    _ = t := zero_add t

/-- The left affine line is the functional-equation reflection of the right
affine line with opposite height. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_eq_one_sub_rightAffineLine
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaLeftAffineLine F t =
      1 - zetaCompletedExplicitFormulaRightAffineLine F (-t) := by
  apply Complex.ext
  · have hleft :
        (zetaCompletedExplicitFormulaLeftAffineLine F t).re =
          (1 : ℝ) - F.c :=
      zetaCompletedExplicitFormulaLeftAffineLine_re F t
    have hright :
        (zetaCompletedExplicitFormulaRightAffineLine F (-t)).re = F.c :=
      zetaCompletedExplicitFormulaRightAffineLine_re F (-t)
    have hreflected :
        (1 - zetaCompletedExplicitFormulaRightAffineLine F (-t)).re =
          (1 : ℝ) - F.c := by
      calc
        (1 - zetaCompletedExplicitFormulaRightAffineLine F (-t)).re =
            (1 : ℂ).re -
              (zetaCompletedExplicitFormulaRightAffineLine F (-t)).re := by
          exact Complex.sub_re
            (1 : ℂ)
            (zetaCompletedExplicitFormulaRightAffineLine F (-t))
        _ = (1 : ℝ) -
              (zetaCompletedExplicitFormulaRightAffineLine F (-t)).re := by
          exact congrArg
            (fun x : ℝ =>
              x - (zetaCompletedExplicitFormulaRightAffineLine F (-t)).re)
            (Complex.ofReal_re (1 : ℝ))
        _ = (1 : ℝ) - F.c := by
          exact congrArg (fun x : ℝ => (1 : ℝ) - x) hright
    exact hleft.trans hreflected.symm
  · have hleft :
        (zetaCompletedExplicitFormulaLeftAffineLine F t).im = t :=
      zetaCompletedExplicitFormulaLeftAffineLine_im F t
    have hright :
        (zetaCompletedExplicitFormulaRightAffineLine F (-t)).im = -t :=
      zetaCompletedExplicitFormulaRightAffineLine_im F (-t)
    have hreflected :
        (1 - zetaCompletedExplicitFormulaRightAffineLine F (-t)).im = t := by
      calc
        (1 - zetaCompletedExplicitFormulaRightAffineLine F (-t)).im =
            (1 : ℂ).im -
              (zetaCompletedExplicitFormulaRightAffineLine F (-t)).im := by
          exact Complex.sub_im
            (1 : ℂ)
            (zetaCompletedExplicitFormulaRightAffineLine F (-t))
        _ = (0 : ℝ) -
              (zetaCompletedExplicitFormulaRightAffineLine F (-t)).im := by
          exact congrArg
            (fun x : ℝ =>
              x - (zetaCompletedExplicitFormulaRightAffineLine F (-t)).im)
            (Complex.ofReal_im (1 : ℝ))
        _ = (0 : ℝ) - (-t) := by
          exact congrArg (fun x : ℝ => (0 : ℝ) - x) hright
        _ = -(-t) := zero_sub (-t)
        _ = t := neg_neg t
    exact hleft.trans hreflected.symm

/-- Away from height `0`, the left affine line cannot meet the completed
`Gammaℝ` nonpositive-even locus. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_ne_Gammaℝ_zero_locus_of_ne_zero_height
    (F : ExplicitFormulaContourFamily) {t : ℝ} (ht : t ≠ 0) :
    ∀ n : ℕ,
      zetaCompletedExplicitFormulaLeftAffineLine F t ≠
        -(2 * (n : ℂ)) := by
  intro n hline
  have him :
      (zetaCompletedExplicitFormulaLeftAffineLine F t).im =
        (-(2 * (n : ℂ))).im :=
    congrArg Complex.im hline
  have hline_im :
      (zetaCompletedExplicitFormulaLeftAffineLine F t).im = t :=
    zetaCompletedExplicitFormulaLeftAffineLine_im F t
  have hright_im :
      (-(2 * (n : ℂ))).im = 0 := by
    calc
      (-(2 * (n : ℂ))).im = -((2 * (n : ℂ)).im) := by
        exact Complex.neg_im (2 * (n : ℂ))
      _ = -(((2 : ℂ).re * (n : ℂ).im) +
            ((2 : ℂ).im * (n : ℂ).re)) := by
        exact congrArg Neg.neg (Complex.mul_im (2 : ℂ) (n : ℂ))
      _ = -(((2 : ℝ) * 0) + (0 * (n : ℝ))) := by
        exact congrArg Neg.neg
          (congrArg₂ HAdd.hAdd
            (congrArg₂ HMul.hMul
              (Complex.ofReal_re (2 : ℝ))
              (Complex.ofReal_im (n : ℝ)))
            (congrArg₂ HMul.hMul
              (Complex.ofReal_im (2 : ℝ))
              (Complex.ofReal_re (n : ℝ))))
      _ = -(0 + 0) := by
        exact congrArg Neg.neg
          (congrArg₂ HAdd.hAdd
            (mul_zero (2 : ℝ))
            (zero_mul (n : ℝ)))
      _ = -0 := by
        exact congrArg Neg.neg (zero_add (0 : ℝ))
      _ = 0 := neg_zero
  have ht_zero : t = 0 :=
    hline_im.symm.trans (him.trans hright_im)
  exact ht ht_zero

/-- If the central height avoids the completed `Gammaℝ` nonpositive-even
locus, the entire left affine line avoids it. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_ne_Gammaℝ_zero_locus_of_gammaRegular
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (t : ℝ) :
    ∀ n : ℕ,
      zetaCompletedExplicitFormulaLeftAffineLine F t ≠
        -(2 * (n : ℂ)) := by
  by_cases ht : t = 0
  · intro n
    exact
      Eq.subst
        (motive := fun u : ℝ =>
          zetaCompletedExplicitFormulaLeftAffineLine F u ≠
            -(2 * (n : ℂ)))
        ht.symm
        (hregular n)
  · exact
      zetaCompletedExplicitFormulaLeftAffineLine_ne_Gammaℝ_zero_locus_of_ne_zero_height
        F ht

/-- Under the parameter-level left-line regularity condition, the completed
`Gammaℝ` factor is nonzero on the entire left affine line. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_ne_zero_of_gammaRegular
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (t : ℝ) :
    Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) ≠ 0 := by
  intro hzero
  match Complex.Gammaℝ_eq_zero_iff.mp hzero with
  | ⟨n, hn⟩ =>
      exact
        (zetaCompletedExplicitFormulaLeftAffineLine_ne_Gammaℝ_zero_locus_of_gammaRegular
          F hregular t n)
        hn

/-- Away from central height, the completed `Gammaℝ` factor is nonzero on the
left affine line. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_ne_zero_of_ne_zero_height
    (F : ExplicitFormulaContourFamily) {t : ℝ} (ht : t ≠ 0) :
    Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) ≠ 0 := by
  intro hzero
  match Complex.Gammaℝ_eq_zero_iff.mp hzero with
  | ⟨n, hn⟩ =>
      exact
        (zetaCompletedExplicitFormulaLeftAffineLine_ne_Gammaℝ_zero_locus_of_ne_zero_height
          F ht n)
        hn

/-- Under the parameter-level left-line regularity condition, the half-line
appearing in `Gammaℝ s = π^(-s/2) Γ(s/2)` avoids the ordinary Gamma pole
locus. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_half_ne_Gamma_zero_locus_of_gammaRegular
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (t : ℝ) :
    ∀ n : ℕ,
      zetaCompletedExplicitFormulaLeftAffineLine F t / 2 ≠
        -(n : ℂ) := by
  intro n hhalf
  have hdouble :
      zetaCompletedExplicitFormulaLeftAffineLine F t =
        2 * (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) := by
    exact (mul_div_cancel₀
      (zetaCompletedExplicitFormulaLeftAffineLine F t)
      (show (2 : ℂ) ≠ 0 from two_ne_zero)).symm
  have hline :
      zetaCompletedExplicitFormulaLeftAffineLine F t =
        2 * (-(n : ℂ)) := by
    exact hdouble.trans (congrArg (fun z : ℂ => 2 * z) hhalf)
  have htarget :
      2 * (-(n : ℂ)) = -(2 * (n : ℂ)) := by
    exact (mul_neg (2 : ℂ) (n : ℂ)).trans
      (congrArg Neg.neg (mul_comm (2 : ℂ) (n : ℂ)).symm)
  exact
    (zetaCompletedExplicitFormulaLeftAffineLine_ne_Gammaℝ_zero_locus_of_gammaRegular
      F hregular t n)
      (hline.trans htarget)

/-- Away from central height, the half-line appearing in `Gammaℝ s =
π^(-s/2) Γ(s/2)` avoids the ordinary Gamma pole locus. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_half_ne_Gamma_zero_locus_of_ne_zero_height
    (F : ExplicitFormulaContourFamily) {t : ℝ} (ht : t ≠ 0) :
    ∀ n : ℕ,
      zetaCompletedExplicitFormulaLeftAffineLine F t / 2 ≠
        -(n : ℂ) := by
  intro n hhalf
  have hdouble :
      zetaCompletedExplicitFormulaLeftAffineLine F t =
        2 * (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) := by
    exact (mul_div_cancel₀
      (zetaCompletedExplicitFormulaLeftAffineLine F t)
      (show (2 : ℂ) ≠ 0 from two_ne_zero)).symm
  have hline :
      zetaCompletedExplicitFormulaLeftAffineLine F t =
        2 * (-(n : ℂ)) := by
    exact hdouble.trans (congrArg (fun z : ℂ => 2 * z) hhalf)
  have htarget :
      2 * (-(n : ℂ)) = -(2 * (n : ℂ)) := by
    exact (mul_neg (2 : ℂ) (n : ℂ)).trans
      (congrArg Neg.neg (mul_comm (2 : ℂ) (n : ℂ)).symm)
  exact
    (zetaCompletedExplicitFormulaLeftAffineLine_ne_Gammaℝ_zero_locus_of_ne_zero_height
      F ht n)
      (hline.trans htarget)

/-- The shifted left affine line has fixed real part `1 - F.c - 1/2`. -/
theorem zetaCompletedExplicitFormulaLeftCenteredAffineLine_re
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t).re =
      (1 : ℝ) - F.c - (1 / 2 : ℝ) := by
  calc
    (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t).re =
        (((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ)) +
          (t : ℂ) * Complex.I).re := by
      exact congrArg Complex.re
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq F t)
    _ = (((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ)).re) +
          ((t : ℂ) * Complex.I).re := by
      exact Complex.add_re
        ((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ))
        ((t : ℂ) * Complex.I)
    _ = ((((1 : ℂ) - (F.c : ℂ)).re - (1 / 2 : ℂ).re)) + 0 := by
      exact congrArg₂ HAdd.hAdd
        (Complex.sub_re ((1 : ℂ) - (F.c : ℂ)) (1 / 2 : ℂ))
        (zetaCompletedExplicitFormula_real_mul_I_re_zero t)
    _ = (((1 : ℂ).re - (F.c : ℂ).re) - (1 / 2 : ℂ).re) + 0 := by
      exact congrArg (fun x : ℝ => (x - (1 / 2 : ℂ).re) + 0)
        (Complex.sub_re (1 : ℂ) (F.c : ℂ))
    _ = (((1 : ℝ) - F.c) - (1 / 2 : ℝ)) + 0 := by
      exact congrArg (fun x : ℝ => x + 0)
        (congrArg₂ HSub.hSub
          (congrArg₂ HSub.hSub
            (Complex.ofReal_re (1 : ℝ))
            (Complex.ofReal_re F.c))
          (Complex.ofReal_re (1 / 2 : ℝ)))
    _ = (1 : ℝ) - F.c - (1 / 2 : ℝ) :=
      add_zero ((1 : ℝ) - F.c - (1 / 2 : ℝ))

/-- The shifted left affine line also lies strictly in the negative real
half-plane. -/
theorem zetaCompletedExplicitFormulaLeftCenteredAffineLine_re_lt_zero
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t).re < 0 := by
  have hleft : (1 : ℝ) - F.c < 0 :=
    sub_neg.mpr F.c_gt_one
  have hhalf : (0 : ℝ) < (1 / 2 : ℝ) :=
    one_half_pos
  have hshift_lt :
      (1 : ℝ) - F.c - (1 / 2 : ℝ) < (1 : ℝ) - F.c :=
    sub_lt_self ((1 : ℝ) - F.c) hhalf
  have htarget : (1 : ℝ) - F.c - (1 / 2 : ℝ) < 0 :=
    lt_trans hshift_lt hleft
  exact
    Eq.subst
      (motive := fun x : ℝ => x < 0)
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine_re F t).symm
      htarget

/-- The shifted left affine line has imaginary part `t`. -/
theorem zetaCompletedExplicitFormulaLeftCenteredAffineLine_im
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t).im = t := by
  calc
    (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t).im =
        (((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ)) +
          (t : ℂ) * Complex.I).im := by
      exact congrArg Complex.im
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq F t)
    _ = (((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ)).im) +
          ((t : ℂ) * Complex.I).im := by
      exact Complex.add_im
        ((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ))
        ((t : ℂ) * Complex.I)
    _ = ((((1 : ℂ) - (F.c : ℂ)).im - (1 / 2 : ℂ).im)) + t := by
      exact congrArg₂ HAdd.hAdd
        (Complex.sub_im ((1 : ℂ) - (F.c : ℂ)) (1 / 2 : ℂ))
        (zetaCompletedExplicitFormula_real_mul_I_im t)
    _ = (((1 : ℂ).im - (F.c : ℂ).im) - (1 / 2 : ℂ).im) + t := by
      exact congrArg (fun x : ℝ => (x - (1 / 2 : ℂ).im) + t)
        (Complex.sub_im (1 : ℂ) (F.c : ℂ))
    _ = ((0 - 0) - 0) + t := by
      exact congrArg (fun x : ℝ => x + t)
        (congrArg₂ HSub.hSub
          (congrArg₂ HSub.hSub
            (Complex.ofReal_im (1 : ℝ))
            (Complex.ofReal_im F.c))
          (Complex.ofReal_im (1 / 2 : ℝ)))
    _ = (0 - 0) + t := by
      exact congrArg (fun x : ℝ => x + t) (sub_zero (0 - 0))
    _ = 0 + t := by
      exact congrArg (fun x : ℝ => x + t) (sub_self (0 : ℝ))
    _ = t := zero_add t

/-- The shifted left affine line is the negative of the shifted right affine
line with opposite height. -/
theorem zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq_neg_rightCenteredAffineLine
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaLeftCenteredAffineLine F t =
      - zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t) := by
  apply Complex.ext
  · have hleft :
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t).re =
          (1 : ℝ) - F.c - (1 / 2 : ℝ) :=
      zetaCompletedExplicitFormulaLeftCenteredAffineLine_re F t
    have hright :
        (zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)).re =
          F.c - (1 / 2 : ℝ) :=
      zetaCompletedExplicitFormulaRightCenteredAffineLine_re F (-t)
    have htarget :
        (1 : ℝ) - F.c - (1 / 2 : ℝ) =
          -(F.c - (1 / 2 : ℝ)) := by
      calc
        (1 : ℝ) - F.c - (1 / 2 : ℝ) =
            ((1 : ℝ) - (1 / 2 : ℝ)) - F.c := by
          exact sub_right_comm (1 : ℝ) F.c (1 / 2 : ℝ)
        _ = (1 / 2 : ℝ) - F.c := by
          exact congrArg (fun x : ℝ => x - F.c) (sub_self_div_two (1 : ℝ))
        _ = -(F.c - (1 / 2 : ℝ)) := by
          exact (neg_sub F.c (1 / 2 : ℝ)).symm
    have hneg_re :
        (-zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)).re =
          -(F.c - (1 / 2 : ℝ)) := by
      calc
        (-zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)).re =
            -((zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)).re) := by
          exact Complex.neg_re
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t))
        _ = -(F.c - (1 / 2 : ℝ)) := by
          exact congrArg Neg.neg hright
    exact hleft.trans (htarget.trans hneg_re.symm)
  · have hleft :
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t).im = t :=
      zetaCompletedExplicitFormulaLeftCenteredAffineLine_im F t
    have hright :
        (zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)).im = -t :=
      zetaCompletedExplicitFormulaRightCenteredAffineLine_im F (-t)
    have hneg_im :
        (-zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)).im =
          t := by
      calc
        (-zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)).im =
            -((zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)).im) := by
          exact Complex.neg_im
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t))
        _ = -(-t) := by
          exact congrArg Neg.neg hright
        _ = t := neg_neg t
    exact hleft.trans hneg_im.symm

/-- The left affine line is the shifted-left affine line plus `1 / 2`. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_eq_leftCentered_add_half
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaLeftAffineLine F t =
      zetaCompletedExplicitFormulaLeftCenteredAffineLine F t +
        (1 / 2 : ℂ) := by
  apply Complex.ext
  · have hleft :
        (zetaCompletedExplicitFormulaLeftAffineLine F t).re =
          (1 : ℝ) - F.c :=
      zetaCompletedExplicitFormulaLeftAffineLine_re F t
    have hcenter :
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t).re =
          (1 : ℝ) - F.c - (1 / 2 : ℝ) :=
      zetaCompletedExplicitFormulaLeftCenteredAffineLine_re F t
    have hadd_re :
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t +
            (1 / 2 : ℂ)).re =
          (1 : ℝ) - F.c := by
      calc
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t +
            (1 / 2 : ℂ)).re =
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t).re +
              (1 / 2 : ℂ).re := by
          exact Complex.add_re
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
            (1 / 2 : ℂ)
        _ = ((1 : ℝ) - F.c - (1 / 2 : ℝ)) + (1 / 2 : ℝ) := by
          exact congrArg₂ HAdd.hAdd
            hcenter
            (Complex.ofReal_re (1 / 2 : ℝ))
        _ = (1 : ℝ) - F.c := by
          exact sub_add_cancel ((1 : ℝ) - F.c) (1 / 2 : ℝ)
    exact hleft.trans hadd_re.symm
  · have hleft :
        (zetaCompletedExplicitFormulaLeftAffineLine F t).im = t :=
      zetaCompletedExplicitFormulaLeftAffineLine_im F t
    have hcenter :
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t).im = t :=
      zetaCompletedExplicitFormulaLeftCenteredAffineLine_im F t
    have hadd_im :
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t +
            (1 / 2 : ℂ)).im =
          t := by
      calc
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t +
            (1 / 2 : ℂ)).im =
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t).im +
              (1 / 2 : ℂ).im := by
          exact Complex.add_im
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
            (1 / 2 : ℂ)
        _ = t + 0 := by
          exact congrArg₂ HAdd.hAdd
            hcenter
            (Complex.ofReal_im (1 / 2 : ℝ))
        _ = t := add_zero t
    exact hleft.trans hadd_im.symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
