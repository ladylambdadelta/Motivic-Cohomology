import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.BoundaryCancellation

/-!
# Boundary explicit-formula analytic core

This file fixes the analytic vocabulary used by the completed Guinand--Weil
route:

* the involution `f†`,
* the autocorrelation kernel `g_f`,
* the spectral transform `Φ_f`,
* the completed zeta logarithmic derivative integrand,
* and the named prime / archimedean / correction pieces.

The file is intentionally definitional. The contour, residue, and decay
arguments will consume these owner-level objects.
-/

/-! This owner part contains the boundary contributions and channel kernel. -/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed prime-power explicit-formula contribution indexed by genuine prime-power
coordinates.  This is the owner real-side prime distribution: prime powers sample the
time/log-side boundary value.  Contour and vertical-line arguments may realize this
distribution spectrally, but the owner object is not a pointwise Laplace sample. -/
noncomputable def zetaCompletedExplicitFormulaPrimePowerContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  ((∑' ι : ZetaPrimePowerIndex,
    -(ZetaPrimePowerIndex.weight ι *
      Complex.re
        (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι) +
          star (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι))))) : ℂ)

/-- The prime contribution in the completed explicit formula.

This public owner definition is the completed time/log-side prime-power distribution, not the
finite display support and not the contour-side spectral-sample presentation. -/
noncomputable def zetaCompletedExplicitFormulaPrimeContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimePowerContribution f

/-- The completed prime-power owner contribution is the public prime contribution. -/
theorem zetaCompletedExplicitFormulaPrimePowerContribution_eq_primeContribution
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimePowerContribution f =
      zetaCompletedExplicitFormulaPrimeContribution f := by
  rfl

/-- The archimedean contribution in the completed explicit formula. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  (2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0

/-- The correction contribution in the completed explicit formula. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) *
    zetaCompletedExplicitFormulaPhi f 0

/-- The prime contribution unfolds to the completed prime-power owner distribution. -/
theorem zetaCompletedExplicitFormulaPrimeContribution_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeContribution f =
      zetaCompletedExplicitFormulaPrimePowerContribution f := by
  rfl

/-- The archimedean contribution is the spectral value at the self-paired basepoint. -/
theorem zetaCompletedExplicitFormulaArchimedeanContribution_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanContribution f =
      (2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0 := by
  rfl

/-- The correction contribution is the centered pole correction at the basepoint. -/
theorem zetaCompletedExplicitFormulaCorrectionContribution_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionContribution f =
      (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) *
        zetaCompletedExplicitFormulaPhi f 0 := by
  rfl

/-- The centered correction contribution vanishes on the zero admissible probe. -/
theorem zetaCompletedExplicitFormulaCorrectionContribution_zero :
    zetaCompletedExplicitFormulaCorrectionContribution
        (0 : ZetaAdmissibleFunction) = 0 := by
  calc
    zetaCompletedExplicitFormulaCorrectionContribution
        (0 : ZetaAdmissibleFunction) =
        (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) *
          zetaCompletedExplicitFormulaPhi (0 : ZetaAdmissibleFunction) 0 := by
      exact zetaCompletedExplicitFormulaCorrectionContribution_eq 0
    _ =
        (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) * 0 := by
      exact congrArg
        (fun z : ℂ =>
          (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) * z)
        (zetaCompletedExplicitFormulaPhi_zero 0)
    _ = 0 := by
      exact mul_zero _

/-- The combined completed explicit-formula boundary sum. -/
noncomputable def zetaCompletedExplicitFormulaBoundarySumCore
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeContribution f +
    zetaCompletedExplicitFormulaArchimedeanContribution f +
    zetaCompletedExplicitFormulaCorrectionContribution f

/-- The analytic core boundary sum is the sum of the three named pieces. -/
theorem zetaCompletedExplicitFormulaBoundarySumCore_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumCore f =
      zetaCompletedExplicitFormulaPrimeContribution f +
        zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionContribution f := by
  exact Eq.refl _

/-- The completed explicit-formula boundary channel. -/
def completedBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaBoundarySumCore g

/-- The prime channel of the completed boundary functional. -/
def primeBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeContribution g

/-- The opposite prime face of the completed boundary functional.  This is the negative
prime-power face paired with the positive prime channel by dagger. -/
def oppositePrimeBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    -((zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
      zetaCompletedExplicitFormulaPhi g (-(zetaPrimePacketCenter ℓ.1 ℓ.2 : ℂ)))

/-- The archimedean channel of the completed boundary functional. -/
def archimedeanBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanContribution g

/-- The pole channel in the current centered completed-zeta normalization. -/
def poleBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionContribution g

/-- The residual completion channel after the explicit archimedean and pole channels have been
separated.  In the current normalization this channel is zero; if the gamma normalization is
split further, this is the owner slot to refine. -/
def completionBoundaryChannel (_g : ZetaAdmissibleFunction) : ℂ :=
  0

/-- The opposite completed boundary channel.  The prime face is reflected to the negative
prime-power face; the self-paired archimedean and correction faces remain at the basepoint. -/
def oppositeBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  oppositePrimeBoundaryChannel g +
    archimedeanBoundaryChannel g +
    poleBoundaryChannel g +
    completionBoundaryChannel g

/-- The completed boundary channel unfolds to the analytic boundary sum core. -/
theorem completedBoundaryChannel_unfold
    (g : ZetaAdmissibleFunction) :
    completedBoundaryChannel g =
      zetaCompletedExplicitFormulaBoundarySumCore g := by
  rfl

/-- The prime boundary channel unfolds to the prime contribution. -/
theorem primeBoundaryChannel_unfold
    (g : ZetaAdmissibleFunction) :
    primeBoundaryChannel g =
      zetaCompletedExplicitFormulaPrimeContribution g := by
  rfl

/-- The archimedean boundary channel unfolds to the archimedean contribution. -/
theorem archimedeanBoundaryChannel_unfold
    (g : ZetaAdmissibleFunction) :
    archimedeanBoundaryChannel g =
      zetaCompletedExplicitFormulaArchimedeanContribution g := by
  rfl

/-- The pole boundary channel unfolds to the correction contribution. -/
theorem poleBoundaryChannel_unfold
    (g : ZetaAdmissibleFunction) :
    poleBoundaryChannel g =
      zetaCompletedExplicitFormulaCorrectionContribution g := by
  rfl

/-- The residual completion channel is zero in the current normalization. -/
theorem completionBoundaryChannel_unfold
    (g : ZetaAdmissibleFunction) :
    completionBoundaryChannel g = 0 := by
  rfl

/-- The local channel decomposition of the completed boundary functional. -/
theorem completedBoundaryChannel_eq_prime_add_archimedean_add_pole_add_completion
    (g : ZetaAdmissibleFunction) :
    completedBoundaryChannel g =
      primeBoundaryChannel g +
        archimedeanBoundaryChannel g +
        poleBoundaryChannel g +
        completionBoundaryChannel g := by
  calc
    completedBoundaryChannel g =
        zetaCompletedExplicitFormulaBoundarySumCore g :=
      completedBoundaryChannel_unfold g
    _ =
        zetaCompletedExplicitFormulaPrimeContribution g +
          zetaCompletedExplicitFormulaArchimedeanContribution g +
          zetaCompletedExplicitFormulaCorrectionContribution g :=
      zetaCompletedExplicitFormulaBoundarySumCore_eq g
    _ =
        zetaCompletedExplicitFormulaPrimeContribution g +
          zetaCompletedExplicitFormulaArchimedeanContribution g +
          zetaCompletedExplicitFormulaCorrectionContribution g + 0 := by
      exact (add_zero _).symm
    _ =
        primeBoundaryChannel g +
          archimedeanBoundaryChannel g +
          poleBoundaryChannel g +
          completionBoundaryChannel g := by
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ HAdd.hAdd
          (congrArg₂ HAdd.hAdd
            (primeBoundaryChannel_unfold g).symm
            (archimedeanBoundaryChannel_unfold g).symm)
          (poleBoundaryChannel_unfold g).symm)
        (completionBoundaryChannel_unfold g).symm

/-- The Hermitian kernel assembled from the completed boundary channels on the convolution
pairing algebra. -/
def completedHermitianKernel
    (f h : ZetaAdmissibleFunction) : ℂ :=
  primeBoundaryChannel (convolutionPair f h) +
    archimedeanBoundaryChannel (convolutionPair f h) +
    poleBoundaryChannel (convolutionPair f h) +
    completionBoundaryChannel (convolutionPair f h)

/-- The completed boundary channel of a convolution pair is the completed Hermitian kernel. -/
theorem completedBoundaryChannel_convolutionPair_eq_kernel
    (f h : ZetaAdmissibleFunction) :
    completedBoundaryChannel (convolutionPair f h) =
      completedHermitianKernel f h := by
  exact completedBoundaryChannel_eq_prime_add_archimedean_add_pole_add_completion
    (convolutionPair f h)

/-- The diagonal convolution-pair transport specializes to the completed autocorrelation
boundary channel. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_eq_kernel_diagonal
    (f : ZetaAdmissibleFunction) :
    completedBoundaryChannel (convolutionAutocorrelation f) =
      completedHermitianKernel f f := by
  exact
    Eq.subst
      (motive := fun g : ZetaAdmissibleFunction =>
        completedBoundaryChannel g = completedHermitianKernel f f)
      (convolutionPair_self f)
      (completedBoundaryChannel_convolutionPair_eq_kernel f f)


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
