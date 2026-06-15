import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.Owner

/-!
# Zero-tail tomography for completed boundary Hilbert sources

This file owns the zero-tail quotient API for completed Hilbert sources.  It is downstream
from both the Hilbert-source owner and the zero-tail owner, so neither primitive owner imports
the other.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Zero-tail tomography equivalence for completed Hilbert sources.

This is the quotient relation appropriate for zero-tail descent: two sources are equivalent
when every finite completed-zero tail cut has the same real absolute tail value on their
analytic seeds. It is intentionally separate from scalar-only GNS tomography. -/
def CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent
    (X Y : CompletedBoundaryHilbertSource) : Prop :=
  ∀ S : Finset ℂ,
    |Complex.re (zetaZeroTail S X.seed)| =
      |Complex.re (zetaZeroTail S Y.seed)|

/-- Spectral tomography equivalence for completed Hilbert sources.

This is the raw probe/spectral version of tomography: the analytic seeds have the same
spectral transform at every complex spectral parameter. -/
def CompletedBoundaryHilbertSource.SpectrallyTomographicallyEquivalent
    (X Y : CompletedBoundaryHilbertSource) : Prop :=
  ∀ z : ℂ, zetaSpectralEval X.seed z = zetaSpectralEval Y.seed z

/-- Spectral tomography identifies every completed-zero side contribution. -/
theorem zetaZeroSideContribution_eq_of_spectralTomography
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.SpectrallyTomographicallyEquivalent X Y)
    (ρ : ℂ) :
    zetaZeroSideContribution ρ X.seed =
      zetaZeroSideContribution ρ Y.seed := by
  unfold zetaZeroSideContribution
  exact congrArg
    (fun w : ℂ => - (zetaZeroMultiplicity ρ : ℂ) * w)
    (hXY (zetaCenteredZero ρ))

/-- Spectral tomography identifies every completed zero-tail functional. -/
theorem zetaZeroTail_eq_of_spectralTomography
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.SpectrallyTomographicallyEquivalent X Y)
    (S : Finset ℂ) :
    zetaZeroTail S X.seed = zetaZeroTail S Y.seed := by
  unfold zetaZeroTail
  exact tsum_congr
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
      zetaZeroSideContribution_eq_of_spectralTomography hXY (ρ : ℂ))

/-- Spectral tomography descends to zero-tail tomography. -/
theorem CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.of_spectralTomography
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.SpectrallyTomographicallyEquivalent X Y) :
    CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent X Y := by
  intro S
  exact congrArg (fun w : ℂ => |Complex.re w|)
    (zetaZeroTail_eq_of_spectralTomography hXY S)

/-- Zero-tail tomography equivalence is reflexive. -/
theorem CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.refl
    (X : CompletedBoundaryHilbertSource) :
    CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent X X := by
  intro S
  rfl

/-- Zero-tail tomography equivalence is symmetric. -/
theorem CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.symm
    {X Y : CompletedBoundaryHilbertSource}
    (h :
      CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent X Y) :
    CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent Y X := by
  intro S
  exact (h S).symm

/-- Zero-tail tomography equivalence is transitive. -/
theorem CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.trans
    {X Y Z : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent X Y)
    (hYZ :
      CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent Y Z) :
    CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent X Z := by
  intro S
  exact (hXY S).trans (hYZ S)

/-- The completed zero-tail quotient relation on Hilbert-source representatives. -/
def completedBoundaryHilbertSourceZeroTailTomographySetoid :
    Setoid CompletedBoundaryHilbertSource where
  r := CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent
  iseqv := by
    constructor
    · intro X
      exact CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.refl X
    · intro X Y hXY
      exact CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.symm hXY
    · intro X Y Z hXY hYZ
      exact CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.trans hXY hYZ

/-- The completed zero-tail ordered-heart quotient: Hilbert sources modulo zero-tail
tomography. -/
abbrev CompletedBoundaryZeroTailOrderedHeartClass :=
  Quotient completedBoundaryHilbertSourceZeroTailTomographySetoid

/-- The quotient class of a completed Hilbert-source representative in the zero-tail
ordered-heart quotient. -/
def completedBoundaryZeroTailOrderedHeartClass
    (X : CompletedBoundaryHilbertSource) :
    CompletedBoundaryZeroTailOrderedHeartClass :=
  Quotient.mk completedBoundaryHilbertSourceZeroTailTomographySetoid X

/-- Zero-tail-tomographically equivalent representatives define the same zero-tail
ordered-heart class. -/
theorem completedBoundaryZeroTailOrderedHeartClass_eq_of_zeroTailTomography
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent X Y) :
    completedBoundaryZeroTailOrderedHeartClass X =
      completedBoundaryZeroTailOrderedHeartClass Y := by
  exact Quotient.sound hXY

/-- Spectral tomography identifies the zero-tail ordered-heart quotient class. -/
theorem completedBoundaryZeroTailOrderedHeartClass_eq_of_spectralTomography
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.SpectrallyTomographicallyEquivalent X Y) :
    completedBoundaryZeroTailOrderedHeartClass X =
      completedBoundaryZeroTailOrderedHeartClass Y := by
  exact completedBoundaryZeroTailOrderedHeartClass_eq_of_zeroTailTomography
    (CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.of_spectralTomography
      hXY)

/-- Contour/channel tomography identifies the zero-tail ordered-heart quotient class.

This is the quotient-level forgetting theorem for scheduled contour realizations: once the
chosen realization supplies the same spectral/channel evaluations for two Hilbert sources,
the zero-tail ordered-heart class no longer depends on the chosen contour representative. -/
theorem completedBoundaryZeroTailOrderedHeartClass_eq_of_contourChannelTomography
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      ∀ z : ℂ, zetaSpectralEval X.seed z = zetaSpectralEval Y.seed z) :
    completedBoundaryZeroTailOrderedHeartClass X =
      completedBoundaryZeroTailOrderedHeartClass Y := by
  exact completedBoundaryZeroTailOrderedHeartClass_eq_of_spectralTomography hXY

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
