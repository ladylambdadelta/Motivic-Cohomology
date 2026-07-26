import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceKernelSplit

/-!
# Endpoint trace domination

This file names the positive-trace domination theorem in the completed
Hilbert-source lane and records its equivalent scalar forms.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Endpoint trace domination by the completed positive GNS presentation. -/
def CompletedEndpointTraceDomination
    (f : ZetaAdmissibleFunction) : Prop :=
  (completedWeilEndpointTraceFiber f).gram ≤
    zetaCompletedGNSPositiveBoundaryPresentationScalar f

/-- Endpoint trace domination unfolds to the endpoint-fiber Gram inequality. -/
theorem completedEndpointTraceDomination_iff_endpointFiberGram_le_positivePresentation
    (f : ZetaAdmissibleFunction) :
    CompletedEndpointTraceDomination f ↔
      (completedWeilEndpointTraceFiber f).gram ≤
        zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  Iff.intro
    (fun hdomination => hdomination)
    (fun hbound => hbound)

/-- Endpoint trace domination is equivalent to nonnegativity of the
positive-presentation endpoint remainder. -/
theorem completedEndpointTraceDomination_iff_positivePresentationRemainder_nonnegative
    (f : ZetaAdmissibleFunction) :
    CompletedEndpointTraceDomination f ↔
      0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  Iff.trans
    (completedEndpointTraceDomination_iff_endpointFiberGram_le_positivePresentation
      f)
    (completedEndpointFiberPositivePresentationRemainder_nonnegative_iff_endpointFiberGram_le_positivePresentation
      f).symm

/-- Endpoint trace domination gives nonnegativity of the positive-presentation
endpoint remainder. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_of_endpointTraceDomination
    (f : ZetaAdmissibleFunction)
    (hdomination : CompletedEndpointTraceDomination f) :
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  (completedEndpointTraceDomination_iff_positivePresentationRemainder_nonnegative
    f).mp hdomination

/-- Nonnegativity of the positive-presentation endpoint remainder gives
endpoint trace domination. -/
theorem completedEndpointTraceDomination_of_positivePresentationRemainder_nonnegative
    (f : ZetaAdmissibleFunction)
    (hremainder :
      0 ≤ completedEndpointFiberPositivePresentationRemainder f) :
    CompletedEndpointTraceDomination f :=
  (completedEndpointTraceDomination_iff_positivePresentationRemainder_nonnegative
    f).mpr hremainder

/-- Endpoint trace domination gives nonnegativity of the canonical
Hilbert-source endpoint-kernel remainder. -/
theorem completedBoundaryHilbertSourceEndpointKernelRemainder_source_nonnegative_of_endpointTraceDomination
    (f : ZetaAdmissibleFunction)
    (hdomination : CompletedEndpointTraceDomination f) :
    0 ≤
      completedBoundaryHilbertSourceEndpointKernelRemainder
        (completedBoundaryHilbertSource f) :=
  completedBoundaryHilbertSourceEndpointKernelRemainder_source_nonnegative_of_endpointFiberGram_le_positivePresentation
    f
    ((completedEndpointTraceDomination_iff_endpointFiberGram_le_positivePresentation
      f).mp hdomination)

/-- Canonical Hilbert-source endpoint-kernel nonnegativity gives endpoint
trace domination. -/
theorem completedEndpointTraceDomination_of_sourceEndpointKernelRemainder_nonnegative
    (f : ZetaAdmissibleFunction)
    (hkernel :
      0 ≤
        completedBoundaryHilbertSourceEndpointKernelRemainder
          (completedBoundaryHilbertSource f)) :
    CompletedEndpointTraceDomination f :=
  (completedEndpointTraceDomination_iff_endpointFiberGram_le_positivePresentation
    f).mpr
    ((completedBoundaryHilbertSourceEndpointKernelRemainder_source_nonnegative_iff_endpointFiberGram_le_positivePresentation
      f).mp hkernel)

/-- Endpoint trace domination is equivalent to nonnegativity of the canonical
Hilbert-source endpoint-kernel remainder. -/
theorem completedEndpointTraceDomination_iff_sourceEndpointKernelRemainder_nonnegative
    (f : ZetaAdmissibleFunction) :
    CompletedEndpointTraceDomination f ↔
      0 ≤
        completedBoundaryHilbertSourceEndpointKernelRemainder
          (completedBoundaryHilbertSource f) :=
  Iff.intro
    (fun hdomination =>
      completedBoundaryHilbertSourceEndpointKernelRemainder_source_nonnegative_of_endpointTraceDomination
        f hdomination)
    (fun hkernel =>
      completedEndpointTraceDomination_of_sourceEndpointKernelRemainder_nonnegative
        f hkernel)

/-- Nonnegativity of the archimedean/correction endpoint residual gives
endpoint trace domination. -/
theorem completedEndpointTraceDomination_of_archCorrectionRemainder_nonnegative
    (f : ZetaAdmissibleFunction)
    (archCorrectionRemainderNonnegative :
      0 ≤ completedEndpointFiberArchCorrectionRemainder f) :
    CompletedEndpointTraceDomination f :=
  completedEndpointTraceDomination_of_positivePresentationRemainder_nonnegative
    f
    (completedEndpointFiberPositivePresentationRemainder_nonnegative_of_archCorrectionRemainder
      f archCorrectionRemainderNonnegative)

/-- The explicit centered-packet endpoint inequality gives endpoint trace
domination. -/
theorem completedEndpointTraceDomination_of_endpointPhiNorms_le_centeredPacketGrams
    (f : ZetaAdmissibleFunction)
    (endpointPhiDomination :
      Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) ≤
        ZetaHermitianPacketEnsemble.coordinateGram
            (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
          ZetaHermitianPacketEnsemble.coordinateGram
            ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
              zetaCompletedExplicitFormulaPhi f 0)) :
    CompletedEndpointTraceDomination f :=
  completedEndpointTraceDomination_of_archCorrectionRemainder_nonnegative
    f
    (completedEndpointFiberArchCorrectionRemainder_nonnegative_of_endpointPhiNorms_le_centeredPacketGrams
      f endpointPhiDomination)

/-- Physical endpoint absorption gives endpoint domination after identifying
the physical boundary scalar with the positive GNS presentation. -/
theorem completedEndpointTraceDomination_of_boundary_eq_positivePresentation_absorbedPhysical
    (f : ZetaAdmissibleFunction)
    (boundaryToPositive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f)
    (absorbedPhysical :
      0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f) :
    CompletedEndpointTraceDomination f :=
  let endpointDebtBound :
      (zetaCompletedEndpointCorrectionPacket f).diagonalDebt ≤
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    (completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_iff_diagonalDebt_le_boundary
      f).mp absorbedPhysical
  let endpointFiberBound :
      (completedWeilEndpointTraceFiber f).gram ≤
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))
      (completedWeilEndpointTraceFiber_gram_eq_diagonalDebt f).symm
      endpointDebtBound
  let endpointPositiveBound :
      (completedWeilEndpointTraceFiber f).gram ≤
        zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
    Eq.subst
      (motive := fun value : ℝ =>
        (completedWeilEndpointTraceFiber f).gram ≤ value)
      boundaryToPositive
      endpointFiberBound
  (completedEndpointTraceDomination_iff_endpointFiberGram_le_positivePresentation
    f).mpr endpointPositiveBound

/-- Under physical/positive scalar identification, endpoint domination is
equivalent to endpoint absorption of the physical boundary. -/
theorem completedEndpointTraceDomination_iff_absorbedPhysical_of_boundary_eq_positivePresentation
    (f : ZetaAdmissibleFunction)
    (boundaryToPositive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    CompletedEndpointTraceDomination f ↔
      0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f :=
  Iff.intro
    (fun hdomination =>
      let endpointPositiveBound :
        (completedWeilEndpointTraceFiber f).gram ≤
          zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
        (completedEndpointTraceDomination_iff_endpointFiberGram_le_positivePresentation
          f).mp hdomination
      let endpointBoundaryBound :
        (completedWeilEndpointTraceFiber f).gram ≤
          Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
        Eq.subst
          (motive := fun value : ℝ =>
            (completedWeilEndpointTraceFiber f).gram ≤ value)
          boundaryToPositive.symm
          endpointPositiveBound
      (completedWeilEndpointTraceRemainder_nonnegative_iff_absorbedPhysical
        f).mp
        ((completedWeilEndpointTraceRemainder_nonnegative_iff_endpointFiberGram_le_boundary
          f).mpr endpointBoundaryBound))
    (fun absorbedPhysical =>
      completedEndpointTraceDomination_of_boundary_eq_positivePresentation_absorbedPhysical
        f boundaryToPositive absorbedPhysical)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
