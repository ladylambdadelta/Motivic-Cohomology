import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointFiniteBesselParts.SquareEnergyDebtFrame
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointFiniteBesselParts.EndpointVectorRealization

/-!
# Endpoint finite Bessel compression

This file assembles the finite endpoint Bessel compression theorem from the
positive trace-matrix Schur-complement owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The finite renormalized boundary window is the finite positive square
energy after subtracting the finite prime diagonal debt. -/
theorem finitePositiveRenormalizedBoundaryWindow_eq_squareEnergy_sub_primeDiagonalDebt
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePositiveRenormalizedBoundaryWindow N f =
      finitePositiveSquareEnergyWindow N f - zetaPrimeDiagonalDebt N f :=
  finitePositiveRenormalizedBoundaryWindow_eq_squareEnergy_sub_primeDiagonalDebt_traceFrame
    N f

/-- The finite Bessel Schur remainder is the same scalar as the finite
renormalized trace residual window. -/
theorem completedEndpointFiniteBesselSchurRemainder_eq_renormalizedTraceResidualWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedEndpointFiniteBesselSchurRemainder N f =
      completedEndpointFiniteRenormalizedTraceResidualWindow N f :=
  Eq.refl (completedEndpointFiniteBesselSchurRemainder N f)

/-- The finite endpoint Bessel Schur remainder is the finite prime
off-diagonal channel plus the non-prime endpoint residual. -/
theorem completedEndpointFiniteBesselSchurRemainder_eq_primeOffDiagonal_add_nonPrimeResidual
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedEndpointFiniteBesselSchurRemainder N f =
      zetaPrimeOffDiagonalChannel N f +
        completedEndpointNonPrimeTraceResidual f :=
  Eq.trans
    (completedEndpointFiniteBesselSchurRemainder_eq_renormalizedTraceResidualWindow
      N f)
    (completedEndpointFiniteRenormalizedTraceResidualWindow_eq_primeOffDiagonal_add_nonPrimeResidual
      N f)

/-- Finite Bessel compression is equivalent to nonnegativity of its Schur
remainder. -/
theorem completedEndpointFiniteBesselCompression_iff_schurRemainder_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    CompletedEndpointFiniteBesselCompression N f ↔
      0 ≤ completedEndpointFiniteBesselSchurRemainder N f :=
  Iff.intro
    (fun hcompression =>
      sub_nonneg.mpr hcompression)
    (fun hschur =>
      sub_nonneg.mp hschur)

/-- Eventual finite Schur-complement nonnegativity gives eventual finite
trace-compression exhaustion. -/
theorem completedEndpointFiniteTraceCompressionExhaustion_of_schurComplementExhaustion
    (f : ZetaAdmissibleFunction)
    (hschur : CompletedEndpointFiniteSchurComplementExhaustion f) :
    CompletedEndpointFiniteTraceCompressionExhaustion f :=
  hschur.mono
    (fun N hN =>
      (completedEndpointFiniteBesselCompression_iff_schurRemainder_nonnegative
        N f).mpr hN)

/-- Eventual finite positive trace-matrix Schur compression gives eventual
finite Schur-complement nonnegativity. -/
theorem completedEndpointFiniteSchurComplementExhaustion_of_positiveTraceMatrixSchurCompression
    (f : ZetaAdmissibleFunction)
    (hmatrix :
      ∀ᶠ N in atTop,
        CompletedEndpointFinitePositiveTraceMatrixSchurCompression N f) :
    CompletedEndpointFiniteSchurComplementExhaustion f :=
  hmatrix

/-- Source finite endpoint Schur-complement exhaustion. -/
theorem completedEndpointFiniteSchurComplementExhaustion_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    CompletedEndpointFiniteSchurComplementExhaustion f :=
  completedEndpointFiniteSchurComplementExhaustion_of_positiveTraceMatrixSchurCompression
    f
    (completedEndpointFinitePositiveTraceMatrixSchurCompression_eventually_source
      f
      (completedEndpointFinitePositiveTraceMatrixEndpointVectorRealization_eventually_source
        f D hnonPrime))

/-- Source finite endpoint trace-compression exhaustion. -/
theorem completedEndpointFiniteTraceCompressionExhaustion_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    CompletedEndpointFiniteTraceCompressionExhaustion f :=
  completedEndpointFiniteTraceCompressionExhaustion_of_schurComplementExhaustion
    f
    (completedEndpointFiniteSchurComplementExhaustion_source f D hnonPrime)

/-- Eventual source nonnegativity of the finite endpoint Bessel Schur remainder.

This is the finite trace-compression exhaustion statement: after the cutoff has
captured the endpoint reconstruction data, the visible endpoint trace fiber is a
finite compression of the renormalized positive boundary window. -/
theorem completedEndpointFiniteBesselSchurRemainder_eventually_nonnegative_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    ∀ᶠ N in atTop,
      0 ≤ completedEndpointFiniteBesselSchurRemainder N f :=
  completedEndpointFiniteSchurComplementExhaustion_source f D hnonPrime

/-- Source finite endpoint Bessel compression, packaged eventually in the
cutoff filter. -/
theorem completedEndpointFiniteBesselCompression_eventually_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    ∀ᶠ N in atTop, CompletedEndpointFiniteBesselCompression N f :=
  completedEndpointFiniteTraceCompressionExhaustion_source f D hnonPrime

/-- Finite endpoint Bessel compression passes to the completed boundary trace
under finite-window convergence. -/
theorem completedEndpointTraceFiber_gram_le_boundaryChannel_of_finiteBesselCompression
    (f : ZetaAdmissibleFunction)
    (finiteCompression :
      ∀ᶠ N in atTop, CompletedEndpointFiniteBesselCompression N f) :
    (completedWeilEndpointTraceFiber f).gram ≤
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
  let hlimit :
      Tendsto
        (fun N : ℕ => finitePositiveRenormalizedBoundaryWindow N f)
        atTop
        (𝓝 (Complex.re
          (completedBoundaryChannel (convolutionAutocorrelation f)))) :=
    finitePositiveRenormalizedBoundaryWindow_tendsto_boundaryChannel f
  ge_of_tendsto
    hlimit
    finiteCompression

/-- Source endpoint trace-fiber domination by the completed physical boundary
trace, obtained as the limit of finite endpoint Bessel compression. -/
theorem completedEndpointTraceFiber_gram_le_boundaryChannel_finiteBessel_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    (completedWeilEndpointTraceFiber f).gram ≤
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
  completedEndpointTraceFiber_gram_le_boundaryChannel_of_finiteBesselCompression
    f
    (completedEndpointFiniteBesselCompression_eventually_source
      f D hnonPrime)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
