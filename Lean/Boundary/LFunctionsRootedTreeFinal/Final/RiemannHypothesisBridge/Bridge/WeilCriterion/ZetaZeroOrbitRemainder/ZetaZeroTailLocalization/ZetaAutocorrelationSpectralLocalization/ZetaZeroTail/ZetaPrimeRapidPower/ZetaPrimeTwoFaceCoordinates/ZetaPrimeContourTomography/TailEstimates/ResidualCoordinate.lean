import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.ResidualCoordinateSource
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.Density.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.BoundedCoefficientDirect

/-!
# Completed prime residual coordinates

This file owns the coordinate-functional representation of the completed prime
trace residual.  The source contour/time transport facts are owned by
`ResidualCoordinateSource`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Density eliminates any continuous completed-zero coordinate functional that
vanishes on the admissible probe-coordinate image. -/
theorem completedZeroCoordinateContinuousLinearMap_eq_zero_of_coordinateDensity
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ)
    (hvanishes :
      ∀ g : ZetaAdmissibleFunction,
        L
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite
            hpartialLeft hcompactBoundary g) = 0)
    (hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary = Set.univ) :
    L = 0 :=
  let hclosed : IsClosed (L ⁻¹' ({0} : Set ℂ)) :=
    isClosed_singleton.preimage L.continuous
  let himage :
      zetaCompletedZeroSideCoordinateL1Image
          hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary ⊆
        L ⁻¹' ({0} : Set ℂ) :=
    fun x hx =>
      match hx with
      | ⟨g, hg⟩ =>
        Eq.subst
          (motive := fun y : ZetaCompletedZeroCoordinateL1 =>
            L y = 0)
          hg
          (hvanishes g)
  let hclosure :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary ⊆
        L ⁻¹' ({0} : Set ℂ) :=
    closure_minimal himage hclosed
  ContinuousLinearMap.ext
    (fun x =>
      let hx :
          x ∈
            zetaCompletedZeroSideCoordinateL1Closure
              hbranch hpartialOneTwo hcompactOneTwo hfinite
              hpartialLeft hcompactBoundary :=
        Eq.subst
          (motive := fun carrier : Set
            ZetaCompletedZeroCoordinateL1 =>
              x ∈ carrier)
          hdense.symm
          (Set.mem_univ x)
      let hLx : L x = 0 := hclosure hx
      hLx)

/-- The completed prime trace residual at a fixed probe is represented by the
diagonal-debt bounded completed-zero coefficient supplied by the diagonal
residual owner. -/
theorem exists_completedPrimeTraceResidualDistribution_boundedCoordinateCoefficient_at
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    ∃ b : ZetaCompletedZeroCoordinateLInfinity,
      ZetaCompletedZeroSideAnnihilatorVanishes
        b hbranch hpartialOneTwo hcompactOneTwo hfinite
        hpartialLeft hcompactBoundary ∧
      completedPrimeTraceResidualComplexScalar f =
        zetaCompletedZeroSideAnnihilator
          b hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary f :=
  match
    exists_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_boundedCoordinateCoefficient_source_primitive
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
      hcompactBoundary f D hmajorant hcoordinateZero
  with
  | ⟨b, hvanishes, hdiagonal⟩ =>
      let hresidual :
          ((Complex.re
              (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
    ℂ) =
            completedPrimeTraceResidualComplexScalar f :=
        diagonalDebtCoordinateResidual_eq_completedPrimeTraceResidual_source f
          D hmajorant hcoordinateZero
      let hrepresents :
          completedPrimeTraceResidualComplexScalar f =
            zetaCompletedZeroSideAnnihilator
              b hbranch hpartialOneTwo hcompactOneTwo hfinite
              hpartialLeft hcompactBoundary f :=
        Eq.trans hresidual.symm hdiagonal
      ⟨b, hvanishes, hrepresents⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
