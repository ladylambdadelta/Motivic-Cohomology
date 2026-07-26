import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.Detection
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.CoordinateDensity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.Owner

/-!
# Kernel-density finite-window detection

This file connects the abstract dense-coordinate finite-window detector to the
kernel-density owner theorem.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace FiniteWindow

open scoped ENNReal

theorem zetaCompletedZeroSideCoefficient_eq_zero_of_no_detecting_probe_from_kernelDensity
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hnoProbe :
      ¬ ∃ f : ZetaAdmissibleFunction,
        zetaCompletedZeroSideAnnihilator
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ≠ 0) :
    b rho = 0 :=
  let hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =
        Set.univ :=
    zetaCompletedZeroSideCoordinateL1Closure_eq_univ_of_kernelDensity
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  zetaCompletedZeroSideCoefficient_eq_zero_of_no_detecting_probe_of_coordinateDensity
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    b rho hnoProbe hdense

theorem zetaCompletedZeroSideCoordinateL1Single_mem_closure_of_kernelDensity
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (rho : ZetaCompletedZeroCoordinate) :
    (lp.single (1 : ENNReal) rho (1 : ℂ) :
      lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) ∈
      closure
        (Set.range
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)) :=
  let hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =
        Set.univ :=
    zetaCompletedZeroSideCoordinateL1Closure_eq_univ_of_kernelDensity
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  zetaCompletedZeroSideCoordinateL1Single_mem_closure_of_coordinateDensity
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    rho hdense

theorem exists_probe_detecting_nonzero_completedZeroCoefficient_from_kernelDensity
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0) :
    ∃ f : ZetaAdmissibleFunction,
      zetaCompletedZeroSideAnnihilator
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ≠ 0 :=
  let hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =
        Set.univ :=
    zetaCompletedZeroSideCoordinateL1Closure_eq_univ_of_kernelDensity
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  exists_probe_detecting_nonzero_completedZeroCoefficient_of_coordinateDensity
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    b rho hrho hdense

theorem exists_zetaCompletedZeroSideAnnihilator_finiteWindow_dominates_complementaryTail_from_kernelDensity
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0) :
    ∃ (S : Finset ℂ)
      (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
      (f : ZetaAdmissibleFunction),
      (rho : ℂ) ∈ S ∧
        norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) <
          norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
  let hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =
        Set.univ :=
    zetaCompletedZeroSideCoordinateL1Closure_eq_univ_of_kernelDensity
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  exists_zetaCompletedZeroSideAnnihilator_finiteWindow_dominates_complementaryTail_of_coordinateDensity
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    b rho hrho hdense

end FiniteWindow
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
