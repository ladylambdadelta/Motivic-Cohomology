import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.DistributionalClassification.Vanishing
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.KernelDensityDetection

/-!
# Bounded completed-zero distributional classification

This owner begins the explicit-formula classification of bounded completed-zero
coefficient distributions.  The analytic prime and archimedean identification
is built on the linear distributional form isolated here.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

open scoped ENNReal

/-- Probewise annihilation is precisely vanishing of the associated linear
completed-zero distribution. -/
theorem zetaCompletedZeroSideAnnihilatorLinearMap_eq_zero_iff
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    zetaCompletedZeroSideAnnihilatorLinearMap
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary = 0 ↔
      ZetaCompletedZeroSideAnnihilatorVanishes
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary :=
  Iff.intro
    (fun hlinear f =>
      Eq.trans
        (zetaCompletedZeroSideAnnihilatorLinearMap_apply
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f).symm
        (Eq.trans
          (congrArg
            (fun L : ZetaAdmissibleFunction →ₗ[ℂ] ℂ => L f)
            hlinear)
          (Eq.refl 0)))
    (fun hvanishes =>
      LinearMap.ext
        (fun f =>
          Eq.trans
            (zetaCompletedZeroSideAnnihilatorLinearMap_apply
              b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f)
            (Eq.trans (hvanishes f) (Eq.refl 0))))

/-- A nonzero bounded completed-zero coefficient family produces a nonzero
linear distribution precisely when the explicit-formula classification detects
every probewise-vanishing annihilator. -/
theorem zetaCompletedZeroSideAnnihilatorLinearMap_ne_zero_of_nonzero
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hclassification :
      ZetaCompletedZeroSideAnnihilatorVanishes
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary ->
        b = 0)
    (hb : b ≠ 0) :
    zetaCompletedZeroSideAnnihilatorLinearMap
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary ≠ 0 :=
  fun hlinear =>
    hb
      (hclassification
        ((zetaCompletedZeroSideAnnihilatorLinearMap_eq_zero_iff
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary).mp
          hlinear))

/-! The remaining classification theorem is owned here rather than by the
finite-window assembly.  Its proof constructs a damped exponential
distribution from `b`, identifies its modulation orbit with the annihilator,
and applies uniqueness of that distribution to the selected coordinate. -/

/-- If no admissible probe detects a bounded completed-zero coefficient
family, then the associated completed-zero annihilator vanishes probewise. -/
theorem zetaCompletedZeroSideAnnihilatorVanishes_of_no_detecting_probe
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hnoProbe :
      ¬ ∃ f : ZetaAdmissibleFunction,
        zetaCompletedZeroSideAnnihilator
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ≠ 0) :
    ZetaCompletedZeroSideAnnihilatorVanishes
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary :=
  fun f : ZetaAdmissibleFunction =>
    not_ne_iff.mp
      (fun hvalueNonzero =>
        hnoProbe ⟨f, hvalueNonzero⟩)

/-- Kernel density forces every selected coefficient to vanish when no
admissible probe detects the bounded completed-zero annihilator. -/
theorem zetaCompletedZeroSideCoefficient_eq_zero_of_no_detecting_probe
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
  FiniteWindow.zetaCompletedZeroSideCoefficient_eq_zero_of_no_detecting_probe_from_kernelDensity
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    b rho hnoProbe

theorem exists_probe_detecting_nonzero_completedZeroCoefficient
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
  FiniteWindow.exists_probe_detecting_nonzero_completedZeroCoefficient_from_kernelDensity
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    b rho hrho

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
