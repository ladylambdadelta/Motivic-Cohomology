import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.Presentation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.TailSummability.Owner

/-!
# Weighted completed-zero tail norm

The quantitative separation lane uses the complementary `l1` mass of the
completed-zero side coordinates.  This norm directly dominates both the
complex zero tail and its real absolute-value projection.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace QuantitativeSeparation

noncomputable def completedZeroComplementL1Norm
    (S : Finset ℂ)
    (f : ZetaAdmissibleFunction) : ℝ :=
  ∑' rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S},
    ‖zetaZeroSideContribution (rho : ℂ) f‖

/-- The nested subtype produced by restriction is canonically equivalent to
the flat completed-zero complement subtype used by the tail norm. -/
def completedZeroComplementIndexEquiv
    (S : Finset ℂ) :
    {rho : {rho : ℂ // ZetaCompletedZero rho} // (rho : ℂ) ∉ S} ≃
      {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} :=
  Equiv.subtypeSubtypeEquivSubtypeInter
    (fun rho : ℂ => ZetaCompletedZero rho)
    (fun rho : ℂ => rho ∉ S)

theorem summable_completedZeroComplementL1Norm
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
        ‖zetaZeroSideContribution (rho : ℂ) f‖) :=
  let hglobal :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          ‖zetaZeroSideContribution (rho : ℂ) f‖) :=
    (summable_zetaZeroSideContribution
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      f).norm
  let hrestricted :
      Summable
        (fun rho :
            {rho : {rho : ℂ // ZetaCompletedZero rho} // (rho : ℂ) ∉ S} =>
          ‖zetaZeroSideContribution (rho : ℂ) f‖) :=
    hglobal.subtype
      {rho : {rho : ℂ // ZetaCompletedZero rho} | (rho : ℂ) ∉ S}
  let hcomposition :
      (fun rho :
          {rho : {rho : ℂ // ZetaCompletedZero rho} // (rho : ℂ) ∉ S} =>
        ‖zetaZeroSideContribution (rho : ℂ) f‖) =
        (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
          ‖zetaZeroSideContribution (rho : ℂ) f‖) ∘
            completedZeroComplementIndexEquiv S :=
    funext
      (fun rho =>
        Eq.refl ‖zetaZeroSideContribution (rho : ℂ) f‖)
  let hcomposed :
      Summable
        ((fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
          ‖zetaZeroSideContribution (rho : ℂ) f‖) ∘
            completedZeroComplementIndexEquiv S) :=
    Eq.mp (congrArg Summable hcomposition) hrestricted
  (completedZeroComplementIndexEquiv S).summable_iff.mp hcomposed

theorem zetaZeroTail_norm_le_completedZeroComplementL1Norm
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (f : ZetaAdmissibleFunction) :
    ‖zetaZeroTail S f‖ ≤ completedZeroComplementL1Norm S f :=
  norm_tsum_le_tsum_norm
    (summable_completedZeroComplementL1Norm
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S f)

theorem autocorrelationZeroTailRealAbs_le_completedZeroComplementL1Norm
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (f : ZetaAdmissibleFunction) :
    autocorrelationZeroTailRealAbs S f ≤
      completedZeroComplementL1Norm S (convolutionAutocorrelation f) :=
  let hrealNorm :
      autocorrelationZeroTailRealAbs S f ≤
        ‖zetaZeroTail S (convolutionAutocorrelation f)‖ :=
    RCLike.abs_re_le_norm
      (zetaZeroTail S (convolutionAutocorrelation f))
  let hcomplexNorm :
      ‖zetaZeroTail S (convolutionAutocorrelation f)‖ ≤
        completedZeroComplementL1Norm S (convolutionAutocorrelation f) :=
    zetaZeroTail_norm_le_completedZeroComplementL1Norm
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S (convolutionAutocorrelation f)
  le_trans hrealNorm hcomplexNorm

theorem autocorrelationZeroTailRealAbs_lt_of_completedZeroComplementL1Norm_lt
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (f : ZetaAdmissibleFunction)
    (epsilon : ℝ)
    (htail :
      completedZeroComplementL1Norm S (convolutionAutocorrelation f) < epsilon) :
    autocorrelationZeroTailRealAbs S f < epsilon :=
  lt_of_le_of_lt
    (autocorrelationZeroTailRealAbs_le_completedZeroComplementL1Norm
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S f)
    htail

end QuantitativeSeparation
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
