import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.QuantitativeSeparation.Owner

/-!
# Quantitative finite cardinal tails

The finite tomography construction supplies exact cardinal interpolation.  This owner
records the separate quantitative theorem needed to control the tail of its concrete
cardinal interpolants as the completed-zero window grows.

The theorem is deliberately stated for the aggregate weighted tail, not as a uniform
metric separation or Riesz-sequence assertion for completed zeros.  Finite zero counting
gives summability of a prescribed polynomial weight, whereas the required estimate also
has to control the interpolation constants of the growing cardinal family.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Quantitative weighted finite tomography for the completed-zero tail.

For each fixed finite autocorrelation fiber and tolerance, this constructs a cardinal
family whose finite tomographic interpolant preserves the dagger samples, annihilates a
non-dagger completed-zero height window, and has a small complementary tail.  A proof
must bound the transform of this particular cardinal interpolant by a summable weighted
zero envelope with constants controlled as the height window grows. -/
def AutocorrelationSpectralEvalFiberSeparatedNonDaggerHeightWindowTailLocalization : Prop :=
  ∀ (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ) (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction),
    (∀ ρ : ℂ,
      ZetaCompletedZero ρ →
        ρ ∉ S →
          ρ ∉ daggerClosedSpectralSampleFinset P) →
      ∀ ε : ℝ, 0 < ε →
        ∃ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
            autocorrelationZeroTailRealAbs S f < ε

/-- Controlled weighted-cardinal construction implies finite tomographic tail
localization. -/
theorem autocorrelationSpectralEvalFiber_separatedNonDaggerHeightWindowTailLocalization :
    AutocorrelationSpectralEvalFiberSeparatedNonDaggerHeightWindowTailLocalization :=
  fun hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =>
  fun S P f₀ hSeparated ε hε =>
    QuantitativeSeparation.exists_fixedFiberProbe_with_autocorrelationZeroTailRealAbs_lt
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S P f₀ hSeparated ε hε

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
