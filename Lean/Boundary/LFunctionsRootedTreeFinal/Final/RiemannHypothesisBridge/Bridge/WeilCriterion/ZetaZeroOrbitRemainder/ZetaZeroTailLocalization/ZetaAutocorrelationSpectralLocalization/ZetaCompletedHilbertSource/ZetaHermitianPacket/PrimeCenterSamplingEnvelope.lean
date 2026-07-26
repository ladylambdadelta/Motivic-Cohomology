import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.KernelZeroOrder.RealCenterEnvelope
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerSampling
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPrimePowerWindow.OwnerParts.Part04

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-! The Paley--Wiener owner estimate is now exposed at the sampling-density
level.  This is deliberately pointwise: the later arithmetic owner will be
responsible for converting the exponential envelope into a prime-height
majorant after the support scale has been chosen. -/

theorem completedPrimeCenterPlancherelDensity_le_realCenterEnvelope_sq
    (f : ZetaAdmissibleFunction) (index : ZetaPrimePowerIndex) :
    completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
        index f ≤
      (zetaPaleyWienerZeroOrderEnvelope
        f (canonicalZetaPaleyWienerSupportInterval f)
        index.center index.center) ^ 2 := by
  let A : ℝ :=
    ‖zetaCompletedSpectralLaplaceTransform f index.center‖
  let B : ℝ :=
    zetaPaleyWienerZeroOrderEnvelope
      f (canonicalZetaPaleyWienerSupportInterval f)
      index.center index.center
  have hAB : A ≤ B := by
    exact zetaLaplaceTransform_realCenter_le_canonicalSupportEnvelope f
      index.center
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := le_trans hA hAB
  have hsq : A * A ≤ B * B :=
    mul_le_mul hAB hAB hA hB
  have hleft :
      completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
          index f = A * A := by
    unfold completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
    unfold A
    exact pow_two _
  have hright :
      B * B =
        (zetaPaleyWienerZeroOrderEnvelope
          f (canonicalZetaPaleyWienerSupportInterval f)
          index.center index.center) ^ 2 := by
    unfold B
    exact (pow_two _).symm
  calc
    completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
        index f = A * A := hleft
    _ ≤ B * B := hsq
    _ = (zetaPaleyWienerZeroOrderEnvelope
        f (canonicalZetaPaleyWienerSupportInterval f)
        index.center index.center) ^ 2 := hright

/-! Once the arithmetic owner has produced a polynomial majorant for the
envelope square, summability is a one-line positive-series transport.  Keeping
this cut here prevents the analytic and arithmetic sinks from re-forming a
cycle in the trace-energy file. -/

theorem completedPrimeCenterPlancherelDensity_summable_of_polynomialEnvelope
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : ∀ index : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
          index f ≤
        D * ZetaPrimePowerIndex.polynomialHeightDecay k index) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
          index f) :=
  Summable.of_nonneg_of_le
    (fun index =>
      completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity_nonnegative
        index f)
    hbound
    (ZetaPrimePowerIndex.summable_const_mul_polynomialHeightDecay D k)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
