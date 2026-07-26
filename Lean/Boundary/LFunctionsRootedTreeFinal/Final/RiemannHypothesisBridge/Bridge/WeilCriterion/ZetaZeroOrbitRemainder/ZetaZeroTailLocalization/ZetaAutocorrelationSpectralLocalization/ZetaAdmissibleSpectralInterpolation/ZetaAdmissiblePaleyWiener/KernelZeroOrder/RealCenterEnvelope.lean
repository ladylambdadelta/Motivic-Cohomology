import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.KernelZeroOrder.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.SupportInterval.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleNormalizedScale

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The canonical Paley--Wiener support interval gives the honest exponential
bound for the admissible Laplace transform at a real spectral center. -/
theorem zetaLaplaceTransform_realCenter_le_canonicalSupportEnvelope
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' (x : ℂ)‖ ≤
      zetaPaleyWienerZeroOrderEnvelope
        f (canonicalZetaPaleyWienerSupportInterval f) x x :=
  let I : ZetaPaleyWienerSupportInterval f :=
    canonicalZetaPaleyWienerSupportInterval f
  let hz : zetaPaleyWienerInVerticalStrip x x (x : ℂ) :=
    ⟨le_trans (le_refl x) (le_refl x),
      le_trans (le_refl x) (le_refl x)⟩
  zetaLaplaceTransform_supportInterval_zeroOrder_le_envelope
    f I x x (x : ℂ) hz

theorem normalizedScale_realCenter_le_originalSupportEnvelope
    (a : ℝ) (ha : 0 < a) (f : ZetaAdmissibleFunction) (R : ℝ) :
    ‖Boundary.zetaLaplaceTransform
        (normalizedScale a f).toZetaTestFunction' (R : ℂ)‖ ≤
      zetaPaleyWienerZeroOrderEnvelope
        f (canonicalZetaPaleyWienerSupportInterval f)
        (a * R) (a * R) := by
  have hscale := zetaLaplaceTransform_normalizedScale a ha f (R : ℂ)
  have hcast :
      (a : ℂ) * (R : ℂ) = ((a * R : ℝ) : ℂ) := by
    exact (Complex.ofReal_mul a R).symm
  have htransform :
      ‖Boundary.zetaLaplaceTransform
          (normalizedScale a f).toZetaTestFunction' (R : ℂ)‖ =
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction'
          ((a * R : ℝ) : ℂ)‖ := by
    exact Eq.trans
      (congrArg norm hscale)
      (congrArg
        (fun z : ℂ => ‖Boundary.zetaLaplaceTransform
          f.toZetaTestFunction' z‖) hcast)
  exact Eq.subst
    (motive := fun value : ℝ => value ≤
      zetaPaleyWienerZeroOrderEnvelope
        f (canonicalZetaPaleyWienerSupportInterval f)
        (a * R) (a * R))
    htransform.symm
    (zetaLaplaceTransform_realCenter_le_canonicalSupportEnvelope f (a * R))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
