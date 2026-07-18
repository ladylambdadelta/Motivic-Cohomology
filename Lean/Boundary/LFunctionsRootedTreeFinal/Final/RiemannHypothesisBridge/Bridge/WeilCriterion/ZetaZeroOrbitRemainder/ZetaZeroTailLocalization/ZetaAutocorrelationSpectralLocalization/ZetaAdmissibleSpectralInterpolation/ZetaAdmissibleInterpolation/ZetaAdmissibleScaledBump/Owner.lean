import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleNormalizedScale

/-!
# Scaled complex spectral bumps

This owner constructs an admissible probe whose spectral transform is a scaled copy of
the normalized unit seed centered at an arbitrary complex sample.
-/

namespace Boundary
namespace LFunctions
noncomputable section

namespace ZetaAdmissibleFunction

/-- The normalized unit seed, spectrally centered at `c` and concentrated by the positive
scale `a`. -/
def centeredScaledLaplaceSeed
    (a : ℝ)
    (c : ℂ) : ZetaAdmissibleFunction :=
  complexExponentialModulate c
    (normalizedScale a (laplaceUnitSeed 0))

/-- The centered scaled seed has the expected scaled and translated spectral evaluation. -/
theorem zetaSpectralEval_centeredScaledLaplaceSeed
    (a : ℝ)
    (ha : 0 < a)
    (c z : ℂ) :
    zetaSpectralEval (centeredScaledLaplaceSeed a c) z =
      zetaSpectralEval (laplaceUnitSeed 0) ((a : ℂ) * (z - c)) := by
  calc
    zetaSpectralEval (centeredScaledLaplaceSeed a c) z =
        zetaSpectralEval (normalizedScale a (laplaceUnitSeed 0)) (z - c) := by
          exact zetaSpectralEval_complexExponentialModulate c z
            (normalizedScale a (laplaceUnitSeed 0))
    _ = zetaSpectralEval (laplaceUnitSeed 0) ((a : ℂ) * (z - c)) := by
          exact zetaSpectralEval_normalizedScale a ha (laplaceUnitSeed 0) (z - c)

/-- The centered scaled seed has unit spectral value at its center. -/
theorem zetaSpectralEval_centeredScaledLaplaceSeed_center
    (a : ℝ)
    (ha : 0 < a)
    (c : ℂ) :
    zetaSpectralEval (centeredScaledLaplaceSeed a c) c = 1 := by
  have hscaled :
      zetaSpectralEval (centeredScaledLaplaceSeed a c) c =
        zetaSpectralEval (laplaceUnitSeed 0) ((a : ℂ) * (c - c)) :=
    zetaSpectralEval_centeredScaledLaplaceSeed a ha c c
  have hzero :
      ((a : ℂ) * (c - c)) = 0 := by
    exact Eq.trans
      (congrArg (fun value : ℂ => (a : ℂ) * value) (sub_self c))
      (mul_zero (a : ℂ))
  have hunit : zetaSpectralEval (laplaceUnitSeed 0) 0 = 1 := by
    calc
      zetaSpectralEval (laplaceUnitSeed 0) 0 =
          zetaLaplaceTransform (laplaceUnitSeed 0).toZetaTestFunction' 0 := by
            exact zetaSpectralEval_eq_laplace (laplaceUnitSeed 0) 0
      _ = 1 := zetaLaplaceTransform_laplaceUnitSeed 0
  exact
    Eq.trans hscaled
      (Eq.trans
        (congrArg (fun value : ℂ => zetaSpectralEval (laplaceUnitSeed 0) value) hzero)
        hunit)

end ZetaAdmissibleFunction
end
end
end LFunctions
end Boundary
