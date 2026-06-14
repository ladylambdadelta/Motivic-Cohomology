import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.ZetaLogBoundaryDefect.Owner

/-!
# Boundary completion correction on the logarithmic line

This file isolates the pole/completion correction term in centered
coordinates. The construction is intentionally conservative: it records the
centered correction contribution already present in the completed zeta
normalization, together with its reflection symmetry.

The explicit-formula route will later package this correction term alongside
the prime and archimedean logarithmic defects.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The centered pole/completion correction term on the logarithmic line. -/
def zetaCompletionCorrection (s : ℂ) : ℂ :=
  zetaWeilCorrection s

theorem zetaCompletionCorrection_eq (s : ℂ) :
    zetaCompletionCorrection s =
      1 / (1 / 2 + s) + 1 / (1 - (1 / 2 + s)) := by
  rfl

/-- At the centered basepoint the correction has the explicit pole-normalized value. -/
theorem zetaCompletionCorrection_zero :
    zetaCompletionCorrection 0 =
      1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ)) := by
  have harg : (1 / 2 : ℂ) + 0 = (1 / 2 : ℂ) := add_zero (1 / 2 : ℂ)
  have hleft :
      1 / ((1 / 2 : ℂ) + 0) = 1 / (1 / 2 : ℂ) :=
    congrArg (fun z : ℂ => 1 / z) harg
  have hright_den :
      1 - ((1 / 2 : ℂ) + 0) = 1 - (1 / 2 : ℂ) :=
    congrArg (fun z : ℂ => 1 - z) harg
  have hright :
      1 / (1 - ((1 / 2 : ℂ) + 0)) = 1 / (1 - (1 / 2 : ℂ)) :=
    congrArg (fun z : ℂ => 1 / z) hright_den
  calc
    zetaCompletionCorrection 0 =
        1 / ((1 / 2 : ℂ) + 0) + 1 / (1 - ((1 / 2 : ℂ) + 0)) :=
      zetaCompletionCorrection_eq 0
    _ = 1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ)) :=
      congrArg₂ (fun a b : ℂ => a + b) hleft hright

/-- The inverse of the centered half is two. -/
theorem complex_one_div_half_eq_two :
    1 / (1 / 2 : ℂ) = 2 := by
  exact one_div_one_div (2 : ℂ)

/-- The complement of the centered half is again the centered half. -/
theorem complex_one_sub_half_eq_half :
    1 - (1 / 2 : ℂ) = 1 / 2 := by
  exact sub_half (1 : ℂ)

/-- The inverse of the complement of the centered half is two. -/
theorem complex_one_div_one_sub_half_eq_two :
    1 / (1 - (1 / 2 : ℂ)) = 2 := by
  have hsub : 1 - (1 / 2 : ℂ) = 1 / 2 :=
    complex_one_sub_half_eq_half
  exact Eq.trans
    (congrArg (fun z : ℂ => 1 / z) hsub)
    complex_one_div_half_eq_two

/-- The centered basepoint correction has complex value four. -/
theorem zetaCompletionCorrection_zero_eq_four :
    zetaCompletionCorrection 0 = (4 : ℂ) := by
  calc
    zetaCompletionCorrection 0 =
        1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ)) :=
      zetaCompletionCorrection_zero
    _ = (2 : ℂ) + 2 :=
      congrArg₂ (fun a b : ℂ => a + b)
        complex_one_div_half_eq_two
        complex_one_div_one_sub_half_eq_two
    _ = (4 : ℂ) :=
      two_add_two_eq_four

/-- The centered basepoint correction is real. -/
theorem zetaCompletionCorrection_zero_im :
    Complex.im (zetaCompletionCorrection 0) = 0 := by
  exact Eq.trans
    (congrArg Complex.im zetaCompletionCorrection_zero_eq_four)
    (Complex.ofReal_im 4)

/-- The centered basepoint correction has real value four. -/
theorem zetaCompletionCorrection_zero_re :
    Complex.re (zetaCompletionCorrection 0) = 4 := by
  exact Eq.trans
    (congrArg Complex.re zetaCompletionCorrection_zero_eq_four)
    (Complex.ofReal_re 4)

/-- The centered basepoint correction is fixed by complex conjugation. -/
theorem zetaCompletionCorrection_zero_star :
    star (zetaCompletionCorrection 0) = zetaCompletionCorrection 0 := by
  apply Complex.ext
  · rfl
  · have him := zetaCompletionCorrection_zero_im
    calc
      Complex.im (star (zetaCompletionCorrection 0)) =
          -Complex.im (zetaCompletionCorrection 0) := by
        rfl
      _ = -0 := by
        exact congrArg Neg.neg him
      _ = 0 := by
        exact neg_zero
      _ = Complex.im (zetaCompletionCorrection 0) := by
        exact him.symm

/-- The normalized correction packet coordinate. Its square is the centered
linear correction value. -/
def zetaCompletionCorrectionPacketCoordinate : ℝ :=
  2

/-- The normalized correction packet coordinate squares to the centered
correction contribution. -/
theorem zetaCompletionCorrectionPacketCoordinate_sq :
    zetaCompletionCorrectionPacketCoordinate *
        zetaCompletionCorrectionPacketCoordinate =
      Complex.re (zetaCompletionCorrection 0) := by
  calc
    zetaCompletionCorrectionPacketCoordinate *
        zetaCompletionCorrectionPacketCoordinate = 4 := by
      exact Eq.trans
        (mul_two (2 : ℝ))
        (two_add_two_eq_four : (2 : ℝ) + 2 = 4)
    _ = Complex.re (zetaCompletionCorrection 0) := by
      exact zetaCompletionCorrection_zero_re.symm

theorem zetaCompletionCorrection_neg (s : ℂ) :
    zetaCompletionCorrection (-s) = zetaCompletionCorrection s := by
  unfold zetaCompletionCorrection
  exact zetaWeilCorrection_neg s

theorem zetaCompletionCorrection_centered (s : ℂ) :
    zetaCompletionCorrection s = zetaWeilCorrection s := by
  rfl

end

end LFunctions
end Boundary
