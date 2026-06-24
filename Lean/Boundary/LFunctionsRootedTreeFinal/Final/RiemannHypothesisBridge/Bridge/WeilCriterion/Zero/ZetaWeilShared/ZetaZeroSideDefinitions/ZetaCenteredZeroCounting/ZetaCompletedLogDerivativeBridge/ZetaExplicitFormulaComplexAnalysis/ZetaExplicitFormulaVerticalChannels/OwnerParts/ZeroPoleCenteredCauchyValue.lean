import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleSides

/-!
# Centered zero-pole inversion value

This file owns the centered value targeted by the right zero-pole
Cauchy/Laplace inversion theorem.  It deliberately does not identify this value
with the existing shifted project rectangle boundary: that boundary has the
local `s = 0` numerator `Φ_f (-1/2)`, while the vertical inversion target is
normalized at `Φ_f 0`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The centered zero-pole Cauchy/Laplace boundary value targeted by the
right zero-pole inversion theorem. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionCenteredZeroPoleBoundaryValue
    (f : ZetaAdmissibleFunction) : ℂ :=
  1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0

/-- The centered zero-pole boundary value unfolds to the displayed
`(1 / (1 / 2)) * Φ_f 0` normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionCenteredZeroPoleBoundaryValue_eq_centeredPolePhi
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionCenteredZeroPoleBoundaryValue f =
      1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0 := by
  rfl

/-- Centered zero-pole Cauchy/Laplace kernel in the variable
`z = s - 1 / 2`.

The denominator is `z + 1 / 2`, because the original pole factor is `1 / s`.
This definition keeps the centered inversion theorem separate from the shifted
local rectangle residue at `s = 0`. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionCenteredZeroPoleKernel
    (f : ZetaAdmissibleFunction) (z : ℂ) : ℂ :=
  (-1 / (z + (1 / 2 : ℂ))) * zetaCompletedExplicitFormulaPhi f z

/-- The centered zero-pole kernel unfolds to
`(-1 / (z + 1/2)) * Φ_f z`. -/
theorem zetaCompletedExplicitFormulaCorrectionCenteredZeroPoleKernel_eq
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedExplicitFormulaCorrectionCenteredZeroPoleKernel f z =
      (-1 / (z + (1 / 2 : ℂ))) * zetaCompletedExplicitFormulaPhi f z := by
  rfl

/-- The centered right affine zero-pole kernel, written directly in the
centered variable `z = (F.c - 1/2) + i t`. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionCenteredRightZeroPoleAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionCenteredZeroPoleKernel f
    (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I)

/-- The centered right affine zero-pole kernel unfolds to the original
right-line zero-pole integrand in centered coordinates. -/
theorem zetaCompletedExplicitFormulaCorrectionCenteredRightZeroPoleAffineKernel_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaCorrectionCenteredRightZeroPoleAffineKernel f F t =
      (-1 / (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I + (1 / 2 : ℂ))) *
        zetaCompletedExplicitFormulaPhi f
          (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
  rfl

/-- In centered coordinates, adding back `1/2` recovers the right affine
line denominator. -/
theorem zetaCompletedExplicitFormulaCorrectionCenteredRightZeroPole_denominator_eq_rightAffine
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I + (1 / 2 : ℂ)) =
      (F.c : ℂ) + t * Complex.I := by
  calc
    (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I + (1 / 2 : ℂ)) =
        (((F.c : ℂ) + -(1 / 2 : ℂ)) + t * Complex.I + (1 / 2 : ℂ)) := by
      exact congrArg
        (fun z : ℂ => z + t * Complex.I + (1 / 2 : ℂ))
        (sub_eq_add_neg (F.c : ℂ) (1 / 2 : ℂ))
    _ = ((F.c : ℂ) + (-(1 / 2 : ℂ) + t * Complex.I) + (1 / 2 : ℂ)) := by
      exact congrArg
        (fun z : ℂ => z + (1 / 2 : ℂ))
        (add_assoc (F.c : ℂ) (-(1 / 2 : ℂ)) (t * Complex.I))
    _ = ((F.c : ℂ) + (t * Complex.I + -(1 / 2 : ℂ)) + (1 / 2 : ℂ)) := by
      exact congrArg
        (fun z : ℂ => ((F.c : ℂ) + z) + (1 / 2 : ℂ))
        (add_comm (-(1 / 2 : ℂ)) (t * Complex.I))
    _ = (((F.c : ℂ) + t * Complex.I) + -(1 / 2 : ℂ) + (1 / 2 : ℂ)) := by
      exact congrArg
        (fun z : ℂ => z + (1 / 2 : ℂ))
        ((add_assoc (F.c : ℂ) (t * Complex.I) (-(1 / 2 : ℂ))).symm)
    _ = ((F.c : ℂ) + t * Complex.I) + (-(1 / 2 : ℂ) + (1 / 2 : ℂ)) := by
      exact add_assoc ((F.c : ℂ) + t * Complex.I) (-(1 / 2 : ℂ)) (1 / 2 : ℂ)
    _ = ((F.c : ℂ) + t * Complex.I) + 0 := by
      exact congrArg
        (fun z : ℂ => ((F.c : ℂ) + t * Complex.I) + z)
        (neg_add_cancel (1 / 2 : ℂ))
    _ = (F.c : ℂ) + t * Complex.I := by
      exact add_zero ((F.c : ℂ) + t * Complex.I)

/-- The centered right zero-pole affine kernel is the existing right
zero-pole affine integrand, written in centered coordinates. -/
theorem zetaCompletedExplicitFormulaCorrectionCenteredRightZeroPoleAffineKernel_eq_rightAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaCorrectionCenteredRightZeroPoleAffineKernel f F t =
      (-1 / ((F.c : ℂ) + t * Complex.I)) *
        zetaCompletedExplicitFormulaPhi f
          (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
  let z : ℂ := ((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I
  let d : ℂ := z + (1 / 2 : ℂ)
  have hkernel :
      zetaCompletedExplicitFormulaCorrectionCenteredRightZeroPoleAffineKernel f F t =
        (-1 / d) * zetaCompletedExplicitFormulaPhi f z := by
    rfl
  have hden :
      d = (F.c : ℂ) + t * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionCenteredRightZeroPole_denominator_eq_rightAffine
      F t
  calc
    zetaCompletedExplicitFormulaCorrectionCenteredRightZeroPoleAffineKernel f F t =
        (-1 / d) * zetaCompletedExplicitFormulaPhi f z := hkernel
    _ = (-1 / ((F.c : ℂ) + t * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f z := by
      exact congrArg
        (fun w : ℂ => (-1 / w) * zetaCompletedExplicitFormulaPhi f z)
        hden
    _ = (-1 / ((F.c : ℂ) + t * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
      rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
