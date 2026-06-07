import Boundary.LFunctions.ZetaAdmissibleFunction
import Boundary.LFunctions.ZetaExplicitFormulaPackage

/-!
# Boundary admissible explicit-formula transform

This file packages the explicit-formula transform on the admissible carrier by
reusing the concrete logarithmic-line defect package already proved for
`ZetaTestFunction`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The explicit-formula transform attached to an admissible test function. -/
def toZetaExplicitFormulaTransform (f : ZetaAdmissibleFunction) :
    ZetaTestFunction.zetaExplicitFormulaTransform :=
  ZetaTestFunction.toZetaExplicitFormulaTransform f.toZetaTestFunction'

/-- The prime component of the admissible explicit-formula transform. -/
theorem toZetaExplicitFormulaTransform_prime (f : ZetaAdmissibleFunction) (p : ℕ) (n : ℕ) :
    (toZetaExplicitFormulaTransform f).primeDefect p n =
      ZetaTestFunction.primePacketTranslationDefect p n f.toZetaTestFunction' := by
  rfl

/-- The archimedean component of the admissible explicit-formula transform. -/
theorem toZetaExplicitFormulaTransform_archimedean (f : ZetaAdmissibleFunction) (a : ℝ) :
    (toZetaExplicitFormulaTransform f).archimedeanDefect a =
      ZetaTestFunction.archimedeanTranslationDefect a f.toZetaTestFunction' 0 := by
  rfl

/-- The correction component of the admissible explicit-formula transform. -/
theorem toZetaExplicitFormulaTransform_correction (f : ZetaAdmissibleFunction) :
    (toZetaExplicitFormulaTransform f).correctionDefect =
      zetaCompletionCorrection 0 := by
  rfl

/-- The admissible explicit-formula transform agrees with the underlying test-function transform. -/
theorem toZetaExplicitFormulaTransform_eq (f : ZetaAdmissibleFunction) :
    toZetaExplicitFormulaTransform f =
      ZetaTestFunction.toZetaExplicitFormulaTransform f.toZetaTestFunction' := by
  rfl

/-- The admissible transform is the underlying explicit-formula transform. -/
theorem toZetaExplicitFormulaTransform_pair (f : ZetaAdmissibleFunction) :
    toZetaExplicitFormulaTransform f =
      ZetaTestFunction.toZetaExplicitFormulaTransform f.toZetaTestFunction' := by
  rfl

/-- The admissible transform exposes the prime, archimedean, and correction components. -/
theorem toZetaExplicitFormulaTransform_components (f : ZetaAdmissibleFunction) :
    (toZetaExplicitFormulaTransform f).primeDefect =
        (fun (p : ℕ) (n : ℕ) =>
          ZetaTestFunction.primePacketTranslationDefect p n f.toZetaTestFunction') ∧
      (toZetaExplicitFormulaTransform f).archimedeanDefect =
        (fun a => ZetaTestFunction.archimedeanTranslationDefect a f.toZetaTestFunction' 0) ∧
      (toZetaExplicitFormulaTransform f).correctionDefect = zetaCompletionCorrection 0 := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- The admissible transform is decomposed into prime, archimedean, and correction parts. -/
theorem toZetaExplicitFormulaTransform_parts (f : ZetaAdmissibleFunction) :
    (toZetaExplicitFormulaTransform f).primeDefect =
        (fun (p : ℕ) (n : ℕ) =>
          ZetaTestFunction.primePacketTranslationDefect p n f.toZetaTestFunction') ∧
      (toZetaExplicitFormulaTransform f).archimedeanDefect =
        (fun a => ZetaTestFunction.archimedeanTranslationDefect a f.toZetaTestFunction' 0) ∧
      (toZetaExplicitFormulaTransform f).correctionDefect = zetaCompletionCorrection 0 := by
  exact toZetaExplicitFormulaTransform_components f

/-- The admissible transform components are prime, archimedean, and correction terms. -/
theorem toZetaExplicitFormulaTransform_split (f : ZetaAdmissibleFunction) :
    (toZetaExplicitFormulaTransform f).primeDefect =
        (fun (p : ℕ) (n : ℕ) =>
          ZetaTestFunction.primePacketTranslationDefect p n f.toZetaTestFunction') ∧
      (toZetaExplicitFormulaTransform f).archimedeanDefect =
        (fun a => ZetaTestFunction.archimedeanTranslationDefect a f.toZetaTestFunction' 0) ∧
      (toZetaExplicitFormulaTransform f).correctionDefect = zetaCompletionCorrection 0 := by
  exact toZetaExplicitFormulaTransform_components f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
