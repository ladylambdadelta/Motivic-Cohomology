import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissibleInterpolation.ZetaAdmissibleTransform.ZetaExplicitFormulaPackage.Owner

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
    ZetaTestFunction.explicitFormulaDefectPackage :=
  ZetaTestFunction.toExplicitFormulaDefectPackage f.toZetaTestFunction'

/-- The linear core of the admissible explicit-formula transform. -/
def toZetaExplicitFormulaLinearTransform (f : ZetaAdmissibleFunction) :
    ZetaTestFunction.explicitFormulaLinearDefectPackage :=
  ZetaTestFunction.toExplicitFormulaLinearDefectPackage f.toZetaTestFunction'

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
      ZetaTestFunction.toExplicitFormulaDefectPackage f.toZetaTestFunction' := by
  rfl

/-- The completed admissible explicit-formula transform is the linear core plus correction. -/
theorem toZetaExplicitFormulaTransform_eq_linear_add_correction (f : ZetaAdmissibleFunction) :
    toZetaExplicitFormulaTransform f =
      { primeDefect := fun p n =>
          (toZetaExplicitFormulaLinearTransform f).primeDefect p n
        archimedeanDefect := fun a =>
          (toZetaExplicitFormulaLinearTransform f).archimedeanDefect a
        correctionDefect := zetaCompletionCorrection 0 } := by
  rfl

/-- The admissible transform is the underlying explicit-formula transform. -/
theorem toZetaExplicitFormulaTransform_pair (f : ZetaAdmissibleFunction) :
    toZetaExplicitFormulaTransform f =
      ZetaTestFunction.toExplicitFormulaDefectPackage f.toZetaTestFunction' := by
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

/-- The admissible explicit-formula transform of a sum is the sum of the transforms. -/
theorem toZetaExplicitFormulaLinearTransform_add (f g : ZetaAdmissibleFunction) :
    toZetaExplicitFormulaLinearTransform (f + g) =
      toZetaExplicitFormulaLinearTransform f + toZetaExplicitFormulaLinearTransform g := by
  exact ZetaTestFunction.toExplicitFormulaLinearDefectPackage_add
    (f := f.toZetaTestFunction') (g := g.toZetaTestFunction')

/-- The admissible explicit-formula transform of a scalar multiple is the scalar multiple of the
transform. -/
theorem toZetaExplicitFormulaLinearTransform_smul (c : ℂ) (f : ZetaAdmissibleFunction) :
    toZetaExplicitFormulaLinearTransform (c • f) =
      c • toZetaExplicitFormulaLinearTransform f := by
  exact ZetaTestFunction.toExplicitFormulaLinearDefectPackage_smul
    (c := c) (f := f.toZetaTestFunction')

/-- Finite sums in `ZetaTestFunction` evaluate pointwise. -/
theorem zetaTestFunction_sum_apply {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ZetaTestFunction) (x : ℝ) :
    (∑ a in s, f a) x = ∑ a in s, f a x := by
  induction s using Finset.induction_on with
  | empty =>
      rfl
  | @insert a s ha ih =>
      calc
        (∑ b in insert a s, f b) x = (f a + ∑ b in s, f b) x := by
          exact congrArg (fun g : ZetaTestFunction => g x) (Finset.sum_insert ha)
        _ = f a x + (∑ b in s, f b) x := by
          rfl
        _ = f a x + ∑ b in s, f b x := by
          exact congrArg (fun y => f a x + y) ih
        _ = ∑ b in insert a s, f b x := by
          exact (Finset.sum_insert
              (s := s)
              (a := a)
              (f := fun b => f b x)
              ha).symm

/-- The underlying test function of an admissible finite sum is the finite sum of the
underlying test functions. -/
theorem toZetaTestFunction'_sum {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    (∑ a in s, f a).toZetaTestFunction' =
      ∑ a in s, (f a).toZetaTestFunction' := by
  ext x
  exact
    (ZetaAdmissibleFunction.sum_apply (s := s) (f := f) x).trans
      (zetaTestFunction_sum_apply (s := s)
        (f := fun a => (f a).toZetaTestFunction') x).symm

/-- The admissible explicit-formula transform commutes with finite sums. -/
theorem toZetaExplicitFormulaLinearTransform_sum {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    toZetaExplicitFormulaLinearTransform (∑ a in s, f a) =
      ∑ a in s, toZetaExplicitFormulaLinearTransform (f a) := by
  calc
    toZetaExplicitFormulaLinearTransform (∑ a in s, f a)
        = ZetaTestFunction.toExplicitFormulaLinearDefectPackage
            (∑ a in s, (f a).toZetaTestFunction') := by
          exact congrArg ZetaTestFunction.toExplicitFormulaLinearDefectPackage
            (toZetaTestFunction'_sum (s := s) (f := f))
    _ = ∑ a in s, toZetaExplicitFormulaLinearTransform (f a) := by
          exact ZetaTestFunction.toExplicitFormulaLinearDefectPackage_sum
            (s := s) (f := fun a => (f a).toZetaTestFunction')

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
