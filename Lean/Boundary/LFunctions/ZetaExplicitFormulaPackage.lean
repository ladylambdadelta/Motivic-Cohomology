import Boundary.LFunctions.ZetaCompletionCorrection
import Boundary.LFunctions.ZetaLogBoundaryDefect

/-!
# Boundary explicit-formula defect package

This file packages the three logarithmic-line defect families into a single
owner-level object. It does not yet prove the full analytic explicit formula;
it records the concrete components that the completed explicit formula must
assemble:

* finite prime translation defects,
* archimedean translation defects,
* pole/completion correction defects.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaTestFunction

/-- The explicit-formula defect package for a logarithmic test function. -/
@[ext]
structure explicitFormulaDefectPackage where
  primeDefect : ℕ → ℕ → ℝ → ℂ
  archimedeanDefect : ℝ → ℂ
  correctionDefect : ℂ

instance : Zero explicitFormulaDefectPackage where
  zero :=
    { primeDefect := fun _ _ _ => 0
      archimedeanDefect := fun _ => 0
      correctionDefect := 0 }

instance : Add explicitFormulaDefectPackage where
  add f g :=
    { primeDefect := fun p n => f.primeDefect p n + g.primeDefect p n
      archimedeanDefect := fun a => f.archimedeanDefect a + g.archimedeanDefect a
      correctionDefect := f.correctionDefect + g.correctionDefect }

instance : SMul ℂ explicitFormulaDefectPackage where
  smul a f :=
    { primeDefect := fun p n => fun x => a * f.primeDefect p n x
      archimedeanDefect := fun x => a * (f.archimedeanDefect x)
      correctionDefect := a * f.correctionDefect }

instance : AddCommMonoid explicitFormulaDefectPackage where
  zero := 0
  add := (· + ·)
  nsmul := fun n f =>
    { primeDefect := fun p m a => n • f.primeDefect p m a
      archimedeanDefect := fun a => n • f.archimedeanDefect a
      correctionDefect := n • f.correctionDefect }
  add_assoc := by
    intro f g h
    ext p n a
    · change ((f.primeDefect p n a + g.primeDefect p n a) + h.primeDefect p n a) =
        f.primeDefect p n a + (g.primeDefect p n a + h.primeDefect p n a)
      rw [add_assoc]
    · change ((f.archimedeanDefect p + g.archimedeanDefect p) + h.archimedeanDefect p) =
        f.archimedeanDefect p + (g.archimedeanDefect p + h.archimedeanDefect p)
      rw [add_assoc]
    · change ((f.correctionDefect + g.correctionDefect) + h.correctionDefect) =
        f.correctionDefect + (g.correctionDefect + h.correctionDefect)
      rw [add_assoc]
  zero_add := by
    intro f
    ext p n a
    · change (0 : ℂ) + f.primeDefect p n a = f.primeDefect p n a
      rw [zero_add]
    · change (0 : ℂ) + f.archimedeanDefect p = f.archimedeanDefect p
      rw [zero_add]
    · change (0 : ℂ) + f.correctionDefect = f.correctionDefect
      rw [zero_add]
  add_zero := by
    intro f
    ext p n a
    · change f.primeDefect p n a + (0 : ℂ) = f.primeDefect p n a
      rw [add_zero]
    · change f.archimedeanDefect p + (0 : ℂ) = f.archimedeanDefect p
      rw [add_zero]
    · change f.correctionDefect + (0 : ℂ) = f.correctionDefect
      rw [add_zero]
  add_comm := by
    intro f g
    ext p n a
    · change f.primeDefect p n a + g.primeDefect p n a = g.primeDefect p n a + f.primeDefect p n a
      rw [add_comm]
    · change f.archimedeanDefect p + g.archimedeanDefect p = g.archimedeanDefect p + f.archimedeanDefect p
      rw [add_comm]
    · change f.correctionDefect + g.correctionDefect = g.correctionDefect + f.correctionDefect
      rw [add_comm]
  nsmul_zero := by
    intro f
    ext p n a
    · change (0 : ℕ) • f.primeDefect p n a = 0
      rw [zero_nsmul]
    · change (0 : ℕ) • f.archimedeanDefect p = 0
      rw [zero_nsmul]
    · change (0 : ℕ) • f.correctionDefect = 0
      rw [zero_nsmul]
  nsmul_succ := by
    intro n f
    ext p m a
    · change ((n + 1 : ℕ) • f.primeDefect p m a) = n • f.primeDefect p m a + f.primeDefect p m a
      rw [add_nsmul, one_nsmul]
    · change ((n + 1 : ℕ) • f.archimedeanDefect p) = n • f.archimedeanDefect p + f.archimedeanDefect p
      rw [add_nsmul, one_nsmul]
    · change ((n + 1 : ℕ) • f.correctionDefect) = n • f.correctionDefect + f.correctionDefect
      rw [add_nsmul, one_nsmul]

/-- The logarithmic explicit-formula transform attached to a test function. -/
abbrev zetaExplicitFormulaTransform := explicitFormulaDefectPackage

/-- The explicit-formula defect package attached to `f`. -/
def toExplicitFormulaDefectPackage (f : ZetaTestFunction) :
    explicitFormulaDefectPackage where
  primeDefect := fun p n => primePacketTranslationDefect p n f
  archimedeanDefect := fun a => archimedeanTranslationDefect a f 0
  correctionDefect := zetaCompletionCorrection 0

/-- The logarithmic explicit-formula transform attached to `f`. -/
def toZetaExplicitFormulaTransform (f : ZetaTestFunction) :
    zetaExplicitFormulaTransform := toExplicitFormulaDefectPackage f

/-- The prime component of the logarithmic explicit-formula transform. -/
theorem toZetaExplicitFormulaTransform_prime (f : ZetaTestFunction) (p : ℕ) (n : ℕ) :
    (toZetaExplicitFormulaTransform f).primeDefect p n =
      primePacketTranslationDefect p n f := by
  rfl

/-- The archimedean component of the logarithmic explicit-formula transform. -/
theorem toZetaExplicitFormulaTransform_archimedean (f : ZetaTestFunction) (a : ℝ) :
    (toZetaExplicitFormulaTransform f).archimedeanDefect a =
      archimedeanTranslationDefect a f 0 := by
  rfl

/-- The correction component of the logarithmic explicit-formula transform. -/
theorem toZetaExplicitFormulaTransform_correction (f : ZetaTestFunction) :
    (toZetaExplicitFormulaTransform f).correctionDefect = zetaCompletionCorrection 0 := by
  rfl

/-- The prime component of the transform is compatible with reflection. -/
theorem toZetaExplicitFormulaTransform_prime_reflect (f : ZetaTestFunction) (p : ℕ) (n : ℕ)
    :
    (toZetaExplicitFormulaTransform (reflect f)).primeDefect p n =
      fun x => - (toZetaExplicitFormulaTransform f).primeDefect p n (-x) := by
  ext x
  unfold toZetaExplicitFormulaTransform toExplicitFormulaDefectPackage primePacketTranslationDefect
  exact congrFun (translationDefect_reflect (zetaPrimePacketCenter p n) f) x

/-- The archimedean component of the transform is compatible with reflection. -/
theorem toZetaExplicitFormulaTransform_archimedean_reflect (f : ZetaTestFunction) (a : ℝ)
    :
    (toZetaExplicitFormulaTransform (reflect f)).archimedeanDefect a =
      (toZetaExplicitFormulaTransform f).archimedeanDefect a := by
  change archimedeanTranslationDefect a (reflect f) 0 =
    archimedeanTranslationDefect a f 0
  have h := congrFun (archimedeanTranslationDefect_reflect a f) 0
  rw [neg_zero] at h
  exact h

/-- The correction component is invariant under reflection. -/
theorem toZetaExplicitFormulaTransform_correction_reflect (f : ZetaTestFunction) :
    (toZetaExplicitFormulaTransform (reflect f)).correctionDefect =
      (toZetaExplicitFormulaTransform f).correctionDefect := by
  rfl

/-- The explicit-formula transform has the centered reflection symmetry on its
prime component. -/
theorem toZetaExplicitFormulaTransform_prime_centered_reflect (f : ZetaTestFunction)
    (p : ℕ) (n : ℕ) (x : ℝ) :
    (toZetaExplicitFormulaTransform (reflect f)).primeDefect p n x =
      - (toZetaExplicitFormulaTransform f).primeDefect p n (-x) := by
  unfold toZetaExplicitFormulaTransform toExplicitFormulaDefectPackage primePacketTranslationDefect
  exact congrFun (translationDefect_reflect (zetaPrimePacketCenter p n) f) x

/-- The explicit-formula transform has the centered reflection symmetry on its
archimedean component. -/
theorem toZetaExplicitFormulaTransform_archimedean_centered_reflect (f : ZetaTestFunction)
    (a : ℝ) :
    (toZetaExplicitFormulaTransform (reflect f)).archimedeanDefect a =
      (toZetaExplicitFormulaTransform f).archimedeanDefect a := by
  change archimedeanTranslationDefect a (reflect f) 0 =
    archimedeanTranslationDefect a f 0
  have h := congrFun (archimedeanTranslationDefect_reflect a f) 0
  rw [neg_zero] at h
  exact h

/-- The explicit-formula transform is exactly the concrete defect package. -/
theorem toZetaExplicitFormulaTransform_eq (f : ZetaTestFunction) :
    toZetaExplicitFormulaTransform f =
      { primeDefect := fun p n => primePacketTranslationDefect p n f,
        archimedeanDefect := fun a => archimedeanTranslationDefect a f 0,
        correctionDefect := zetaCompletionCorrection 0 } := by
  rfl

/-- The explicit-formula transform decomposes into its prime, archimedean, and
correction components. -/
theorem toZetaExplicitFormulaTransform_decomposition (f : ZetaTestFunction) :
    (toZetaExplicitFormulaTransform f).primeDefect =
        (fun (p : ℕ) (n : ℕ) => primePacketTranslationDefect p n f) ∧
      (toZetaExplicitFormulaTransform f).archimedeanDefect =
        (fun a => archimedeanTranslationDefect a f 0) ∧
      (toZetaExplicitFormulaTransform f).correctionDefect = zetaCompletionCorrection 0 := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

theorem toExplicitFormulaDefectPackage_prime (f : ZetaTestFunction) (p : ℕ) (n : ℕ) :
    (toExplicitFormulaDefectPackage f).primeDefect p n =
      primePacketTranslationDefect p n f := by
  rfl

theorem toExplicitFormulaDefectPackage_archimedean (f : ZetaTestFunction) (a : ℝ) :
    (toExplicitFormulaDefectPackage f).archimedeanDefect a =
      archimedeanTranslationDefect a f 0 := by
  rfl

theorem toExplicitFormulaDefectPackage_correction (f : ZetaTestFunction) :
    (toExplicitFormulaDefectPackage f).correctionDefect = zetaCompletionCorrection 0 := by
  rfl

theorem toExplicitFormulaDefectPackage_eq (f : ZetaTestFunction) :
    toExplicitFormulaDefectPackage f =
      { primeDefect := fun p n => primePacketTranslationDefect p n f,
        archimedeanDefect := fun a => archimedeanTranslationDefect a f 0,
        correctionDefect := zetaCompletionCorrection 0 } := by
  rfl

/-- The explicit-formula transform and defect package coincide. -/
theorem toZetaExplicitFormulaTransform_eq_defectPackage (f : ZetaTestFunction) :
    toZetaExplicitFormulaTransform f = toExplicitFormulaDefectPackage f := by
  rfl

/-- The explicit-formula defect package decomposes into the same three
components. -/
theorem toExplicitFormulaDefectPackage_decomposition (f : ZetaTestFunction) :
    (toExplicitFormulaDefectPackage f).primeDefect =
        (fun (p : ℕ) (n : ℕ) => primePacketTranslationDefect p n f) ∧
      (toExplicitFormulaDefectPackage f).archimedeanDefect =
        (fun a => archimedeanTranslationDefect a f 0) ∧
      (toExplicitFormulaDefectPackage f).correctionDefect = zetaCompletionCorrection 0 := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

end ZetaTestFunction

end
end LFunctions
end Boundary
