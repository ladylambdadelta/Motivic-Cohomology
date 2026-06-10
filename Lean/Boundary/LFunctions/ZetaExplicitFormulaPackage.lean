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

/-- The genuinely linear part of the explicit-formula defect package. -/
@[ext]
structure explicitFormulaLinearDefectPackage where
  primeDefect : ℕ → ℕ → ℝ → ℂ
  archimedeanDefect : ℝ → ℂ

instance : Zero explicitFormulaLinearDefectPackage where
  zero :=
    { primeDefect := fun _ _ _ => 0
      archimedeanDefect := fun _ => 0 }

instance : Add explicitFormulaLinearDefectPackage where
  add f g :=
    { primeDefect := fun p n => f.primeDefect p n + g.primeDefect p n
      archimedeanDefect := fun a => f.archimedeanDefect a + g.archimedeanDefect a }

instance : SMul ℂ explicitFormulaLinearDefectPackage where
  smul a f :=
    { primeDefect := fun p n => fun x => a * f.primeDefect p n x
      archimedeanDefect := fun x => a * (f.archimedeanDefect x) }

instance : AddCommMonoid explicitFormulaLinearDefectPackage where
  zero := 0
  add := (· + ·)
  nsmul := fun n f =>
    { primeDefect := fun p m a => n • f.primeDefect p m a
      archimedeanDefect := fun a => n • f.archimedeanDefect a }
  add_assoc := by
    intro f g h
    ext p n a <;> exact add_assoc _ _ _
  zero_add := by
    intro f
    ext p n a <;> exact zero_add _
  add_zero := by
    intro f
    ext p n a <;> exact add_zero _
  add_comm := by
    intro f g
    ext p n a <;> exact add_comm _ _
  nsmul_zero := by
    intro f
    ext p n a <;> exact zero_nsmul _
  nsmul_succ := by
    intro n f
    ext p m a <;> exact succ_nsmul _ n

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

/-- The logarithmic explicit-formula linear core attached to a test function. -/
abbrev zetaExplicitFormulaLinearTransform := explicitFormulaLinearDefectPackage

/-- The linear core attached to `f`. -/
def toExplicitFormulaLinearDefectPackage (f : ZetaTestFunction) :
    explicitFormulaLinearDefectPackage where
  primeDefect := fun p n => primePacketTranslationDefect p n f
  archimedeanDefect := fun a => archimedeanTranslationDefect a f 0

/-- The linear explicit-formula transform attached to `f`. -/
def toZetaExplicitFormulaLinearTransform (f : ZetaTestFunction) :
    zetaExplicitFormulaLinearTransform := toExplicitFormulaLinearDefectPackage f

/-- The explicit-formula defect package attached to `f`. -/
def toExplicitFormulaDefectPackage (f : ZetaTestFunction) :
    explicitFormulaDefectPackage where
  primeDefect := fun p n => primePacketTranslationDefect p n f
  archimedeanDefect := fun a => archimedeanTranslationDefect a f 0
  correctionDefect := zetaCompletionCorrection 0

/-- Pointwise additivity of the prime defect. -/
theorem primePacketTranslationDefect_add_pointwise (f g : ZetaTestFunction) (p : ℕ) (n : ℕ)
    (a : ℝ) :
    primePacketTranslationDefect p n (f + g) a =
      primePacketTranslationDefect p n f a +
        primePacketTranslationDefect p n g a := by
  unfold primePacketTranslationDefect translationDefect
  calc
    (f (a + zetaPrimePacketCenter p n / 2) + g (a + zetaPrimePacketCenter p n / 2)) -
        (f (a - zetaPrimePacketCenter p n / 2) + g (a - zetaPrimePacketCenter p n / 2)) =
        (f (a + zetaPrimePacketCenter p n / 2) + g (a + zetaPrimePacketCenter p n / 2)) +
          (-f (a - zetaPrimePacketCenter p n / 2) + -g (a - zetaPrimePacketCenter p n / 2)) := by
          rw [sub_eq_add_neg, neg_add]
    _ = (f (a + zetaPrimePacketCenter p n / 2) + -f (a - zetaPrimePacketCenter p n / 2)) +
          (g (a + zetaPrimePacketCenter p n / 2) + -g (a - zetaPrimePacketCenter p n / 2)) := by
          ac_rfl

/-- Pointwise additivity of the archimedean defect at the completed-formula basepoint. -/
theorem archimedeanTranslationDefect_add_pointwise (a : ℝ) (f g : ZetaTestFunction) :
    archimedeanTranslationDefect a (f + g) 0 =
      archimedeanTranslationDefect a f 0 + archimedeanTranslationDefect a g 0 := by
  unfold archimedeanTranslationDefect
  change
    f (0 + a / 2) + g (0 + a / 2) + (f (0 - a / 2) + g (0 - a / 2)) =
      (f (0 + a / 2) + f (0 - a / 2)) + (g (0 + a / 2) + g (0 - a / 2))
  ac_rfl

/-- Pointwise scalar compatibility of the prime defect. -/
theorem primePacketTranslationDefect_smul_pointwise (c : ℂ) (f : ZetaTestFunction) (p : ℕ)
    (n : ℕ) (a : ℝ) :
    primePacketTranslationDefect p n (c • f) a =
      c * primePacketTranslationDefect p n f a := by
  unfold primePacketTranslationDefect translationDefect
  calc
    c * f (a + zetaPrimePacketCenter p n / 2) - c * f (a - zetaPrimePacketCenter p n / 2) =
        c * f (a + zetaPrimePacketCenter p n / 2) + -(c * f (a - zetaPrimePacketCenter p n / 2)) := by
          rw [sub_eq_add_neg]
    _ = c * (f (a + zetaPrimePacketCenter p n / 2) + -f (a - zetaPrimePacketCenter p n / 2)) := by
          rw [← mul_neg, ← mul_add]

/-- Pointwise scalar compatibility of the archimedean defect. -/
theorem archimedeanTranslationDefect_smul_pointwise (a : ℝ) (c : ℂ) (f : ZetaTestFunction) :
    archimedeanTranslationDefect a (c • f) 0 = c * archimedeanTranslationDefect a f 0 := by
  unfold archimedeanTranslationDefect
  change
    (c * f (0 + a / 2)) + (c * f (0 - a / 2)) =
      c * (f (0 + a / 2) + f (0 - a / 2))
  rw [zero_add, zero_sub, ← mul_add]

/-- Pointwise vanishing of the prime defect on zero. -/
theorem primePacketTranslationDefect_zero_pointwise (p : ℕ) (n : ℕ) (a : ℝ) :
    primePacketTranslationDefect p n (0 : ZetaTestFunction) a = 0 := by
  unfold primePacketTranslationDefect translationDefect
  change (0 : ℂ) - 0 = 0
  rw [sub_eq_add_neg, neg_zero, zero_add]

/-- Pointwise vanishing of the archimedean defect on zero. -/
theorem archimedeanTranslationDefect_zero_pointwise (a : ℝ) :
    archimedeanTranslationDefect a (0 : ZetaTestFunction) 0 = 0 := by
  unfold archimedeanTranslationDefect
  change (0 : ℂ) + 0 = 0
  rw [zero_add]

/-- The completed explicit-formula package is the linear core plus the fixed correction. -/
theorem toExplicitFormulaDefectPackage_eq_linear_add_correction (f : ZetaTestFunction) :
    toExplicitFormulaDefectPackage f =
      { primeDefect := fun p n => (toExplicitFormulaLinearDefectPackage f).primeDefect p n
        archimedeanDefect := fun a => (toExplicitFormulaLinearDefectPackage f).archimedeanDefect a
        correctionDefect := zetaCompletionCorrection 0 } := by
  rfl

/-- The linear core of the explicit-formula package of a sum is the sum of the linear cores. -/
theorem toExplicitFormulaLinearDefectPackage_add (f g : ZetaTestFunction) :
    toExplicitFormulaLinearDefectPackage (f + g) =
      toExplicitFormulaLinearDefectPackage f + toExplicitFormulaLinearDefectPackage g := by
  ext p n a
  · exact primePacketTranslationDefect_add_pointwise f g p n a
  · exact archimedeanTranslationDefect_add_pointwise p f g

/-- The linear core of the explicit-formula package of a scalar multiple is the scalar multiple
of the linear core. -/
theorem toExplicitFormulaLinearDefectPackage_smul (c : ℂ) (f : ZetaTestFunction) :
    toExplicitFormulaLinearDefectPackage (c • f) = c • toExplicitFormulaLinearDefectPackage f := by
  ext p n a
  · exact primePacketTranslationDefect_smul_pointwise c f p n a
  · exact archimedeanTranslationDefect_smul_pointwise p c f

/-- The linear core of the explicit-formula package commutes with finite sums. -/
theorem toExplicitFormulaLinearDefectPackage_sum_insert {α : Type*} [DecidableEq α]
    (a : α) (s : Finset α) (ha : a ∉ s) (f : α → ZetaTestFunction) :
    toExplicitFormulaLinearDefectPackage (∑ b in insert a s, f b) =
      toExplicitFormulaLinearDefectPackage (f a) +
        toExplicitFormulaLinearDefectPackage (∑ b in s, f b) := by
  rw [Finset.sum_insert ha]
  exact toExplicitFormulaLinearDefectPackage_add (f a) (∑ b in s, f b)

/-- The linear core of the explicit-formula package commutes with finite sums. -/
theorem toExplicitFormulaLinearDefectPackage_sum {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ZetaTestFunction) :
    toExplicitFormulaLinearDefectPackage (∑ a in s, f a) =
      ∑ a in s, toExplicitFormulaLinearDefectPackage (f a) := by
  induction s using Finset.induction_on with
  | empty =>
      ext p n a
      · exact primePacketTranslationDefect_zero_pointwise p n a
      · exact archimedeanTranslationDefect_zero_pointwise p
  | @insert a s ha ih =>
      calc
        toExplicitFormulaLinearDefectPackage (∑ b in insert a s, f b) =
            toExplicitFormulaLinearDefectPackage (f a) +
              toExplicitFormulaLinearDefectPackage (∑ b in s, f b) := by
              exact toExplicitFormulaLinearDefectPackage_sum_insert a s ha f
        _ = toExplicitFormulaLinearDefectPackage (f a) +
              ∑ b in s, toExplicitFormulaLinearDefectPackage (f b) := by
              rw [ih]
        _ = ∑ b in insert a s, toExplicitFormulaLinearDefectPackage (f b) := by
              rw [Finset.sum_insert ha]

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
  change archimedeanTranslationDefect a (reflect f) 0 = archimedeanTranslationDefect a f 0
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
  change archimedeanTranslationDefect a (reflect f) 0 = archimedeanTranslationDefect a f 0
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

-- The completed package is affine in `f`; only the linear core has a genuine module structure.

end ZetaTestFunction

end
end LFunctions
end Boundary
