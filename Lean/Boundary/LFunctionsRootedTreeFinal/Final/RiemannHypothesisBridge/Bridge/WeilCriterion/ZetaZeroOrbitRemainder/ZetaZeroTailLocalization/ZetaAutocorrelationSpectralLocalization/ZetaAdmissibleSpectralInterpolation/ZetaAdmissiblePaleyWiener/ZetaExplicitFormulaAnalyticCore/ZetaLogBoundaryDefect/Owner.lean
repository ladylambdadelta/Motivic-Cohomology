import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaTestFunction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPacketLabels.ZetaCenteredNormalization.Owner

/-!
# Boundary logarithmic boundary defects

This file isolates the logarithmic-line translation defects used by the
explicit-formula route. The prime-side packet construction is built from
centered translations by `± a / 2`, with `a = m * log p`.

The file is intentionally concrete: the only operations here are the existing
reflection/translation/scaling operations on `ZetaTestFunction` and the
resulting translation-defect identities.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaTestFunction

/-- The centered translation defect at logarithmic displacement `a`. -/
def translationDefect (a : ℝ) (f : ZetaTestFunction) : ℝ → ℂ :=
  fun x => f (x + a / 2) - f (x - a / 2)

theorem translationDefect_apply (a : ℝ) (f : ZetaTestFunction) (x : ℝ) :
    translationDefect a f x = f (x + a / 2) - f (x - a / 2) := by
  rfl

theorem translationDefect_add_apply (a : ℝ) (f g : ZetaTestFunction) (x : ℝ) :
    translationDefect a (f + g) x = translationDefect a f x + translationDefect a g x := by
  unfold translationDefect
  calc
    (f (x + a / 2) + g (x + a / 2)) - (f (x - a / 2) + g (x - a / 2)) =
        (f (x + a / 2) + g (x + a / 2)) +
          (-f (x - a / 2) + -g (x - a / 2)) := by
          rw [sub_eq_add_neg, neg_add]
    _ = (f (x + a / 2) + -f (x - a / 2)) + (g (x + a / 2) + -g (x - a / 2)) := by
          ac_rfl

theorem translationDefect_zero (f : ZetaTestFunction) :
    translationDefect 0 f = fun _ => 0 := by
  funext x
  unfold translationDefect
  rw [show x + 0 / 2 = x by norm_num, show x - 0 / 2 = x by norm_num]
  exact sub_self (f x)

theorem translationDefect_reflect (a : ℝ) (f : ZetaTestFunction) :
    translationDefect a (reflect f) = fun x => - translationDefect a f (-x) := by
  ext x
  unfold translationDefect reflect
  ring_nf

theorem translationDefect_neg (a : ℝ) (f : ZetaTestFunction) :
    translationDefect (-a) f = fun x => - translationDefect a f x := by
  ext x
  unfold translationDefect
  rw [show x + (-a) / 2 = x - a / 2 by ring]
  rw [show x - (-a) / 2 = x + a / 2 by ring]
  ring

theorem translationDefect_smul_apply (a : ℝ) (c : ℂ) (f : ZetaTestFunction) (x : ℝ) :
    translationDefect a (c • f) x = c * translationDefect a f x := by
  unfold translationDefect
  calc
    c * f (x + a / 2) - c * f (x - a / 2) =
        c * f (x + a / 2) + -(c * f (x - a / 2)) := by
          rw [sub_eq_add_neg]
    _ = c * (f (x + a / 2) + -f (x - a / 2)) := by
          rw [← mul_neg, ← mul_add]

theorem translationDefect_zero_apply (a : ℝ) (x : ℝ) :
    translationDefect a (0 : ZetaTestFunction) x = 0 := by
  unfold translationDefect
  change (0 : ℂ) - 0 = 0
  exact sub_self 0

/-- The prime-side translation defect at the logarithmic prime-power center. -/
def primePacketTranslationDefect (p : ℝ) (n : ℕ) (f : ZetaTestFunction) : ℝ → ℂ :=
  translationDefect (zetaPrimePacketCenter p n) f

theorem primePacketTranslationDefect_apply (p : ℝ) (n : ℕ) (f : ZetaTestFunction) (x : ℝ) :
    primePacketTranslationDefect p n f x =
      f (x + zetaPrimePacketCenter p n / 2) -
        f (x - zetaPrimePacketCenter p n / 2) := by
  rfl

theorem primePacketTranslationDefect_pow (p : ℝ) (n : ℕ) (f : ZetaTestFunction) :
    primePacketTranslationDefect p n f =
      translationDefect (Real.log (p ^ n)) f := by
  unfold primePacketTranslationDefect
  rw [zetaPrimePacketCenter_pow]

theorem primePacketTranslationDefect_succ (p : ℝ) (n : ℕ) (f : ZetaTestFunction) :
    primePacketTranslationDefect p (n + 1) f =
      translationDefect (zetaPrimePacketCenter p n + Real.log p) f := by
  rw [primePacketTranslationDefect]
  norm_num
  exact congrArg (fun a => translationDefect a f)
    (zetaPrimePacketCenter_succ (p := p) (n := n))

/-- Reflection compatibility for the prime-side logarithmic translation defect. -/
theorem primePacketTranslationDefect_reflect (p : ℝ) (n : ℕ) (f : ZetaTestFunction) :
    primePacketTranslationDefect p n (reflect f) =
      fun x => - primePacketTranslationDefect p n f (-x) := by
  unfold primePacketTranslationDefect
  exact translationDefect_reflect (zetaPrimePacketCenter p n) f

/-- The archimedean translation defect at displacement `a`. -/
def archimedeanTranslationDefect (a : ℝ) (f : ZetaTestFunction) : ℝ → ℂ :=
  fun x => f (x + a / 2) + f (x - a / 2)

theorem archimedeanTranslationDefect_apply (a : ℝ) (f : ZetaTestFunction) (x : ℝ) :
    archimedeanTranslationDefect a f x = f (x + a / 2) + f (x - a / 2) := by
  rfl

theorem archimedeanTranslationDefect_add_apply (a : ℝ) (f g : ZetaTestFunction) (x : ℝ) :
    archimedeanTranslationDefect a (f + g) x =
      archimedeanTranslationDefect a f x + archimedeanTranslationDefect a g x := by
  unfold archimedeanTranslationDefect
  change
    f (x + a / 2) + g (x + a / 2) + (f (x - a / 2) + g (x - a / 2)) =
      (f (x + a / 2) + f (x - a / 2)) + (g (x + a / 2) + g (x - a / 2))
  ac_rfl

theorem archimedeanTranslationDefect_zero (f : ZetaTestFunction) :
    archimedeanTranslationDefect 0 f = fun x => 2 * f x := by
  ext x
  unfold archimedeanTranslationDefect
  rw [show x + 0 / 2 = x by norm_num, show x - 0 / 2 = x by norm_num]
  exact (two_mul (f x)).symm

theorem archimedeanTranslationDefect_reflect (a : ℝ) (f : ZetaTestFunction) :
    archimedeanTranslationDefect a (reflect f) = fun x => archimedeanTranslationDefect a f (-x) := by
  ext x
  unfold archimedeanTranslationDefect reflect
  ring_nf

theorem archimedeanTranslationDefect_reflect_zero (a : ℝ) (f : ZetaTestFunction) :
    archimedeanTranslationDefect a (reflect f) 0 = archimedeanTranslationDefect a f 0 := by
  have h := congrFun (archimedeanTranslationDefect_reflect a f) 0
  rw [neg_zero] at h
  exact h

theorem archimedeanTranslationDefect_neg (a : ℝ) (f : ZetaTestFunction) :
    archimedeanTranslationDefect (-a) f = archimedeanTranslationDefect a f := by
  ext x
  unfold archimedeanTranslationDefect
  rw [show x + (-a) / 2 = x - a / 2 by ring]
  rw [show x - (-a) / 2 = x + a / 2 by ring]
  ring

theorem archimedeanTranslationDefect_smul_apply (a : ℝ) (c : ℂ) (f : ZetaTestFunction)
    (x : ℝ) :
    archimedeanTranslationDefect a (c • f) x = c * archimedeanTranslationDefect a f x := by
  unfold archimedeanTranslationDefect
  change
    (c * f (x + a / 2)) + (c * f (x - a / 2)) =
      c * (f (x + a / 2) + f (x - a / 2))
  rw [← mul_add]

theorem archimedeanTranslationDefect_zero_apply (a : ℝ) (x : ℝ) :
    archimedeanTranslationDefect a (0 : ZetaTestFunction) x = 0 := by
  unfold archimedeanTranslationDefect
  change (0 : ℂ) + 0 = 0
  exact add_zero 0

end ZetaTestFunction

end
end LFunctions
end Boundary
