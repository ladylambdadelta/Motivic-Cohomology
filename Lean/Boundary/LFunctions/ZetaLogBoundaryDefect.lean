import Boundary.LFunctions.ZetaTestFunction
import Boundary.LFunctions.ZetaCenteredNormalization

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

theorem translationDefect_zero (f : ZetaTestFunction) :
    translationDefect 0 f = fun _ => 0 := by
  funext x
  unfold translationDefect
  rw [show x + (0 : ℝ) / 2 = x by ring, show x - (0 : ℝ) / 2 = x by ring]
  ring

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

theorem archimedeanTranslationDefect_zero (f : ZetaTestFunction) :
    archimedeanTranslationDefect 0 f = fun x => 2 * f x := by
  ext x
  unfold archimedeanTranslationDefect
  rw [show x + (0 : ℝ) / 2 = x by ring, show x - (0 : ℝ) / 2 = x by ring]
  ring

theorem archimedeanTranslationDefect_reflect (a : ℝ) (f : ZetaTestFunction) :
    archimedeanTranslationDefect a (reflect f) = fun x => archimedeanTranslationDefect a f (-x) := by
  ext x
  unfold archimedeanTranslationDefect reflect
  ring_nf

theorem archimedeanTranslationDefect_neg (a : ℝ) (f : ZetaTestFunction) :
    archimedeanTranslationDefect (-a) f = archimedeanTranslationDefect a f := by
  ext x
  unfold archimedeanTranslationDefect
  rw [show x + (-a) / 2 = x - a / 2 by ring]
  rw [show x - (-a) / 2 = x + a / 2 by ring]
  ring

end ZetaTestFunction

end
end LFunctions
end Boundary
