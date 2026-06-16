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

theorem real_add_zero_half (x : ℝ) : x + (0 : ℝ) / 2 = x := by
  calc
    x + (0 : ℝ) / 2 = x + 0 := by
      exact congrArg (fun y : ℝ => x + y) (zero_div 2)
    _ = x := add_zero x

theorem real_sub_zero_half (x : ℝ) : x - (0 : ℝ) / 2 = x := by
  calc
    x - (0 : ℝ) / 2 = x - 0 := by
      exact congrArg (fun y : ℝ => x - y) (zero_div 2)
    _ = x := sub_zero x

theorem real_add_neg_half_eq_sub_half (x a : ℝ) :
    x + (-a) / 2 = x - a / 2 := by
  calc
    x + (-a) / 2 = x + (-(a / 2)) := by
      exact congrArg (fun y : ℝ => x + y) (neg_div 2 a)
    _ = x - a / 2 := (sub_eq_add_neg x (a / 2)).symm

theorem real_sub_neg_half_eq_add_half (x a : ℝ) :
    x - (-a) / 2 = x + a / 2 := by
  calc
    x - (-a) / 2 = x - (-(a / 2)) := by
      exact congrArg (fun y : ℝ => x - y) (neg_div 2 a)
    _ = x + a / 2 := sub_neg_eq_add x (a / 2)

theorem real_neg_add_half (x a : ℝ) :
    -(x + a / 2) = -x - a / 2 := by
  calc
    -(x + a / 2) = -x + -(a / 2) := neg_add x (a / 2)
    _ = -x - a / 2 := (sub_eq_add_neg (-x) (a / 2)).symm

theorem real_neg_sub_half (x a : ℝ) :
    -(x - a / 2) = -x + a / 2 := by
  calc
    -(x - a / 2) = a / 2 - x := neg_sub x (a / 2)
    _ = a / 2 + -x := sub_eq_add_neg (a / 2) x
    _ = -x + a / 2 := add_comm (a / 2) (-x)

theorem translationDefect_add_apply (a : ℝ) (f g : ZetaTestFunction) (x : ℝ) :
    translationDefect a (f + g) x = translationDefect a f x + translationDefect a g x := by
  unfold translationDefect
  have hnegative :
      -(f (x - a / 2) + g (x - a / 2)) =
        -f (x - a / 2) + -g (x - a / 2) :=
    neg_add (f (x - a / 2)) (g (x - a / 2))
  calc
    (f (x + a / 2) + g (x + a / 2)) - (f (x - a / 2) + g (x - a / 2)) =
        (f (x + a / 2) + g (x + a / 2)) +
          (-f (x - a / 2) + -g (x - a / 2)) := by
          exact (sub_eq_add_neg _ _).trans
            (congrArg
              (fun y : ℂ => (f (x + a / 2) + g (x + a / 2)) + y)
              hnegative)
    _ = (f (x + a / 2) + -f (x - a / 2)) + (g (x + a / 2) + -g (x - a / 2)) := by
          ac_rfl

theorem translationDefect_zero (f : ZetaTestFunction) :
    translationDefect 0 f = fun _ => 0 := by
  funext x
  unfold translationDefect
  have hx1 : x + (0 : ℝ) / 2 = x := real_add_zero_half x
  have hx2 : x - (0 : ℝ) / 2 = x := real_sub_zero_half x
  calc
    f (x + (0 : ℝ) / 2) - f (x - (0 : ℝ) / 2) =
        f x - f (x - (0 : ℝ) / 2) := by
      exact congrArg (fun y : ℂ => y - f (x - (0 : ℝ) / 2)) (congrArg f hx1)
    _ = f x - f x := by
      exact congrArg (fun y : ℂ => f x - y) (congrArg f hx2)
    _ = 0 := sub_self (f x)

theorem translationDefect_reflect (a : ℝ) (f : ZetaTestFunction) :
    translationDefect a (reflect f) = fun x => - translationDefect a f (-x) := by
  ext x
  unfold translationDefect reflect
  have hleft : -(x + a / 2) = -x - a / 2 := real_neg_add_half x a
  have hright : -(x - a / 2) = -x + a / 2 := real_neg_sub_half x a
  calc
    f (-(x + a / 2)) - f (-(x - a / 2)) =
        f (-x - a / 2) - f (-(x - a / 2)) := by
      exact congrArg (fun y : ℂ => y - f (-(x - a / 2))) (congrArg f hleft)
    _ = f (-x - a / 2) - f (-x + a / 2) := by
      exact congrArg (fun y : ℂ => f (-x - a / 2) - y) (congrArg f hright)
    _ = -(f (-x + a / 2) - f (-x - a / 2)) := by
      exact (neg_sub (f (-x + a / 2)) (f (-x - a / 2))).symm

theorem translationDefect_neg (a : ℝ) (f : ZetaTestFunction) :
    translationDefect (-a) f = fun x => - translationDefect a f x := by
  ext x
  unfold translationDefect
  have hx1 : x + (-a) / 2 = x - a / 2 := real_add_neg_half_eq_sub_half x a
  have hx2 : x - (-a) / 2 = x + a / 2 := real_sub_neg_half_eq_add_half x a
  calc
    f (x + (-a) / 2) - f (x - (-a) / 2)
        = f (x - a / 2) - f (x - (-a) / 2) := by
            exact congrArg (fun y : ℂ => y - f (x - (-a) / 2)) (congrArg f hx1)
    _ = f (x - a / 2) - f (x + a / 2) := by
            exact congrArg (fun y : ℂ => f (x - a / 2) - y) (congrArg f hx2)
    _ = -(f (x + a / 2) - f (x - a / 2)) := by
          exact (neg_sub (f (x + a / 2)) (f (x - a / 2))).symm

theorem translationDefect_smul_apply (a : ℝ) (c : ℂ) (f : ZetaTestFunction) (x : ℝ) :
    translationDefect a (c • f) x = c * translationDefect a f x := by
  unfold translationDefect
  have hneg : -(c * f (x - a / 2)) = c * -f (x - a / 2) :=
    (mul_neg c (f (x - a / 2))).symm
  calc
    c * f (x + a / 2) - c * f (x - a / 2) =
        c * f (x + a / 2) + -(c * f (x - a / 2)) := by
          exact (sub_eq_add_neg _ _)
    _ = c * f (x + a / 2) + c * -f (x - a / 2) := by
          exact congrArg (fun y : ℂ => c * f (x + a / 2) + y) hneg
    _ = c * (f (x + a / 2) + -f (x - a / 2)) := by
          exact (mul_add c (f (x + a / 2)) (-f (x - a / 2))).symm

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
  exact congrArg (fun a => translationDefect a f) (zetaPrimePacketCenter_pow (p := p) n)

theorem primePacketTranslationDefect_succ (p : ℝ) (n : ℕ) (f : ZetaTestFunction) :
    primePacketTranslationDefect p (n + 1) f =
      translationDefect (zetaPrimePacketCenter p n + Real.log p) f := by
  unfold primePacketTranslationDefect
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := Nat.cast_add_one n
  have hcenter_cast :
      zetaPrimePacketCenter p ((n + 1 : ℕ) : ℝ) =
        zetaPrimePacketCenter p ((n : ℝ) + 1) := by
    exact congrArg (fun y : ℝ => zetaPrimePacketCenter p y) hcast
  have hcenter_succ :
      zetaPrimePacketCenter p ((n : ℝ) + 1) =
        zetaPrimePacketCenter p n + Real.log p :=
    zetaPrimePacketCenter_succ (p := p) (n := n)
  exact congrArg (fun a => translationDefect a f)
    (hcenter_cast.trans hcenter_succ)

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
  have hx1 : x + (0 : ℝ) / 2 = x := real_add_zero_half x
  have hx2 : x - (0 : ℝ) / 2 = x := real_sub_zero_half x
  calc
    f (x + (0 : ℝ) / 2) + f (x - (0 : ℝ) / 2) =
        f x + f (x - (0 : ℝ) / 2) := by
      exact congrArg (fun y : ℂ => y + f (x - (0 : ℝ) / 2)) (congrArg f hx1)
    _ = f x + f x := by
      exact congrArg (fun y : ℂ => f x + y) (congrArg f hx2)
    _ = 2 * f x := by
      exact (two_mul (f x)).symm

theorem archimedeanTranslationDefect_reflect (a : ℝ) (f : ZetaTestFunction) :
    archimedeanTranslationDefect a (reflect f) = fun x => archimedeanTranslationDefect a f (-x) := by
  ext x
  unfold archimedeanTranslationDefect reflect
  have hleft : -(x + a / 2) = -x - a / 2 := real_neg_add_half x a
  have hright : -(x - a / 2) = -x + a / 2 := real_neg_sub_half x a
  calc
    f (-(x + a / 2)) + f (-(x - a / 2)) =
        f (-x - a / 2) + f (-(x - a / 2)) := by
      exact congrArg (fun y : ℂ => y + f (-(x - a / 2))) (congrArg f hleft)
    _ = f (-x - a / 2) + f (-x + a / 2) := by
      exact congrArg (fun y : ℂ => f (-x - a / 2) + y) (congrArg f hright)
    _ = f (-x + a / 2) + f (-x - a / 2) := add_comm (f (-x - a / 2)) (f (-x + a / 2))

theorem archimedeanTranslationDefect_reflect_zero (a : ℝ) (f : ZetaTestFunction) :
    archimedeanTranslationDefect a (reflect f) 0 = archimedeanTranslationDefect a f 0 := by
  have h := congrFun (archimedeanTranslationDefect_reflect a f) 0
  calc
    archimedeanTranslationDefect a (reflect f) 0 =
        archimedeanTranslationDefect a f (-0) := h
    _ = archimedeanTranslationDefect a f 0 := by
      exact congrArg (fun y : ℝ => archimedeanTranslationDefect a f y) (neg_zero : -(0 : ℝ) = 0)

theorem archimedeanTranslationDefect_neg (a : ℝ) (f : ZetaTestFunction) :
    archimedeanTranslationDefect (-a) f = archimedeanTranslationDefect a f := by
  ext x
  unfold archimedeanTranslationDefect
  have hx1 : x + (-a) / 2 = x - a / 2 := real_add_neg_half_eq_sub_half x a
  have hx2 : x - (-a) / 2 = x + a / 2 := real_sub_neg_half_eq_add_half x a
  calc
    f (x + (-a) / 2) + f (x - (-a) / 2)
        = f (x - a / 2) + f (x - (-a) / 2) := by
            exact congrArg (fun y : ℂ => y + f (x - (-a) / 2)) (congrArg f hx1)
    _ = f (x - a / 2) + f (x + a / 2) := by
            exact congrArg (fun y : ℂ => f (x - a / 2) + y) (congrArg f hx2)
    _ = f (x + a / 2) + f (x - a / 2) := by
          exact add_comm (f (x - a / 2)) (f (x + a / 2))

theorem archimedeanTranslationDefect_smul_apply (a : ℝ) (c : ℂ) (f : ZetaTestFunction)
    (x : ℝ) :
    archimedeanTranslationDefect a (c • f) x = c * archimedeanTranslationDefect a f x := by
  unfold archimedeanTranslationDefect
  change
    (c * f (x + a / 2)) + (c * f (x - a / 2)) =
      c * (f (x + a / 2) + f (x - a / 2))
  exact Eq.symm (mul_add c (f (x + a / 2)) (f (x - a / 2)))

theorem archimedeanTranslationDefect_zero_apply (a : ℝ) (x : ℝ) :
    archimedeanTranslationDefect a (0 : ZetaTestFunction) x = 0 := by
  unfold archimedeanTranslationDefect
  change (0 : ℂ) + 0 = 0
  exact add_zero 0

end ZetaTestFunction

end
end LFunctions
end Boundary
