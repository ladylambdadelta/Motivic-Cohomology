import Mathlib.Data.Complex.Basic

/-!
# Fixed real-part vertical points

This subowner contains the fixed vertical-line point primitive and its coordinate
identities.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.fixedRealPartVerticalPoint (a b : ℝ) : ℂ :=
  (a : ℂ) + (b : ℂ) * Complex.I

/-- The fixed-line point has real coordinate `a`. -/
theorem Complex.fixedRealPartVerticalPoint_re
    (a b : ℝ) :
    (Complex.fixedRealPartVerticalPoint a b).re = a := by
  calc
    (Complex.fixedRealPartVerticalPoint a b).re =
        ((a : ℂ) + (b : ℂ) * Complex.I).re := rfl
    _ = (a : ℂ).re + ((b : ℂ) * Complex.I).re :=
        Complex.add_re (a : ℂ) ((b : ℂ) * Complex.I)
    _ = a + 0 := by
      congr 1
      calc
        ((b : ℂ) * Complex.I).re = -((b : ℂ).im) :=
          Complex.mul_I_re (b : ℂ)
        _ = -0 :=
          congrArg Neg.neg (Complex.ofReal_im b)
        _ = 0 :=
          neg_zero
    _ = a := add_zero a

/-- The fixed-line point has imaginary coordinate `b`. -/
theorem Complex.fixedRealPartVerticalPoint_im
    (a b : ℝ) :
    (Complex.fixedRealPartVerticalPoint a b).im = b := by
  calc
    (Complex.fixedRealPartVerticalPoint a b).im =
        ((a : ℂ) + (b : ℂ) * Complex.I).im := rfl
    _ = (a : ℂ).im + ((b : ℂ) * Complex.I).im :=
        Complex.add_im (a : ℂ) ((b : ℂ) * Complex.I)
    _ = 0 + b := by
      congr 1
      exact Complex.mul_I_im (b : ℂ)
    _ = b := zero_add b

/-- A complex number is its fixed-real-part vertical point. -/
theorem Complex.fixedRealPartVerticalPoint_re_im
    (z : ℂ) :
    Complex.fixedRealPartVerticalPoint z.re z.im = z := by
  exact Complex.ext
    (Complex.fixedRealPartVerticalPoint_re z.re z.im)
    (Complex.fixedRealPartVerticalPoint_im z.re z.im)

end
end LFunctions
end Boundary
