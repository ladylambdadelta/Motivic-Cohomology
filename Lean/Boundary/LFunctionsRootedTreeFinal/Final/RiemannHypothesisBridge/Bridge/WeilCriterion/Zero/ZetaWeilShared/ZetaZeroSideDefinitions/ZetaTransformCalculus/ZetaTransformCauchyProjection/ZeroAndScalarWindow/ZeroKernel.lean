import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.NegativeContour.Owner

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

noncomputable def scalarFourierLaplacePlemelj_unweightedWindowMulExp
    (a T x : ℝ) : ℂ :=
  (∫ t in Set.Icc (-T) T,
    (-1 / ((a : ℂ) + t * Complex.I)) *
      Complex.exp
        (Complex.I * (t : ℂ) * (x : ℂ))) *
    Complex.exp ((a : ℂ) * (x : ℂ))

/-- The normalized scalar finite-window Cauchy integral unfolds to the window integral
times the compensating exponential. -/
theorem scalarFourierLaplacePlemelj_unweightedWindowMulExp_eq
    (a T x : ℝ) :
    scalarFourierLaplacePlemelj_unweightedWindowMulExp a T x =
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp ((a : ℂ) * (x : ℂ)) := by
  rfl

/-- The quadratic denominator in the zero-time Cauchy kernel is strictly
positive. -/
theorem scalarFourierLaplacePlemelj_zero_denominator_pos
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    0 < a ^ 2 + t ^ 2 :=
  add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)

/-- The quadratic denominator in the zero-time Cauchy kernel is nonzero. -/
theorem scalarFourierLaplacePlemelj_zero_denominator_ne_zero
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    a ^ 2 + t ^ 2 ≠ 0 :=
  ne_of_gt
    (scalarFourierLaplacePlemelj_zero_denominator_pos a ha t)

/-- Pointwise algebraic decomposition of the zero-time Cauchy kernel into its
real even part and imaginary odd part. -/
theorem scalarFourierLaplacePlemelj_zero_kernel_pointwise_decomposition
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    (-1 / ((a : ℂ) + t * Complex.I)) =
      ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) +
        (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
  have hden_pos : 0 < a ^ 2 + t ^ 2 :=
    scalarFourierLaplacePlemelj_zero_denominator_pos a ha t
  have hden_ne : a ^ 2 + t ^ 2 ≠ 0 :=
    ne_of_gt hden_pos
  have hz_ne : ((a : ℂ) + t * Complex.I) ≠ 0 := by
    intro hz
    have hre : (((a : ℂ) + t * Complex.I).re) = (0 : ℂ).re :=
      congrArg Complex.re hz
    have ha_zero : a = 0 := by
      have hleft : (((a : ℂ) + t * Complex.I).re) = a := by
        calc
          (((a : ℂ) + t * Complex.I).re) =
              (a : ℂ).re + (t * Complex.I).re :=
            Complex.add_re (a : ℂ) (t * Complex.I)
          _ = a + (t * Complex.I).re :=
            congrArg (fun y : ℝ => y + (t * Complex.I).re)
              (Complex.ofReal_re a)
          _ = a + ((t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im) :=
            congrArg (fun y : ℝ => a + y)
              (Complex.mul_re (t : ℂ) Complex.I)
          _ = a + (t * Complex.I.re - (t : ℂ).im * Complex.I.im) :=
            congrArg
              (fun y : ℝ => a + (y * Complex.I.re - (t : ℂ).im * Complex.I.im))
              (Complex.ofReal_re t)
          _ = a + (t * 0 - (t : ℂ).im * Complex.I.im) :=
            congrArg (fun y : ℝ => a + (t * y - (t : ℂ).im * Complex.I.im))
              Complex.I_re
          _ = a + (0 - (t : ℂ).im * Complex.I.im) :=
            congrArg (fun y : ℝ => a + (y - (t : ℂ).im * Complex.I.im))
              (mul_zero t)
          _ = a + (0 - 0 * Complex.I.im) :=
            congrArg (fun y : ℝ => a + (0 - y * Complex.I.im))
              (Complex.ofReal_im t)
          _ = a + (0 - 0) :=
            congrArg (fun y : ℝ => a + (0 - 0 * y)) Complex.I_im
          _ = a + 0 :=
            congrArg (fun y : ℝ => a + y) (sub_self (0 : ℝ))
          _ = a := add_zero a
      exact hleft.symm.trans (hre.trans Complex.zero_re)
    exact (ne_of_gt ha) ha_zero
  have hnorm :
      Complex.normSq ((a : ℂ) + t * Complex.I) = a ^ 2 + t ^ 2 :=
    Complex.normSq_add_mul_I a t
  have hre_z : (((a : ℂ) + t * Complex.I).re) = a := by
    calc
      (((a : ℂ) + t * Complex.I).re) =
          (a : ℂ).re + (t * Complex.I).re :=
        Complex.add_re (a : ℂ) (t * Complex.I)
      _ = a + (t * Complex.I).re :=
        congrArg (fun y : ℝ => y + (t * Complex.I).re)
          (Complex.ofReal_re a)
      _ = a + ((t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im) :=
        congrArg (fun y : ℝ => a + y)
          (Complex.mul_re (t : ℂ) Complex.I)
      _ = a + (t * Complex.I.re - (t : ℂ).im * Complex.I.im) :=
        congrArg
          (fun y : ℝ => a + (y * Complex.I.re - (t : ℂ).im * Complex.I.im))
          (Complex.ofReal_re t)
      _ = a + (t * 0 - (t : ℂ).im * Complex.I.im) :=
        congrArg (fun y : ℝ => a + (t * y - (t : ℂ).im * Complex.I.im))
          Complex.I_re
      _ = a + (0 - (t : ℂ).im * Complex.I.im) :=
        congrArg (fun y : ℝ => a + (y - (t : ℂ).im * Complex.I.im))
          (mul_zero t)
      _ = a + (0 - 0 * Complex.I.im) :=
        congrArg (fun y : ℝ => a + (0 - y * Complex.I.im))
          (Complex.ofReal_im t)
      _ = a + (0 - 0) :=
        congrArg (fun y : ℝ => a + (0 - 0 * y)) Complex.I_im
      _ = a + 0 :=
        congrArg (fun y : ℝ => a + y) (sub_self (0 : ℝ))
      _ = a := add_zero a
  have him_z : (((a : ℂ) + t * Complex.I).im) = t := by
    calc
      (((a : ℂ) + t * Complex.I).im) =
          (a : ℂ).im + (t * Complex.I).im :=
        Complex.add_im (a : ℂ) (t * Complex.I)
      _ = 0 + (t * Complex.I).im :=
        congrArg (fun y : ℝ => y + (t * Complex.I).im)
          (Complex.ofReal_im a)
      _ = 0 + ((t : ℂ).re * Complex.I.im + (t : ℂ).im * Complex.I.re) :=
        congrArg (fun y : ℝ => 0 + y)
          (Complex.mul_im (t : ℂ) Complex.I)
      _ = 0 + (t * Complex.I.im + (t : ℂ).im * Complex.I.re) :=
        congrArg
          (fun y : ℝ => 0 + (y * Complex.I.im + (t : ℂ).im * Complex.I.re))
          (Complex.ofReal_re t)
      _ = 0 + (t * 1 + (t : ℂ).im * Complex.I.re) :=
        congrArg (fun y : ℝ => 0 + (t * y + (t : ℂ).im * Complex.I.re))
          Complex.I_im
      _ = 0 + (t * 1 + 0 * Complex.I.re) :=
        congrArg (fun y : ℝ => 0 + (t * 1 + y * Complex.I.re))
          (Complex.ofReal_im t)
      _ = 0 + (t * 1 + 0) :=
        congrArg (fun y : ℝ => 0 + (t * 1 + 0 * y)) Complex.I_re
      _ = 0 + (t * 1) :=
        congrArg (fun y : ℝ => 0 + y) (add_zero (t * 1))
      _ = 0 + t :=
        congrArg (fun y : ℝ => 0 + y) (mul_one t)
      _ = t := zero_add t
  have hre_rhs :
      ((((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) +
        (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I)).re) =
        -(a / (a ^ 2 + t ^ 2)) := by
    calc
      ((((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) +
        (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I)).re) =
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ).re +
            ((((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I).re) :=
        Complex.add_re
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ)
          (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I)
      _ = (-(a / (a ^ 2 + t ^ 2))) +
            ((((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I).re) :=
        congrArg
          (fun y : ℝ =>
            y + ((((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I).re))
          (Complex.ofReal_re (-(a / (a ^ 2 + t ^ 2))))
      _ = (-(a / (a ^ 2 + t ^ 2))) +
            ((t / (a ^ 2 + t ^ 2) : ℂ).re * Complex.I.re -
              (t / (a ^ 2 + t ^ 2) : ℂ).im * Complex.I.im) :=
        congrArg (fun y : ℝ => (-(a / (a ^ 2 + t ^ 2))) + y)
          (Complex.mul_re
            ((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) Complex.I)
      _ = (-(a / (a ^ 2 + t ^ 2))) +
            ((t / (a ^ 2 + t ^ 2)) * Complex.I.re -
              (t / (a ^ 2 + t ^ 2) : ℂ).im * Complex.I.im) := by
        exact congrArg
          (fun y : ℝ =>
            (-(a / (a ^ 2 + t ^ 2))) +
              (y * Complex.I.re -
                (t / (a ^ 2 + t ^ 2) : ℂ).im * Complex.I.im))
          (Complex.ofReal_re (t / (a ^ 2 + t ^ 2)))
      _ = (-(a / (a ^ 2 + t ^ 2))) +
            ((t / (a ^ 2 + t ^ 2)) * 0 -
              (t / (a ^ 2 + t ^ 2) : ℂ).im * Complex.I.im) := by
        exact congrArg
          (fun y : ℝ =>
            (-(a / (a ^ 2 + t ^ 2))) +
              ((t / (a ^ 2 + t ^ 2)) * y -
                (t / (a ^ 2 + t ^ 2) : ℂ).im * Complex.I.im))
          Complex.I_re
      _ = (-(a / (a ^ 2 + t ^ 2))) +
            (0 - (t / (a ^ 2 + t ^ 2) : ℂ).im * Complex.I.im) := by
        exact congrArg
          (fun y : ℝ =>
            (-(a / (a ^ 2 + t ^ 2))) +
              (y - (t / (a ^ 2 + t ^ 2) : ℂ).im * Complex.I.im))
          (mul_zero (t / (a ^ 2 + t ^ 2)))
      _ = (-(a / (a ^ 2 + t ^ 2))) +
            (0 - 0 * Complex.I.im) := by
        exact congrArg
          (fun y : ℝ =>
            (-(a / (a ^ 2 + t ^ 2))) + (0 - y * Complex.I.im))
          (Complex.ofReal_im (t / (a ^ 2 + t ^ 2)))
      _ = (-(a / (a ^ 2 + t ^ 2))) + (0 - 0) := by
        exact congrArg
          (fun y : ℝ =>
            (-(a / (a ^ 2 + t ^ 2))) + (0 - 0 * y))
          Complex.I_im
      _ = (-(a / (a ^ 2 + t ^ 2))) + 0 := by
        exact congrArg
          (fun y : ℝ => (-(a / (a ^ 2 + t ^ 2))) + y)
          (sub_self (0 : ℝ))
      _ = -(a / (a ^ 2 + t ^ 2)) :=
        add_zero (-(a / (a ^ 2 + t ^ 2)))
  have him_rhs :
      ((((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) +
        (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I)).im) =
        t / (a ^ 2 + t ^ 2) := by
    calc
      ((((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) +
        (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I)).im) =
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ).im +
            ((((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I).im) :=
        Complex.add_im
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ)
          (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I)
      _ = 0 + ((((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I).im) :=
        congrArg
          (fun y : ℝ =>
            y + ((((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I).im))
          (Complex.ofReal_im (-(a / (a ^ 2 + t ^ 2))))
      _ = 0 + ((t / (a ^ 2 + t ^ 2) : ℂ).re * Complex.I.im +
              (t / (a ^ 2 + t ^ 2) : ℂ).im * Complex.I.re) :=
        congrArg (fun y : ℝ => 0 + y)
          (Complex.mul_im
            ((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) Complex.I)
      _ = 0 + ((t / (a ^ 2 + t ^ 2)) * Complex.I.im +
              (t / (a ^ 2 + t ^ 2) : ℂ).im * Complex.I.re) := by
        exact congrArg
          (fun y : ℝ =>
            0 + (y * Complex.I.im +
              (t / (a ^ 2 + t ^ 2) : ℂ).im * Complex.I.re))
          (Complex.ofReal_re (t / (a ^ 2 + t ^ 2)))
      _ = 0 + ((t / (a ^ 2 + t ^ 2)) * 1 +
              (t / (a ^ 2 + t ^ 2) : ℂ).im * Complex.I.re) := by
        exact congrArg
          (fun y : ℝ =>
            0 + ((t / (a ^ 2 + t ^ 2)) * y +
              (t / (a ^ 2 + t ^ 2) : ℂ).im * Complex.I.re))
          Complex.I_im
      _ = 0 + ((t / (a ^ 2 + t ^ 2)) * 1 +
              0 * Complex.I.re) := by
        exact congrArg
          (fun y : ℝ =>
            0 + ((t / (a ^ 2 + t ^ 2)) * 1 + y * Complex.I.re))
          (Complex.ofReal_im (t / (a ^ 2 + t ^ 2)))
      _ = 0 + ((t / (a ^ 2 + t ^ 2)) * 1 + 0) := by
        exact congrArg
          (fun y : ℝ =>
            0 + ((t / (a ^ 2 + t ^ 2)) * 1 + 0 * y))
          Complex.I_re
      _ = 0 + ((t / (a ^ 2 + t ^ 2)) * 1) := by
        exact congrArg (fun y : ℝ => 0 + y)
          (add_zero ((t / (a ^ 2 + t ^ 2)) * 1))
      _ = 0 + (t / (a ^ 2 + t ^ 2)) := by
        exact congrArg (fun y : ℝ => 0 + y)
          (mul_one (t / (a ^ 2 + t ^ 2)))
      _ = t / (a ^ 2 + t ^ 2) :=
        zero_add (t / (a ^ 2 + t ^ 2))
  have hre_left :
      ((-1 / ((a : ℂ) + t * Complex.I)).re) =
        -(a / (a ^ 2 + t ^ 2)) := by
    calc
      ((-1 / ((a : ℂ) + t * Complex.I)).re) =
          (-1 : ℂ).re * (((a : ℂ) + t * Complex.I).re) /
              Complex.normSq ((a : ℂ) + t * Complex.I) +
            (-1 : ℂ).im * (((a : ℂ) + t * Complex.I).im) /
              Complex.normSq ((a : ℂ) + t * Complex.I) :=
        Complex.div_re (-1 : ℂ) ((a : ℂ) + t * Complex.I)
      _ =
          (-(1 : ℝ)) * a / (a ^ 2 + t ^ 2) +
            0 * t / (a ^ 2 + t ^ 2) := by
        exact congrArg₂ HAdd.hAdd
          (congrArg₂ HDiv.hDiv
            (congrArg₂ HMul.hMul
              (Complex.neg_re 1 |>.trans
                (congrArg Neg.neg (Complex.one_re)))
              hre_z)
            hnorm)
          (congrArg₂ HDiv.hDiv
            (congrArg₂ HMul.hMul
              (Complex.neg_im 1 |>.trans
                (congrArg Neg.neg (Complex.one_im)))
              him_z)
            hnorm)
      _ =
          (-(a : ℝ)) / (a ^ 2 + t ^ 2) +
            0 * t / (a ^ 2 + t ^ 2) := by
        exact congrArg
          (fun y : ℝ => y / (a ^ 2 + t ^ 2) +
            0 * t / (a ^ 2 + t ^ 2))
          (neg_mul (1 : ℝ) a |>.trans
            (congrArg Neg.neg (one_mul a)))
      _ =
          (-(a : ℝ)) / (a ^ 2 + t ^ 2) + 0 := by
        exact congrArg
          (fun y : ℝ => (-(a : ℝ)) / (a ^ 2 + t ^ 2) + y)
          (zero_mul t ▸ zero_div (a ^ 2 + t ^ 2))
      _ =
          (-(a : ℝ)) / (a ^ 2 + t ^ 2) :=
        add_zero ((-(a : ℝ)) / (a ^ 2 + t ^ 2))
      _ = -(a / (a ^ 2 + t ^ 2)) :=
        neg_div a (a ^ 2 + t ^ 2)
  have him_left :
      ((-1 / ((a : ℂ) + t * Complex.I)).im) =
        t / (a ^ 2 + t ^ 2) := by
    calc
      ((-1 / ((a : ℂ) + t * Complex.I)).im) =
          (-1 : ℂ).im * (((a : ℂ) + t * Complex.I).re) /
              Complex.normSq ((a : ℂ) + t * Complex.I) -
            (-1 : ℂ).re * (((a : ℂ) + t * Complex.I).im) /
              Complex.normSq ((a : ℂ) + t * Complex.I) :=
        Complex.div_im (-1 : ℂ) ((a : ℂ) + t * Complex.I)
      _ =
          0 * a / (a ^ 2 + t ^ 2) -
            (-(1 : ℝ)) * t / (a ^ 2 + t ^ 2) := by
        exact congrArg₂ HSub.hSub
          (congrArg₂ HDiv.hDiv
            (congrArg₂ HMul.hMul
              (Complex.neg_im 1 |>.trans
                (congrArg Neg.neg (Complex.one_im)))
              hre_z)
            hnorm)
          (congrArg₂ HDiv.hDiv
            (congrArg₂ HMul.hMul
              (Complex.neg_re 1 |>.trans
                (congrArg Neg.neg (Complex.one_re)))
              him_z)
            hnorm)
      _ =
          0 - (-(t : ℝ)) / (a ^ 2 + t ^ 2) := by
        exact congrArg₂ HSub.hSub
          (zero_mul a ▸ zero_div (a ^ 2 + t ^ 2))
          (congrArg
            (fun y : ℝ => y / (a ^ 2 + t ^ 2))
            (neg_mul (1 : ℝ) t |>.trans
              (congrArg Neg.neg (one_mul t))))
      _ =
          -((-(t : ℝ)) / (a ^ 2 + t ^ 2)) :=
        zero_sub ((-(t : ℝ)) / (a ^ 2 + t ^ 2))
      _ =
          -(-(t / (a ^ 2 + t ^ 2))) := by
        exact congrArg Neg.neg (neg_div t (a ^ 2 + t ^ 2))
      _ =
          t / (a ^ 2 + t ^ 2) :=
        neg_neg (t / (a ^ 2 + t ^ 2))
  exact Complex.ext (hre_left.trans hre_rhs.symm) (him_left.trans him_rhs.symm)

/-- The odd imaginary part of the zero-time symmetric Cauchy window cancels. -/
theorem scalarFourierLaplacePlemelj_zero_odd_imaginary_integral_eq_zero
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    ∫ t in Set.Icc (-T) T,
      (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) = 0 := by
  let f : ℝ → ℂ :=
    fun t : ℝ => (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I)
  have hodd : ∀ t : ℝ, f (-t) = -f t := by
    intro t
    unfold f
    have hden :
        a ^ 2 + (-t) ^ 2 = a ^ 2 + t ^ 2 := by
      have hneg_sq : (-t) ^ 2 = t ^ 2 := by
        calc
          (-t) ^ 2 = (-t) * (-t) := pow_two (-t)
          _ = t * t := neg_mul_neg t t
          _ = t ^ 2 := (pow_two t).symm
      exact congrArg (fun y : ℝ => a ^ 2 + y) hneg_sq
    calc
      ((((-t) / (a ^ 2 + (-t) ^ 2) : ℝ) : ℂ) * Complex.I)
          =
          ((((-t) / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
            exact congrArg
              (fun y : ℝ => ((y : ℂ) * Complex.I))
              (congrArg (fun d : ℝ => (-t) / d) hden)
      _ =
          -(((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
            calc
              ((((-t) / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I)
                  =
                  (((-(t / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) * Complex.I) := by
                    exact congrArg
                      (fun y : ℝ => ((y : ℂ) * Complex.I))
                      (neg_div t (a ^ 2 + t ^ 2))
              _ =
                  (-(((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ)) * Complex.I) := by
                    exact congrArg
                      (fun z : ℂ => z * Complex.I)
                      (Complex.ofReal_neg (t / (a ^ 2 + t ^ 2)))
              _ =
                  -(((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
                    exact neg_mul (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ)) Complex.I
  have hcomp :
      (∫ t in (-T)..T, f (-t)) = ∫ t in (-T)..T, f t := by
    have hraw :
        (∫ t in (-T)..T, f (-t)) =
          ∫ t in (-T)..(-(-T)), f t :=
      intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := T)
    calc
      (∫ t in (-T)..T, f (-t)) =
          ∫ t in (-T)..(-(-T)), f t := hraw
      _ = ∫ t in (-T)..T, f t := by
        exact congrArg (fun b : ℝ => ∫ t in (-T)..b, f t) (neg_neg T)
  have hneg :
      (∫ t in (-T)..T, f (-t)) = -∫ t in (-T)..T, f t := by
    calc
      (∫ t in (-T)..T, f (-t))
          = ∫ t in (-T)..T, -f t := by
            exact intervalIntegral.integral_congr
              (Filter.Eventually.of_forall hodd)
      _ = -∫ t in (-T)..T, f t := by
            exact intervalIntegral.integral_neg
  have hself_neg : (∫ t in (-T)..T, f t) = -∫ t in (-T)..T, f t :=
    hcomp.symm.trans hneg
  have htwo_zero : (2 : ℂ) * (∫ t in (-T)..T, f t) = 0 := by
    have hsum_zero :
        (∫ t in (-T)..T, f t) + (∫ t in (-T)..T, f t) = 0 := by
      calc
        (∫ t in (-T)..T, f t) + (∫ t in (-T)..T, f t)
            =
            -(∫ t in (-T)..T, f t) + (∫ t in (-T)..T, f t) := by
              exact congrArg
                (fun z : ℂ => z + (∫ t in (-T)..T, f t))
                hself_neg
        _ = 0 := by
            exact neg_add_cancel (∫ t in (-T)..T, f t)
    exact (two_mul (∫ t in (-T)..T, f t)).trans hsum_zero
  have htwo_ne : (2 : ℂ) ≠ 0 :=
    two_ne_zero
  exact mul_eq_zero.mp htwo_zero |>.resolve_left htwo_ne

/-- The even real part of the zero-time symmetric Cauchy window has the
arctangent primitive value. -/
theorem scalarFourierLaplacePlemelj_zero_real_kernel_integral_eq_arctan
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    ∫ t in Set.Icc (-T) T,
      ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) =
      (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hreal :
      (∫ t in (-T)..T, (-(a / (a ^ 2 + t ^ 2)) : ℝ)) =
        -(2 : ℝ) * Real.arctan (T / a) := by
    have hscale :
        (∫ u in (-(T / a))..(T / a),
          (-(1 : ℝ) / (1 + u ^ 2))) =
          -(2 : ℝ) * Real.arctan (T / a) := by
      let r : ℝ := T / a
      have hneg_integrand :
          (∫ u in (-(T / a))..(T / a),
            (-(1 : ℝ) / (1 + u ^ 2))) =
            -∫ u in (-(T / a))..(T / a),
              ((1 : ℝ) + u ^ 2)⁻¹ := by
        have hpoint :
            ∀ u : ℝ,
              (-(1 : ℝ) / (1 + u ^ 2)) =
                -(((1 : ℝ) + u ^ 2)⁻¹) := by
          intro u
          calc
            (-(1 : ℝ) / (1 + u ^ 2)) =
                -((1 : ℝ) / (1 + u ^ 2)) :=
              neg_div (1 : ℝ) (1 + u ^ 2)
            _ = -(((1 : ℝ) + u ^ 2)⁻¹) := by
              exact congrArg Neg.neg (one_div ((1 : ℝ) + u ^ 2))
        calc
          (∫ u in (-(T / a))..(T / a),
            (-(1 : ℝ) / (1 + u ^ 2))) =
              ∫ u in (-(T / a))..(T / a),
                -(((1 : ℝ) + u ^ 2)⁻¹) := by
            exact intervalIntegral.integral_congr
              (Filter.Eventually.of_forall hpoint)
          _ =
              -∫ u in (-(T / a))..(T / a),
                ((1 : ℝ) + u ^ 2)⁻¹ :=
            intervalIntegral.integral_neg
      have harctan_algebra :
          -(Real.arctan r - Real.arctan (-r)) =
            -(2 : ℝ) * Real.arctan r := by
        calc
          -(Real.arctan r - Real.arctan (-r)) =
              -(Real.arctan r - -Real.arctan r) := by
            exact congrArg
              (fun y : ℝ => -(Real.arctan r - y))
              (Real.arctan_neg r)
          _ = -(Real.arctan r + Real.arctan r) := by
            exact congrArg Neg.neg (sub_neg_eq_add (Real.arctan r) (Real.arctan r))
          _ = -(2 * Real.arctan r) := by
            exact congrArg Neg.neg (two_mul (Real.arctan r)).symm
          _ = -(2 : ℝ) * Real.arctan r :=
            neg_mul 2 (Real.arctan r)
      calc
        (∫ u in (-(T / a))..(T / a),
          (-(1 : ℝ) / (1 + u ^ 2)))
            = -∫ u in (-(T / a))..(T / a),
                ((1 : ℝ) + u ^ 2)⁻¹ := hneg_integrand
        _ = -(Real.arctan (T / a) - Real.arctan (-(T / a))) := by
              exact congrArg Neg.neg
                (Real.integral_inv_one_add_sq
                  (a := -(T / a)) (b := T / a))
        _ = -(2 : ℝ) * Real.arctan (T / a) := by
              exact harctan_algebra
    have hsub :
        (∫ t in (-T)..T, (-(a / (a ^ 2 + t ^ 2)) : ℝ)) =
          ∫ u in (-(T / a))..(T / a),
            (-(1 : ℝ) / (1 + u ^ 2)) := by
      have hcomp :=
        intervalIntegral.smul_integral_comp_mul_left
          (f := fun t : ℝ => (-(a / (a ^ 2 + t ^ 2)) : ℝ))
          a
      have hpoint :
          ∀ u : ℝ,
            a • (-(a / (a ^ 2 + (a * u) ^ 2)) : ℝ) =
              (-(1 : ℝ) / (1 + u ^ 2)) := by
        intro u
        have ha_sq_ne : a ^ 2 ≠ 0 :=
          pow_ne_zero 2 ha_ne
        have hden :
            a ^ 2 + (a * u) ^ 2 = a ^ 2 * (1 + u ^ 2) := by
          have hmul_sq : (a * u) ^ 2 = a ^ 2 * u ^ 2 :=
            mul_pow a u 2
          calc
            a ^ 2 + (a * u) ^ 2 =
                a ^ 2 + a ^ 2 * u ^ 2 := by
              exact congrArg (fun y : ℝ => a ^ 2 + y) hmul_sq
            _ = a ^ 2 * 1 + a ^ 2 * u ^ 2 := by
              exact congrArg (fun y : ℝ => y + a ^ 2 * u ^ 2)
                (mul_one (a ^ 2)).symm
            _ = a ^ 2 * (1 + u ^ 2) := by
              exact (mul_add (a ^ 2) 1 (u ^ 2)).symm
        calc
          a • (-(a / (a ^ 2 + (a * u) ^ 2)) : ℝ)
              = a * (-(a / (a ^ 2 + (a * u) ^ 2))) := by
                rfl
          _ = -(a * (a / (a ^ 2 + (a * u) ^ 2))) := by
                exact mul_neg a (a / (a ^ 2 + (a * u) ^ 2))
          _ = -((a * a) / (a ^ 2 + (a * u) ^ 2)) := by
                exact congrArg Neg.neg
                  (mul_div_assoc a a (a ^ 2 + (a * u) ^ 2))
          _ = -(a ^ 2 / (a ^ 2 + (a * u) ^ 2)) := by
                exact congrArg
                  (fun y : ℝ => -(y / (a ^ 2 + (a * u) ^ 2)))
                  (pow_two a).symm
          _ = -(a ^ 2 / (a ^ 2 * (1 + u ^ 2))) := by
                exact congrArg (fun y : ℝ => -(a ^ 2 / y)) hden
          _ = -((a ^ 2 * 1) / (a ^ 2 * (1 + u ^ 2))) := by
                exact congrArg
                  (fun y : ℝ => -(y / (a ^ 2 * (1 + u ^ 2))))
                  (mul_one (a ^ 2)).symm
          _ = -(1 / (1 + u ^ 2)) := by
                exact congrArg Neg.neg
                  (mul_div_mul_left 1 (1 + u ^ 2) ha_sq_ne)
          _ = -(1 : ℝ) / (1 + u ^ 2) := by
                exact (neg_div (1 : ℝ) (1 + u ^ 2)).symm
      have hleft : a * (-(T / a)) = -T := by
        calc
          a * (-(T / a)) = -(a * (T / a)) := by
            exact mul_neg a (T / a)
          _ = -T := by
            exact congrArg Neg.neg (mul_div_cancel₀ T ha_ne)
      have hright : a * (T / a) = T :=
        mul_div_cancel₀ T ha_ne
      calc
        (∫ t in (-T)..T, (-(a / (a ^ 2 + t ^ 2)) : ℝ))
            =
            ∫ t in (a * (-(T / a)))..(a * (T / a)),
              (-(a / (a ^ 2 + t ^ 2)) : ℝ) := by
              exact congrArg₂
                (fun l r : ℝ =>
                  ∫ t in l..r, (-(a / (a ^ 2 + t ^ 2)) : ℝ))
                hleft.symm hright.symm
        _ =
            a • ∫ u in (-(T / a))..(T / a),
              (-(a / (a ^ 2 + (a * u) ^ 2)) : ℝ) := by
              exact Eq.symm hcomp
        _ =
            ∫ u in (-(T / a))..(T / a),
              a •
                (-(a / (a ^ 2 + (a * u) ^ 2)) : ℝ) := by
              exact (intervalIntegral.integral_smul
                (a := -(T / a)) (b := T / a)
                (r := a)
                (f := fun u : ℝ =>
                  (-(a / (a ^ 2 + (a * u) ^ 2)) : ℝ))).symm
        _ =
            ∫ u in (-(T / a))..(T / a),
              (-(1 : ℝ) / (1 + u ^ 2)) := by
              exact intervalIntegral.integral_congr
                (Filter.Eventually.of_forall hpoint)
    exact hsub.trans hscale
  calc
    (∫ t in Set.Icc (-T) T,
      ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ))
        =
        ∫ t in (-T)..T,
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) := by
          rfl
    _ =
        ((∫ t in (-T)..T,
          (-(a / (a ^ 2 + t ^ 2)) : ℝ)) : ℂ) := by
          exact intervalIntegral.integral_ofReal
    _ =
        (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
          exact congrArg (fun y : ℝ => (y : ℂ)) hreal

/-- Interval integrability of the even real part of the zero-time Cauchy
kernel on symmetric finite windows. -/
theorem scalarFourierLaplacePlemelj_zero_real_kernel_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hquot_cont : Continuous (fun t : ℝ => a / (a ^ 2 + t ^ 2)) :=
    continuous_const.div hden_cont
      (scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha)
  have hreal_cont :
      Continuous (fun t : ℝ => (-(a / (a ^ 2 + t ^ 2)) : ℝ)) :=
    hquot_cont.neg
  exact (Complex.continuous_ofReal.comp hreal_cont).intervalIntegrable (-T) T

/-- Interval integrability of the odd imaginary part of the zero-time Cauchy
kernel on symmetric finite windows. -/
theorem scalarFourierLaplacePlemelj_zero_odd_imaginary_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hquot_cont : Continuous (fun t : ℝ => t / (a ^ 2 + t ^ 2)) :=
    continuous_id.div hden_cont
      (scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha)
  have hcomplex_cont :
      Continuous
        (fun t : ℝ => ((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hquot_cont
  exact (hcomplex_cont.mul continuous_const).intervalIntegrable (-T) T

/-- Zero-time symmetric Cauchy window before multiplying by the trivial
endpoint exponential factors. -/
end FixedLineCauchyProjection

end
end Boundary
