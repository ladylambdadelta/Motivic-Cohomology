import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaRectangularCollarsBasic

/-!
# Half-turn and split geometry for rectangular collars

This file owns the half-turn transport, primitive boundary bookkeeping, and
tangent-box cap decomposition for finite-height Abel-Plana collars.  The basic
collar domains and boundary-integral definitions live in
`BinetAbelPlanaRectangularCollarsBasic`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter MeasureTheory

/-- Half-turn through the center `c`.  This is the holomorphic rotation that
identifies the left and right indentation collars. -/
noncomputable def Complex.halfTurnAbout
    (c z : ℂ) : ℂ :=
  2 * c - z

/-- Pullback of a function by the half-turn through `c`. -/
noncomputable def Complex.halfTurnPullback
    (c : ℂ)
    (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z : ℂ => f (Complex.halfTurnAbout c z)

/-- The half-turn is translation by the vector from `z` back to the center. -/
theorem Complex.halfTurnAbout_eq_center_add_center_sub
    (c z : ℂ) :
    Complex.halfTurnAbout c z = c + (c - z) := by
  unfold Complex.halfTurnAbout
  calc
    2 * c - z = (c + c) - z := by
      exact congrArg (fun w : ℂ => w - z) (two_mul c)
    _ = c + (c - z) :=
      add_sub_assoc c c z

/-- The half-turn sends `c + v` to `c - v`. -/
theorem Complex.halfTurnAbout_add_vector
    (c v : ℂ) :
    Complex.halfTurnAbout c (c + v) = c - v := by
  unfold Complex.halfTurnAbout
  calc
    2 * c - (c + v) = (c + c) - (c + v) := by
      exact congrArg (fun z : ℂ => z - (c + v)) (two_mul c)
    _ = c - v :=
      add_sub_add_left_eq_sub c v c

/-- Real coordinate of scalar multiplication by `2` on `ℂ`. -/
theorem Complex.two_mul_re
    (c : ℂ) :
    (2 * c).re = 2 * c.re := by
  calc
    (2 * c).re = (2 : ℂ).re * c.re - (2 : ℂ).im * c.im :=
      Complex.mul_re (2 : ℂ) c
    _ = 2 * c.re - 0 * c.im := rfl
    _ = 2 * c.re - 0 := by
      exact congrArg (fun t : ℝ => 2 * c.re - t) (zero_mul c.im)
    _ = 2 * c.re :=
      sub_zero (2 * c.re)

/-- Imaginary coordinate of scalar multiplication by `2` on `ℂ`. -/
theorem Complex.two_mul_im
    (c : ℂ) :
    (2 * c).im = 2 * c.im := by
  calc
    (2 * c).im = (2 : ℂ).re * c.im + (2 : ℂ).im * c.re :=
      Complex.mul_im (2 : ℂ) c
    _ = 2 * c.im + 0 * c.re := rfl
    _ = 2 * c.im + 0 := by
      exact congrArg (fun t : ℝ => 2 * c.im + t) (zero_mul c.re)
    _ = 2 * c.im :=
      add_zero (2 * c.im)

/-- Real coordinate of the half-turn through `c`. -/
theorem Complex.halfTurnAbout_re
    (c z : ℂ) :
    (Complex.halfTurnAbout c z).re = 2 * c.re - z.re := by
  unfold Complex.halfTurnAbout
  calc
    (2 * c - z).re = (2 * c).re - z.re :=
      Complex.sub_re (2 * c) z
    _ = 2 * c.re - z.re := by
      exact congrArg (fun t : ℝ => t - z.re) (Complex.two_mul_re c)

/-- Imaginary coordinate of the half-turn through `c`. -/
theorem Complex.halfTurnAbout_im
    (c z : ℂ) :
    (Complex.halfTurnAbout c z).im = 2 * c.im - z.im := by
  unfold Complex.halfTurnAbout
  calc
    (2 * c - z).im = (2 * c).im - z.im :=
      Complex.sub_im (2 * c) z
    _ = 2 * c.im - z.im := by
      exact congrArg (fun t : ℝ => t - z.im) (Complex.two_mul_im c)

/-- Half-turn through `c` preserves distance from `c`. -/
theorem Complex.dist_halfTurnAbout_center
    (c z : ℂ) :
    dist z c = dist (Complex.halfTurnAbout c z) c := by
  have hturn :
      Complex.halfTurnAbout c z = c + (c - z) :=
    Complex.halfTurnAbout_eq_center_add_center_sub c z
  have hleft :
      dist z c = ‖z - c‖ :=
    dist_eq_norm z c
  have hright :
      dist (Complex.halfTurnAbout c z) c = ‖c - z‖ := by
    calc
      dist (Complex.halfTurnAbout c z) c =
          ‖Complex.halfTurnAbout c z - c‖ :=
        dist_eq_norm (Complex.halfTurnAbout c z) c
      _ = ‖(c + (c - z)) - c‖ := by
        exact congrArg (fun w : ℂ => ‖w - c‖) hturn
      _ = ‖c - z‖ := by
        exact congrArg norm (add_sub_cancel_left c (c - z))
  calc
    dist z c = ‖z - c‖ :=
      hleft
    _ = ‖c - z‖ :=
      norm_sub_rev z c
    _ = dist (Complex.halfTurnAbout c z) c :=
      hright.symm

/-- Real coordinate of a point written as `x + I*y`. -/
theorem Complex.ofReal_add_I_mul_ofReal_re
    (x y : ℝ) :
    (((x : ℂ) + Complex.I * (y : ℂ))).re = x := by
  calc
    (((x : ℂ) + Complex.I * (y : ℂ))).re =
        (x : ℂ).re + (Complex.I * (y : ℂ)).re :=
      Complex.add_re (x : ℂ) (Complex.I * (y : ℂ))
    _ = x + (Complex.I * (y : ℂ)).re := by
      exact congrArg (fun t : ℝ => t + (Complex.I * (y : ℂ)).re)
        (Complex.ofReal_re x)
    _ = x + -(y : ℂ).im := by
      exact congrArg (fun t : ℝ => x + t) (Complex.I_mul_re (y : ℂ))
    _ = x + -0 := by
      exact congrArg (fun t : ℝ => x + -t) (Complex.ofReal_im y)
    _ = x + 0 := by
      exact congrArg (fun t : ℝ => x + t) (neg_zero)
    _ = x :=
      add_zero x

/-- Imaginary coordinate of a point written as `x + I*y`. -/
theorem Complex.ofReal_add_I_mul_ofReal_im
    (x y : ℝ) :
    (((x : ℂ) + Complex.I * (y : ℂ))).im = y := by
  calc
    (((x : ℂ) + Complex.I * (y : ℂ))).im =
        (x : ℂ).im + (Complex.I * (y : ℂ)).im :=
      Complex.add_im (x : ℂ) (Complex.I * (y : ℂ))
    _ = 0 + (Complex.I * (y : ℂ)).im := by
      exact congrArg (fun t : ℝ => t + (Complex.I * (y : ℂ)).im)
        (Complex.ofReal_im x)
    _ = 0 + (y : ℂ).re := by
      exact congrArg (fun t : ℝ => 0 + t) (Complex.I_mul_im (y : ℂ))
    _ = 0 + y := by
      exact congrArg (fun t : ℝ => 0 + t) (Complex.ofReal_re y)
    _ = y :=
      zero_add y

/-- Coordinate form of the half-turn on a point `x + I*y`. -/
theorem Complex.halfTurnAbout_ofReal_add_I_mul_ofReal
    (c : ℂ)
    (x y : ℝ) :
    Complex.halfTurnAbout c (((x : ℂ) + Complex.I * (y : ℂ))) =
      (((2 * c.re - x : ℝ) : ℂ) +
        Complex.I * (((2 * c.im - y : ℝ) : ℂ))) := by
  apply Complex.ext
  · calc
      (Complex.halfTurnAbout c (((x : ℂ) + Complex.I * (y : ℂ)))).re =
          2 * c.re - (((x : ℂ) + Complex.I * (y : ℂ))).re :=
        Complex.halfTurnAbout_re c (((x : ℂ) + Complex.I * (y : ℂ)))
      _ = 2 * c.re - x := by
        exact congrArg (fun t : ℝ => 2 * c.re - t)
          (Complex.ofReal_add_I_mul_ofReal_re x y)
      _ =
          ((((2 * c.re - x : ℝ) : ℂ) +
            Complex.I * (((2 * c.im - y : ℝ) : ℂ)))).re := by
        exact (Complex.ofReal_add_I_mul_ofReal_re
          (2 * c.re - x) (2 * c.im - y)).symm
  · calc
      (Complex.halfTurnAbout c (((x : ℂ) + Complex.I * (y : ℂ)))).im =
          2 * c.im - (((x : ℂ) + Complex.I * (y : ℂ))).im :=
        Complex.halfTurnAbout_im c (((x : ℂ) + Complex.I * (y : ℂ)))
      _ = 2 * c.im - y := by
        exact congrArg (fun t : ℝ => 2 * c.im - t)
          (Complex.ofReal_add_I_mul_ofReal_im x y)
      _ =
          ((((2 * c.re - x : ℝ) : ℂ) +
            Complex.I * (((2 * c.im - y : ℝ) : ℂ)))).im := by
        exact (Complex.ofReal_add_I_mul_ofReal_im
          (2 * c.re - x) (2 * c.im - y)).symm

/-- The lower side of the left collar is the half-turn image of the upper
side of the right collar at matching parameter `x`. -/
theorem Complex.halfTurnAbout_right_upper_point
    (c : ℂ)
    (ρ x : ℝ) :
    Complex.halfTurnAbout c
        (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) =
      (((2 * c.re - x : ℝ) : ℂ) +
        Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
  have him :
      2 * c.im - (c.im + ρ) = c.im - ρ := by
    calc
      2 * c.im - (c.im + ρ) =
          (c.im + c.im) - (c.im + ρ) := by
        exact congrArg (fun t : ℝ => t - (c.im + ρ)) (two_mul c.im)
      _ = c.im - ρ :=
        add_sub_add_left_eq_sub c.im ρ c.im
  calc
    Complex.halfTurnAbout c
        (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) =
        (((2 * c.re - x : ℝ) : ℂ) +
          Complex.I * (((2 * c.im - (c.im + ρ) : ℝ) : ℂ))) :=
      Complex.halfTurnAbout_ofReal_add_I_mul_ofReal c x (c.im + ρ)
    _ =
        (((2 * c.re - x : ℝ) : ℂ) +
          Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
      exact congrArg
        (fun t : ℝ =>
          (((2 * c.re - x : ℝ) : ℂ) + Complex.I * ((t : ℝ) : ℂ)))
        him

/-- The upper side of the left collar is the half-turn image of the lower
side of the right collar at matching parameter `x`. -/
theorem Complex.halfTurnAbout_right_lower_point
    (c : ℂ)
    (ρ x : ℝ) :
    Complex.halfTurnAbout c
        (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) =
      (((2 * c.re - x : ℝ) : ℂ) +
        Complex.I * ((c.im + ρ : ℝ) : ℂ)) := by
  have him :
      2 * c.im - (c.im - ρ) = c.im + ρ := by
    have hcancel :
        (c.im + c.im) + -c.im = c.im := by
      calc
        (c.im + c.im) + -c.im = (c.im + c.im) - c.im :=
          (sub_eq_add_neg (c.im + c.im) c.im).symm
        _ = c.im :=
          add_sub_cancel_right c.im c.im
    have hneg_sub :
        -(c.im - ρ) = -c.im + ρ := by
      calc
        -(c.im - ρ) = ρ - c.im :=
          neg_sub c.im ρ
        _ = ρ + -c.im :=
          sub_eq_add_neg ρ c.im
        _ = -c.im + ρ :=
          add_comm ρ (-c.im)
    calc
      2 * c.im - (c.im - ρ) =
          (c.im + c.im) - (c.im - ρ) := by
        exact congrArg (fun t : ℝ => t - (c.im - ρ)) (two_mul c.im)
      _ = (c.im + c.im) + -(c.im - ρ) :=
        sub_eq_add_neg (c.im + c.im) (c.im - ρ)
      _ = (c.im + c.im) + (-c.im + ρ) := by
        exact congrArg (fun t : ℝ => (c.im + c.im) + t) hneg_sub
      _ = ((c.im + c.im) + -c.im) + ρ :=
        (add_assoc (c.im + c.im) (-c.im) ρ).symm
      _ = c.im + ρ := by
        exact congrArg (fun t : ℝ => t + ρ) hcancel
  calc
    Complex.halfTurnAbout c
        (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) =
        (((2 * c.re - x : ℝ) : ℂ) +
          Complex.I * (((2 * c.im - (c.im - ρ) : ℝ) : ℂ))) :=
      Complex.halfTurnAbout_ofReal_add_I_mul_ofReal c x (c.im - ρ)
    _ =
        (((2 * c.re - x : ℝ) : ℂ) +
          Complex.I * ((c.im + ρ : ℝ) : ℂ)) := by
      exact congrArg
        (fun t : ℝ =>
          (((2 * c.re - x : ℝ) : ℂ) + Complex.I * ((t : ℝ) : ℂ)))
        him

/-- The safe vertical side of the left collar is the half-turn image of the
safe vertical side of the right collar at matching parameter `y`. -/
theorem Complex.halfTurnAbout_right_vertical_point
    (c : ℂ)
    (a y : ℝ) :
    Complex.halfTurnAbout c
        (((c.re + a : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ)) =
      (((c.re - a : ℝ) : ℂ) +
        Complex.I * ((2 * c.im - y : ℝ) : ℂ)) := by
  have hre :
      2 * c.re - (c.re + a) = c.re - a := by
    calc
      2 * c.re - (c.re + a) =
          (c.re + c.re) - (c.re + a) := by
        exact congrArg (fun t : ℝ => t - (c.re + a)) (two_mul c.re)
      _ = c.re - a :=
        add_sub_add_left_eq_sub c.re a c.re
  calc
    Complex.halfTurnAbout c
        (((c.re + a : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ)) =
        (((2 * c.re - (c.re + a) : ℝ) : ℂ) +
          Complex.I * (((2 * c.im - y : ℝ) : ℂ))) :=
      Complex.halfTurnAbout_ofReal_add_I_mul_ofReal c (c.re + a) y
    _ =
        (((c.re - a : ℝ) : ℂ) +
          Complex.I * ((2 * c.im - y : ℝ) : ℂ)) := by
      exact congrArg
        (fun t : ℝ =>
          (((t : ℝ) : ℂ) + Complex.I * ((2 * c.im - y : ℝ) : ℂ)))
        hre

/-- Exponential at the upper quarter-turn angle. -/
theorem Complex.exp_I_mul_pi_div_two_eq_I :
    Complex.exp (Complex.I * (((Real.pi / 2 : ℝ) : ℂ))) = Complex.I := by
  apply Complex.ext
  · calc
      (Complex.exp (Complex.I * (((Real.pi / 2 : ℝ) : ℂ)))).re =
          (Complex.exp ((((Real.pi / 2 : ℝ) : ℂ)) * Complex.I)).re := by
        exact congrArg Complex.re
          (congrArg Complex.exp
            (mul_comm Complex.I (((Real.pi / 2 : ℝ) : ℂ))))
      _ = Real.cos (Real.pi / 2) :=
        Complex.exp_ofReal_mul_I_re (Real.pi / 2)
      _ = 0 :=
        Real.cos_pi_div_two
      _ = Complex.I.re :=
        Complex.I_re.symm
  · calc
      (Complex.exp (Complex.I * (((Real.pi / 2 : ℝ) : ℂ)))).im =
          (Complex.exp ((((Real.pi / 2 : ℝ) : ℂ)) * Complex.I)).im := by
        exact congrArg Complex.im
          (congrArg Complex.exp
            (mul_comm Complex.I (((Real.pi / 2 : ℝ) : ℂ))))
      _ = Real.sin (Real.pi / 2) :=
        Complex.exp_ofReal_mul_I_im (Real.pi / 2)
      _ = 1 :=
        Real.sin_pi_div_two
      _ = Complex.I.im :=
        Complex.I_im.symm

/-- Exponential at the lower quarter-turn angle. -/
theorem Complex.exp_I_mul_neg_pi_div_two_eq_neg_I :
    Complex.exp (Complex.I * (((-(Real.pi / 2) : ℝ) : ℂ))) = -Complex.I := by
  apply Complex.ext
  · calc
      (Complex.exp (Complex.I * (((-(Real.pi / 2) : ℝ) : ℂ)))).re =
          (Complex.exp ((((-(Real.pi / 2) : ℝ) : ℂ)) * Complex.I)).re := by
        exact congrArg Complex.re
          (congrArg Complex.exp
            (mul_comm Complex.I (((-(Real.pi / 2) : ℝ) : ℂ))))
      _ = Real.cos (-(Real.pi / 2)) :=
        Complex.exp_ofReal_mul_I_re (-(Real.pi / 2))
      _ = Real.cos (Real.pi / 2) :=
        Real.cos_neg (Real.pi / 2)
      _ = 0 :=
        Real.cos_pi_div_two
      _ = (-Complex.I).re := by
        calc
          (0 : ℝ) = -0 :=
            neg_zero.symm
          _ = -Complex.I.re :=
            congrArg Neg.neg Complex.I_re.symm
          _ = (-Complex.I).re :=
            (Complex.neg_re Complex.I).symm
  · calc
      (Complex.exp (Complex.I * (((-(Real.pi / 2) : ℝ) : ℂ)))).im =
          (Complex.exp ((((-(Real.pi / 2) : ℝ) : ℂ)) * Complex.I)).im := by
        exact congrArg Complex.im
          (congrArg Complex.exp
            (mul_comm Complex.I (((-(Real.pi / 2) : ℝ) : ℂ))))
      _ = Real.sin (-(Real.pi / 2)) :=
        Complex.exp_ofReal_mul_I_im (-(Real.pi / 2))
      _ = -Real.sin (Real.pi / 2) :=
        Real.sin_neg (Real.pi / 2)
      _ = -1 := by
        exact congrArg Neg.neg Real.sin_pi_div_two
      _ = (-Complex.I).im := by
        exact (Complex.neg_im Complex.I).symm.trans
          (congrArg Neg.neg Complex.I_im).symm

/-- Upper endpoint of the right semicircle parameterization. -/
theorem Complex.rightSemicircle_upper_endpoint
    (c : ℂ)
    (ρ : ℝ) :
    c + (ρ : ℂ) *
        Complex.exp (Complex.I * (((Real.pi / 2 : ℝ) : ℂ))) =
      (((c.re : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) := by
  have hexp :
      Complex.exp (Complex.I * (((Real.pi / 2 : ℝ) : ℂ))) =
        Complex.I :=
    Complex.exp_I_mul_pi_div_two_eq_I
  apply Complex.ext
  · calc
      (c + (ρ : ℂ) *
          Complex.exp (Complex.I * (((Real.pi / 2 : ℝ) : ℂ)))).re =
          c.re + ((ρ : ℂ) *
            Complex.exp (Complex.I * (((Real.pi / 2 : ℝ) : ℂ)))).re :=
        Complex.add_re c
          ((ρ : ℂ) *
            Complex.exp (Complex.I * (((Real.pi / 2 : ℝ) : ℂ))))
      _ = c.re + ((ρ : ℂ) * Complex.I).re := by
        exact congrArg (fun z : ℂ => c.re + ((ρ : ℂ) * z).re) hexp
      _ = c.re + -((ρ : ℂ).im) := by
        exact congrArg (fun t : ℝ => c.re + t)
          (Complex.mul_I_re (ρ : ℂ))
      _ = c.re + -0 := by
        exact congrArg (fun t : ℝ => c.re + -t) (Complex.ofReal_im ρ)
      _ = c.re + 0 := by
        exact congrArg (fun t : ℝ => c.re + t) neg_zero
      _ = c.re :=
        add_zero c.re
      _ =
          ((((c.re : ℝ) : ℂ) +
            Complex.I * ((c.im + ρ : ℝ) : ℂ))).re := by
        exact (Complex.ofReal_add_I_mul_ofReal_re c.re (c.im + ρ)).symm
  · calc
      (c + (ρ : ℂ) *
          Complex.exp (Complex.I * (((Real.pi / 2 : ℝ) : ℂ)))).im =
          c.im + ((ρ : ℂ) *
            Complex.exp (Complex.I * (((Real.pi / 2 : ℝ) : ℂ)))).im :=
        Complex.add_im c
          ((ρ : ℂ) *
            Complex.exp (Complex.I * (((Real.pi / 2 : ℝ) : ℂ))))
      _ = c.im + ((ρ : ℂ) * Complex.I).im := by
        exact congrArg (fun z : ℂ => c.im + ((ρ : ℂ) * z).im) hexp
      _ = c.im + (ρ : ℂ).re := by
        exact congrArg (fun t : ℝ => c.im + t)
          (Complex.mul_I_im (ρ : ℂ))
      _ = c.im + ρ := by
        exact congrArg (fun t : ℝ => c.im + t) (Complex.ofReal_re ρ)
      _ =
          ((((c.re : ℝ) : ℂ) +
            Complex.I * ((c.im + ρ : ℝ) : ℂ))).im := by
        exact (Complex.ofReal_add_I_mul_ofReal_im c.re (c.im + ρ)).symm

/-- Lower endpoint of the right semicircle parameterization. -/
theorem Complex.rightSemicircle_lower_endpoint
    (c : ℂ)
    (ρ : ℝ) :
    c + (ρ : ℂ) *
        Complex.exp (Complex.I * (((-(Real.pi / 2) : ℝ) : ℂ))) =
      (((c.re : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
  have hexp :
      Complex.exp (Complex.I * (((-(Real.pi / 2) : ℝ) : ℂ))) =
        -Complex.I :=
    Complex.exp_I_mul_neg_pi_div_two_eq_neg_I
  have hmul_neg :
      (ρ : ℂ) * (-Complex.I) = -((ρ : ℂ) * Complex.I) :=
    mul_neg (ρ : ℂ) Complex.I
  apply Complex.ext
  · calc
      (c + (ρ : ℂ) *
          Complex.exp (Complex.I * (((-(Real.pi / 2) : ℝ) : ℂ)))).re =
          c.re + ((ρ : ℂ) *
            Complex.exp (Complex.I * (((-(Real.pi / 2) : ℝ) : ℂ)))).re :=
        Complex.add_re c
          ((ρ : ℂ) *
            Complex.exp (Complex.I * (((-(Real.pi / 2) : ℝ) : ℂ))))
      _ = c.re + ((ρ : ℂ) * (-Complex.I)).re := by
        exact congrArg (fun z : ℂ => c.re + ((ρ : ℂ) * z).re) hexp
      _ = c.re + (-((ρ : ℂ) * Complex.I)).re := by
        exact congrArg (fun z : ℂ => c.re + z.re) hmul_neg
      _ = c.re + -(((ρ : ℂ) * Complex.I).re) := by
        exact congrArg (fun t : ℝ => c.re + t)
          (Complex.neg_re ((ρ : ℂ) * Complex.I))
      _ = c.re + -(-((ρ : ℂ).im)) := by
        exact congrArg (fun t : ℝ => c.re + -t)
          (Complex.mul_I_re (ρ : ℂ))
      _ = c.re + -(-0) := by
        exact congrArg (fun t : ℝ => c.re + -(-t)) (Complex.ofReal_im ρ)
      _ = c.re + -0 := by
        exact congrArg (fun t : ℝ => c.re + t)
          ((neg_neg (0 : ℝ)).trans neg_zero.symm)
      _ = c.re + 0 := by
        exact congrArg (fun t : ℝ => c.re + t) neg_zero
      _ = c.re :=
        add_zero c.re
      _ =
          ((((c.re : ℝ) : ℂ) +
            Complex.I * ((c.im - ρ : ℝ) : ℂ))).re := by
        exact (Complex.ofReal_add_I_mul_ofReal_re c.re (c.im - ρ)).symm
  · calc
      (c + (ρ : ℂ) *
          Complex.exp (Complex.I * (((-(Real.pi / 2) : ℝ) : ℂ)))).im =
          c.im + ((ρ : ℂ) *
            Complex.exp (Complex.I * (((-(Real.pi / 2) : ℝ) : ℂ)))).im :=
        Complex.add_im c
          ((ρ : ℂ) *
            Complex.exp (Complex.I * (((-(Real.pi / 2) : ℝ) : ℂ))))
      _ = c.im + ((ρ : ℂ) * (-Complex.I)).im := by
        exact congrArg (fun z : ℂ => c.im + ((ρ : ℂ) * z).im) hexp
      _ = c.im + (-((ρ : ℂ) * Complex.I)).im := by
        exact congrArg (fun z : ℂ => c.im + z.im) hmul_neg
      _ = c.im + -(((ρ : ℂ) * Complex.I).im) := by
        exact congrArg (fun t : ℝ => c.im + t)
          (Complex.neg_im ((ρ : ℂ) * Complex.I))
      _ = c.im + -((ρ : ℂ).re) := by
        exact congrArg (fun t : ℝ => c.im + -t)
          (Complex.mul_I_im (ρ : ℂ))
      _ = c.im + -ρ := by
        exact congrArg (fun t : ℝ => c.im + -t) (Complex.ofReal_re ρ)
      _ = c.im - ρ :=
        (sub_eq_add_neg c.im ρ).symm
      _ =
          ((((c.re : ℝ) : ℂ) +
            Complex.I * ((c.im - ρ : ℝ) : ℂ))).im := by
        exact (Complex.ofReal_add_I_mul_ofReal_im c.re (c.im - ρ)).symm

/-- The half-turn carries a circle point to the point whose angle is shifted
by `π`. -/
theorem Complex.halfTurnAbout_circlePoint_eq_add_pi
    (c : ℂ)
    (ρ : ℝ)
    (θ : ℝ) :
    Complex.halfTurnAbout c
        (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      c + (ρ : ℂ) *
        Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ))) := by
  have hturn :
      Complex.halfTurnAbout c
          (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        c - (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) :=
    Complex.halfTurnAbout_add_vector c
      ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  have hexp :
      Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ))) =
        -Complex.exp (Complex.I * (θ : ℂ)) :=
    Complex.exp_I_mul_ofReal_add_pi θ
  have hscaled :
      (ρ : ℂ) * Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ))) =
        -((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
    calc
      (ρ : ℂ) * Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ))) =
          (ρ : ℂ) * (-Complex.exp (Complex.I * (θ : ℂ))) := by
        exact congrArg (fun z : ℂ => (ρ : ℂ) * z) hexp
      _ = -((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
        mul_neg (ρ : ℂ) (Complex.exp (Complex.I * (θ : ℂ)))
  calc
    Complex.halfTurnAbout c
        (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        c - (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) :=
      hturn
    _ = c + (-((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :=
      sub_eq_add_neg c ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
    _ = c + (ρ : ℂ) *
        Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ))) := by
      exact congrArg (fun z : ℂ => c + z) hscaled.symm

/-- Multiplying by a negated right factor is canceled by the outer negation. -/
theorem Complex.mul_eq_neg_mul_neg_right
    (a b : ℂ) :
    a * b = -(a * (-b)) := by
  calc
    a * b = -(-(a * b)) :=
      (neg_neg (a * b)).symm
    _ = -(a * (-b)) := by
      exact congrArg Neg.neg (mul_neg a b).symm

/-- Splitting two subtractions over a binary sum. -/
theorem Complex.add_sub_sub_eq_sub_add_sub
    (x y a b : ℂ) :
    (x + y) - a - b = (x - a) + (y - b) := by
  calc
    (x + y) - a - b = (x + y) - (a + b) :=
      sub_sub (x + y) a b
    _ = (x + y) + -(a + b) :=
      sub_eq_add_neg (x + y) (a + b)
    _ = (x + y) + (-a + -b) := by
      exact congrArg (fun z : ℂ => (x + y) + z) (neg_add a b)
    _ = x + -a + (y + -b) :=
      add_add_add_comm x y (-a) (-b)
    _ = (x - a) + (y - b) := by
      exact congrArg₂
        (fun p q : ℂ => p + q)
        (sub_eq_add_neg x a).symm
        (sub_eq_add_neg y b).symm

/-- A term inserted in one summand and subtracted from the other cancels. -/
theorem Complex.add_canceling_split
    (x y t a : ℂ) :
    x + y - a = ((x + t) - a) + (y - t) := by
  have hsplit :
      ((x + t) - a) + (y - t) =
        ((x + t) + y) - a - t :=
    (Complex.add_sub_sub_eq_sub_add_sub (x + t) y a t).symm
  have hmove :
      (x + t) + y = (x + y) + t :=
    add_right_comm x t y
  have hcancel :
      ((x + t) + y) - a - t = x + y - a := by
    calc
      ((x + t) + y) - a - t =
          ((x + t) + y) - t - a :=
        sub_right_comm ((x + t) + y) a t
      _ = ((x + y) + t) - t - a := by
        exact congrArg (fun z : ℂ => z - t - a) hmove
      _ = (x + y) - a := by
        exact congrArg (fun z : ℂ => z - a)
          (add_sub_cancel_right (x + y) t)
  exact (Eq.trans hsplit hcancel).symm

/-- Algebraic orientation reversal for the left/right core boundary chains. -/
theorem Complex.leftRightCoreBoundary_neg_algebra
    (lower upper vertical arc : ℂ) :
    upper + -lower - vertical - -arc =
      -(lower + -upper + vertical - arc) := by
  have hinner :
      upper + -lower - vertical =
        -(lower + -upper + vertical) := by
    calc
      upper + -lower - vertical =
          (upper + -lower) + -vertical :=
        sub_eq_add_neg (upper + -lower) vertical
      _ = (-(-upper) + -lower) + -vertical := by
        exact congrArg (fun z : ℂ => (z + -lower) + -vertical)
          (neg_neg upper).symm
      _ = -(lower + -upper) + -vertical := by
        exact congrArg (fun z : ℂ => z + -vertical)
          (neg_add_rev lower (-upper)).symm
      _ = -(lower + -upper + vertical) :=
        (neg_add (lower + -upper) vertical).symm
  calc
    upper + -lower - vertical - -arc =
        (upper + -lower - vertical) + arc :=
      sub_neg_eq_add (upper + -lower - vertical) arc
    _ = arc + (upper + -lower - vertical) :=
      add_comm (upper + -lower - vertical) arc
    _ = arc + -(lower + -upper + vertical) := by
      exact congrArg (fun z : ℂ => arc + z) hinner
    _ = arc - (lower + -upper + vertical) :=
      (sub_eq_add_neg arc (lower + -upper + vertical)).symm
    _ = -(lower + -upper + vertical - arc) :=
      (neg_sub (lower + -upper + vertical) arc).symm

/-- Four primitive endpoint evaluations telescope around the right core. -/
theorem Complex.rightPrimitiveBoundary_telescopes
    (bottomLeft bottomRight topLeft topRight : ℂ) :
    (bottomRight - bottomLeft) + -(topRight - topLeft) +
        (topRight - bottomRight) - (topLeft - bottomLeft) = 0 := by
  have hneg :
      -(topRight - topLeft) = topLeft - topRight :=
    neg_sub topRight topLeft
  calc
    (bottomRight - bottomLeft) + -(topRight - topLeft) +
        (topRight - bottomRight) - (topLeft - bottomLeft) =
        (bottomRight - bottomLeft) + (topLeft - topRight) +
          (topRight - bottomRight) - (topLeft - bottomLeft) := by
      exact congrArg
        (fun z : ℂ =>
          (bottomRight - bottomLeft) + z +
            (topRight - bottomRight) - (topLeft - bottomLeft))
        hneg
    _ = (bottomRight - bottomLeft) + (topRight - bottomRight) +
          (topLeft - topRight) - (topLeft - bottomLeft) := by
      exact congrArg (fun z : ℂ => z - (topLeft - bottomLeft))
        (add_right_comm
          (bottomRight - bottomLeft)
          (topLeft - topRight)
          (topRight - bottomRight))
    _ = (topRight - bottomLeft) + (topLeft - topRight) -
          (topLeft - bottomLeft) := by
      exact congrArg (fun z : ℂ => z + (topLeft - topRight) -
          (topLeft - bottomLeft))
        (sub_add_sub_cancel' bottomRight bottomLeft topRight)
    _ = (topLeft - bottomLeft) - (topLeft - bottomLeft) := by
      exact congrArg (fun z : ℂ => z - (topLeft - bottomLeft))
        (sub_add_sub_cancel' topRight bottomLeft topLeft)
    _ = 0 :=
      sub_self (topLeft - bottomLeft)

/-- The half-turn carries the right core collar into the left core collar.

This is the geometry behind reducing the left indentation Cauchy theorem to
the right one. -/
theorem Complex.halfTurnAbout_mem_leftCore_of_mem_rightCore
    (c z : ℂ)
    (a ρ : ℝ)
    (ha : 0 ≤ a)
    (hρnonneg : 0 ≤ ρ)
    (hz : z ∈ Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) :
    Complex.halfTurnAbout c z ∈
      Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ := by
  rcases hz with ⟨hbox, hnot_ball⟩
  rcases hbox with ⟨hre, him⟩
  have hre_bounds :
      c.re ≤ z.re ∧ z.re ≤ c.re + a := by
    exact
      Eq.mp
        (congrArg
          (fun S : Set ℝ => z.re ∈ S)
          (Set.uIcc_of_le (Real.binet_le_add_radius c.re a ha)))
        hre
  have him_bounds :
      c.im - ρ ≤ z.im ∧ z.im ≤ c.im + ρ := by
    exact
      Eq.mp
        (congrArg
          (fun S : Set ℝ => z.im ∈ S)
          (Set.uIcc_of_le
            (Real.binet_sub_radius_le_add_radius c.im ρ hρnonneg)))
        him
  have hturn_re :
      (Complex.halfTurnAbout c z).re = 2 * c.re - z.re := by
    exact Complex.halfTurnAbout_re c z
  have hturn_im :
      (Complex.halfTurnAbout c z).im = 2 * c.im - z.im := by
    exact Complex.halfTurnAbout_im c z
  have hleft_re :
      (Complex.halfTurnAbout c z).re ∈ Set.uIcc (c.re - a) c.re := by
    have horder : c.re - a ≤ c.re :=
      Real.binet_sub_radius_le c.re a ha
    have hmem : 2 * c.re - z.re ∈ Set.Icc (c.re - a) c.re :=
      Real.mem_reflected_right_interval hre_bounds
    have hmem_uIcc :
        2 * c.re - z.re ∈ Set.uIcc (c.re - a) c.re :=
      Eq.mpr
        (congrArg
          (fun S : Set ℝ => 2 * c.re - z.re ∈ S)
          (Set.uIcc_of_le horder))
        hmem
    exact
      Eq.mp
        (congrArg
          (fun x : ℝ => x ∈ Set.uIcc (c.re - a) c.re)
          hturn_re.symm)
        hmem_uIcc
  have hleft_im :
      (Complex.halfTurnAbout c z).im ∈ Set.uIcc (c.im - ρ) (c.im + ρ) := by
    have horder : c.im - ρ ≤ c.im + ρ :=
      Real.binet_sub_radius_le_add_radius c.im ρ hρnonneg
    have hmem : 2 * c.im - z.im ∈ Set.Icc (c.im - ρ) (c.im + ρ) :=
      Real.mem_reflected_center_interval him_bounds
    have hmem_uIcc :
        2 * c.im - z.im ∈ Set.uIcc (c.im - ρ) (c.im + ρ) :=
      Eq.mpr
        (congrArg
          (fun S : Set ℝ => 2 * c.im - z.im ∈ S)
          (Set.uIcc_of_le horder))
        hmem
    exact
      Eq.mp
        (congrArg
          (fun y : ℝ => y ∈ Set.uIcc (c.im - ρ) (c.im + ρ))
          hturn_im.symm)
        hmem_uIcc
  have hnot_left :
      Complex.halfTurnAbout c z ∉ Metric.ball c ρ := by
    intro hball
    apply hnot_ball
    have hdist :
        dist z c = dist (Complex.halfTurnAbout c z) c := by
      exact Complex.dist_halfTurnAbout_center c z
    exact
      Metric.mem_ball.mpr
        (hdist.trans_lt (Metric.mem_ball.mp hball))
  exact ⟨⟨hleft_re, hleft_im⟩, hnot_left⟩

/-- Pulling back by the half-turn transports continuity from the left core
collar to the right core collar. -/
theorem Complex.continuousOn_halfTurnPullback_rightCore_of_leftCore
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ)
    (ha : 0 ≤ a)
    (hρnonneg : 0 ≤ ρ)
    (hcont :
      ContinuousOn f
        (Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ)) :
    ContinuousOn (Complex.halfTurnPullback c f)
      (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
  have hmap :
      Set.MapsTo (Complex.halfTurnAbout c)
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ)
        (Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ) := by
    intro z hz
    exact
      Complex.halfTurnAbout_mem_leftCore_of_mem_rightCore c z a ρ ha hρnonneg hz
  have hturn_cont :
      ContinuousOn (Complex.halfTurnAbout c)
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
    unfold Complex.halfTurnAbout
    exact (continuous_const.sub continuous_id).continuousOn
  change
    ContinuousOn (fun z : ℂ => f (Complex.halfTurnAbout c z))
      (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ)
  exact
    ContinuousOn.comp' hcont hturn_cont hmap

/-- Pulling back by the half-turn transports holomorphy from the left core
collar to the right core collar. -/
theorem Complex.differentiableOn_halfTurnPullback_rightCore_of_leftCore
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ)
    (ha : 0 ≤ a)
    (hρnonneg : 0 ≤ ρ)
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ)) :
    DifferentiableOn ℂ (Complex.halfTurnPullback c f)
      (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
  intro z hz
  have hmem :
      Complex.halfTurnAbout c z ∈
        Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ :=
    Complex.halfTurnAbout_mem_leftCore_of_mem_rightCore c z a ρ ha hρnonneg hz
  have hturn :
      DifferentiableAt ℂ (Complex.halfTurnAbout c) z := by
    unfold Complex.halfTurnAbout
    exact ((differentiableAt_const (2 * c)).sub differentiableAt_id)
  have hmap :
      Set.MapsTo (Complex.halfTurnAbout c)
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ)
        (Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ) := by
    intro w hw
    exact
      Complex.halfTurnAbout_mem_leftCore_of_mem_rightCore c w a ρ
        ha hρnonneg hw
  change
    DifferentiableWithinAt ℂ (fun z : ℂ => f (Complex.halfTurnAbout c z))
      (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) z
  exact
    (hdiff (Complex.halfTurnAbout c z) hmem).comp z
      hturn.differentiableWithinAt hmap

/-- The lower horizontal side of the left core collar is the upper horizontal
side of the right core collar after half-turn pullback. -/
theorem Complex.leftHalfRectangleDeletedDiskCore_lower_eq_halfTurn_right_upper
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ) :
    (∫ x : ℝ in (c.re - a)..c.re,
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) =
      ∫ x : ℝ in c.re..(c.re + a),
        (Complex.halfTurnPullback c f)
          (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) := by
  let F : ℝ → ℂ := fun x : ℝ =>
    f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))
  have hsubst :
      (∫ x : ℝ in c.re..(c.re + a), F (2 * c.re - x)) =
        ∫ x : ℝ in (2 * c.re - (c.re + a))..(2 * c.re - c.re), F x := by
    exact
      intervalIntegral.integral_comp_sub_left
        (f := F) (a := c.re) (b := c.re + a) (d := 2 * c.re)
  have hpoint :
      (fun x : ℝ =>
        (Complex.halfTurnPullback c f)
          (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) =
        fun x : ℝ => F (2 * c.re - x) := by
    funext x
    unfold F
    unfold Complex.halfTurnPullback
    exact congrArg f (Complex.halfTurnAbout_right_upper_point c ρ x)
  have hleft :
      2 * c.re - (c.re + a) = c.re - a :=
    Real.two_mul_sub_add_self c.re a
  have hright :
      2 * c.re - c.re = c.re :=
    Real.two_mul_sub_self c.re
  have hbounds :
      (∫ x : ℝ in (2 * c.re - (c.re + a))..(2 * c.re - c.re), F x) =
        ∫ x : ℝ in (c.re - a)..c.re, F x :=
    congrArg₂
      (fun u v : ℝ => ∫ x : ℝ in u..v, F x)
      hleft hright
  exact hpoint ▸ (Eq.trans hsubst hbounds).symm

/-- The upper horizontal side of the left core collar is the lower horizontal
side of the right core collar after half-turn pullback. -/
theorem Complex.leftHalfRectangleDeletedDiskCore_upper_eq_halfTurn_right_lower
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ) :
    (∫ x : ℝ in (c.re - a)..c.re,
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) =
      ∫ x : ℝ in c.re..(c.re + a),
        (Complex.halfTurnPullback c f)
          (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
  let F : ℝ → ℂ := fun x : ℝ =>
    f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))
  have hsubst :
      (∫ x : ℝ in c.re..(c.re + a), F (2 * c.re - x)) =
        ∫ x : ℝ in (2 * c.re - (c.re + a))..(2 * c.re - c.re), F x := by
    exact
      intervalIntegral.integral_comp_sub_left
        (f := F) (a := c.re) (b := c.re + a) (d := 2 * c.re)
  have hpoint :
      (fun x : ℝ =>
        (Complex.halfTurnPullback c f)
          (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) =
        fun x : ℝ => F (2 * c.re - x) := by
    funext x
    unfold F
    unfold Complex.halfTurnPullback
    exact congrArg f (Complex.halfTurnAbout_right_lower_point c ρ x)
  have hleft :
      2 * c.re - (c.re + a) = c.re - a :=
    Real.two_mul_sub_add_self c.re a
  have hright :
      2 * c.re - c.re = c.re :=
    Real.two_mul_sub_self c.re
  have hbounds :
      (∫ x : ℝ in (2 * c.re - (c.re + a))..(2 * c.re - c.re), F x) =
        ∫ x : ℝ in (c.re - a)..c.re, F x :=
    congrArg₂
      (fun u v : ℝ => ∫ x : ℝ in u..v, F x)
      hleft hright
  exact hpoint ▸ (Eq.trans hsubst hbounds).symm

/-- The safe vertical side of the left core collar is the safe vertical side of
the right core collar after half-turn pullback. -/
theorem Complex.leftHalfRectangleDeletedDiskCore_vertical_eq_halfTurn_right_vertical
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ) :
    (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
      f (((c.re - a : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
      ∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
        (Complex.halfTurnPullback c f)
          (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) := by
  let F : ℝ → ℂ := fun y : ℝ =>
    f (((c.re - a : ℝ) : ℂ) + Complex.I * (y : ℂ))
  have hsubst :
      (∫ y : ℝ in (c.im - ρ)..(c.im + ρ), F (2 * c.im - y)) =
        ∫ y : ℝ in (2 * c.im - (c.im + ρ))..(2 * c.im - (c.im - ρ)), F y := by
    exact
      intervalIntegral.integral_comp_sub_left
        (f := F) (a := c.im - ρ) (b := c.im + ρ) (d := 2 * c.im)
  have hpoint :
      (fun y : ℝ =>
        (Complex.halfTurnPullback c f)
          (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        fun y : ℝ => F (2 * c.im - y) := by
    funext y
    unfold F
    unfold Complex.halfTurnPullback
    exact congrArg f (Complex.halfTurnAbout_right_vertical_point c a y)
  have hleft :
      2 * c.im - (c.im + ρ) = c.im - ρ :=
    Real.two_mul_sub_add_self c.im ρ
  have hright :
      2 * c.im - (c.im - ρ) = c.im + ρ :=
    Real.two_mul_sub_sub_self c.im ρ
  have hbounds :
      (∫ y : ℝ in (2 * c.im - (c.im + ρ))..
          (2 * c.im - (c.im - ρ)), F y) =
        ∫ y : ℝ in (c.im - ρ)..(c.im + ρ), F y :=
    congrArg₂
      (fun u v : ℝ => ∫ y : ℝ in u..v, F y)
      hleft hright
  exact hpoint ▸ (Eq.trans hsubst hbounds).symm

/-- The left semicircle is the negative of the right semicircle after half-turn
pullback.

The minus sign is the tangent-vector contribution of the half-turn. -/
theorem Complex.leftHalfRectangleDeletedDiskCore_semicircle_eq_neg_halfTurn_right_semicircle
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) :
    (∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
      f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      -∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        (Complex.halfTurnPullback c f)
          (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  let G : ℝ → ℂ := fun θ : ℝ =>
    f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  let H : ℝ → ℂ := fun θ : ℝ =>
    (Complex.halfTurnPullback c f)
      (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  have hpoint : ∀ θ : ℝ, H θ = -G (θ + Real.pi) := by
    intro θ
    have hexp :
        Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ))) =
          -Complex.exp (Complex.I * (θ : ℂ)) := by
      exact Complex.exp_I_mul_ofReal_add_pi θ
    have htangent :
        Complex.I * (ρ : ℂ) *
            Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ))) =
          -(Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ))) := by
      calc
        Complex.I * (ρ : ℂ) *
            Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ))) =
            Complex.I * (ρ : ℂ) *
              (-Complex.exp (Complex.I * (θ : ℂ))) := by
          exact congrArg
            (fun z : ℂ => Complex.I * (ρ : ℂ) * z)
            hexp
        _ = -(Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ))) := by
          exact mul_neg (Complex.I * (ρ : ℂ))
            (Complex.exp (Complex.I * (θ : ℂ)))
    have hturn :
        Complex.halfTurnAbout c
            (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
          c + (ρ : ℂ) *
            Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ))) := by
      exact Complex.halfTurnAbout_circlePoint_eq_add_pi c ρ θ
    unfold H
    unfold G
    unfold Complex.halfTurnPullback
    calc
      f (Complex.halfTurnAbout c
            (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
          f (c + (ρ : ℂ) *
              Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ)))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
        exact congrArg
          (fun z : ℂ =>
            f z *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          hturn
      _ =
          -(f (c + (ρ : ℂ) *
              Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ)))) *
            (-(Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ))))) :=
        Complex.mul_eq_neg_mul_neg_right
          (f (c + (ρ : ℂ) *
            Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ)))))
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
      _ =
          -(f (c + (ρ : ℂ) *
              Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ)))) *
            (Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ))))) := by
        exact congrArg Neg.neg
          (congrArg
            (fun z : ℂ =>
              f (c + (ρ : ℂ) *
                Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ)))) * z)
            htangent.symm)
  have hsubst :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), G (θ + Real.pi)) =
        ∫ θ : ℝ in (-(Real.pi / 2) + Real.pi)..(Real.pi / 2 + Real.pi), G θ := by
    exact
      intervalIntegral.integral_comp_add_right
        (f := G) (a := -(Real.pi / 2)) (b := Real.pi / 2) Real.pi
  have hH :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), H θ) =
        -∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2), G θ := by
    calc
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), H θ) =
          ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), -G (θ + Real.pi) := by
        apply intervalIntegral.integral_congr
        intro θ _hθ
        exact hpoint θ
      _ = -∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), G (θ + Real.pi) := by
        exact intervalIntegral.integral_neg
      _ = -∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2), G θ := by
        have hleft :
            -(Real.pi / 2) + Real.pi = Real.pi / 2 :=
          Real.neg_pi_div_two_add_pi_eq_pi_div_two
        have hright :
            Real.pi / 2 + Real.pi = 3 * Real.pi / 2 :=
          Real.pi_div_two_add_pi_eq_three_pi_div_two
        have hbounds :
            (∫ θ : ℝ in (-(Real.pi / 2) + Real.pi)..
                (Real.pi / 2 + Real.pi), G θ) =
              ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2), G θ := by
          exact
            congrArg₂
              (fun u v : ℝ => ∫ θ : ℝ in u..v, G θ)
              hleft hright
        exact congrArg Neg.neg (hsubst.trans hbounds)
  unfold G at hH
  unfold H at hH
  exact Complex.eq_neg_of_eq_neg hH

/-- The left core boundary integral is the negative of the right core boundary
integral after pullback by the half-turn.

This is pure boundary reparametrization: the half-turn swaps lower and upper
chords, carries the safe left vertical chord to the safe right vertical chord,
and sends the left semicircle to the right semicircle with the corrected
closed-contour orientation.  The global minus records the orientation reversal
of the half-turn on the boundary chain. -/
theorem Complex.leftHalfRectangleDeletedDiskCoreBoundaryIntegral_eq_neg_halfTurn_right
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ) :
    Complex.leftHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ =
      -Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral
        (Complex.halfTurnPullback c f) c a ρ := by
  have hlower :
      (∫ x : ℝ in (c.re - a)..c.re,
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) =
        ∫ x : ℝ in c.re..(c.re + a),
          (Complex.halfTurnPullback c f)
            (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) :=
    Complex.leftHalfRectangleDeletedDiskCore_lower_eq_halfTurn_right_upper
      f c a ρ
  have hupper :
      (∫ x : ℝ in (c.re - a)..c.re,
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) =
        ∫ x : ℝ in c.re..(c.re + a),
          (Complex.halfTurnPullback c f)
            (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) :=
    Complex.leftHalfRectangleDeletedDiskCore_upper_eq_halfTurn_right_lower
      f c a ρ
  have hvertical :
      (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
        f (((c.re - a : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        ∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
          (Complex.halfTurnPullback c f)
            (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) :=
    Complex.leftHalfRectangleDeletedDiskCore_vertical_eq_halfTurn_right_vertical
      f c a ρ
  have harc :
      (∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        -∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          (Complex.halfTurnPullback c f)
            (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
    Complex.leftHalfRectangleDeletedDiskCore_semicircle_eq_neg_halfTurn_right_semicircle
      f c ρ
  unfold Complex.leftHalfRectangleDeletedDiskCoreBoundaryIntegral
  unfold Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral
  exact hlower ▸ hupper ▸ hvertical ▸ harc ▸
    Complex.leftRightCoreBoundary_neg_algebra _ _ _ _

/-- Boundary telescoping for the right deleted half-rectangle from primitive
evaluations on its four oriented pieces. -/
theorem Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral_eq_zero_of_primitive_evaluations
    (f F : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ)
    (hbottom :
      (∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) =
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) -
          F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
    (htop :
      (∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) =
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
          F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
    (hvertical :
      Complex.I *
        (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
          f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
          F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
    (harc :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
          F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) :
    Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ = 0 := by
  unfold Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral
  exact hbottom ▸ htop ▸ hvertical ▸ harc ▸
    Complex.rightPrimitiveBoundary_telescopes _ _ _ _

/-- Primitive derivative data along the four right-indentation boundary pieces
gives the four primitive endpoint evaluations by the real fundamental theorem
of calculus. -/
theorem Complex.rightHalfRectangleDeletedDiskCore_primitive_evaluations_of_hasDerivAt
    (f F : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ)
    (hbottom_deriv :
      ∀ x ∈ Set.uIcc c.re (c.re + a),
        HasDerivAt
          (fun x : ℝ =>
            F (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
          (f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
          x)
    (hbottom_int :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        volume c.re (c.re + a))
    (htop_deriv :
      ∀ x ∈ Set.uIcc c.re (c.re + a),
        HasDerivAt
          (fun x : ℝ =>
            F (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
          (f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
          x)
    (htop_int :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        volume c.re (c.re + a))
    (hvertical_deriv :
      ∀ y ∈ Set.uIcc (c.im - ρ) (c.im + ρ),
        HasDerivAt
          (fun y : ℝ =>
            F (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)))
          (Complex.I *
            f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)))
          y)
    (hvertical_int :
      IntervalIntegrable
        (fun y : ℝ =>
          Complex.I *
            f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        volume (c.im - ρ) (c.im + ρ))
    (harc_deriv :
      ∀ θ ∈ Set.uIcc (-(Real.pi / 2)) (Real.pi / 2),
        HasDerivAt
          (fun θ : ℝ =>
            F (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          (f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ))))
          θ)
    (harc_int :
      IntervalIntegrable
        (fun θ : ℝ =>
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ))))
        volume (-(Real.pi / 2)) (Real.pi / 2)) :
    (∫ x : ℝ in c.re..(c.re + a),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) =
      F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) -
        F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) ∧
    (∫ x : ℝ in c.re..(c.re + a),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) =
      F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
        F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) ∧
    Complex.I *
      (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
        f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
      F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) ∧
    (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
      f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
        F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
  have hbottom_eval :
      (∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) =
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) -
          F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      hbottom_deriv hbottom_int
  have htop_eval :
      (∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) =
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
          F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      htop_deriv htop_int
  have hvertical_eval_integrand :
      (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
        Complex.I *
          f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
          F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      hvertical_deriv hvertical_int
  have hvertical_eval :
      Complex.I *
        (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
          f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
          F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
    exact
      Eq.trans
        (intervalIntegral.integral_const_mul
          Complex.I
          (fun y : ℝ =>
            f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)))).symm
        hvertical_eval_integrand
  have harc_eval :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        F (c + (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ))) -
          F (c + (ρ : ℂ) * Complex.exp (Complex.I * (((-(Real.pi / 2)) : ℝ) : ℂ))) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      harc_deriv harc_int
  have htop_point :
      c + (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) =
        (((c.re : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) := by
    exact Complex.rightSemicircle_upper_endpoint c ρ
  have hbottom_point :
      c + (ρ : ℂ) * Complex.exp (Complex.I * (((-(Real.pi / 2)) : ℝ) : ℂ)) =
        (((c.re : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
    exact Complex.rightSemicircle_lower_endpoint c ρ
  have harc_eval_named :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
          F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
          F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
    exact htop_point ▸ hbottom_point ▸ harc_eval
  exact ⟨hbottom_eval, htop_eval, hvertical_eval, harc_eval_named⟩

/-- Algebraic boundary bookkeeping for splitting the right core into its
tangent-width semicircular core plus rectangular tail. -/
theorem Complex.rightCoreBoundary_split_algebra
    (bottomCore bottomTail topCore topTail verticalSafe verticalTangent arc : ℂ) :
    (bottomCore + bottomTail) + -(topCore + topTail) + verticalSafe - arc =
      (((bottomCore + -topCore) + verticalTangent) - arc) +
        (((bottomTail - topTail) + verticalSafe) - verticalTangent) := by
  have hneg :
      -(topCore + topTail) = -topCore + -topTail :=
    neg_add topCore topTail
  have hfirst :
      (bottomCore + bottomTail) + -(topCore + topTail) + verticalSafe - arc =
        (bottomCore + -topCore) + ((bottomTail + -topTail) + verticalSafe) -
          arc := by
    calc
      (bottomCore + bottomTail) + -(topCore + topTail) + verticalSafe - arc =
          (bottomCore + bottomTail) + (-topCore + -topTail) +
            verticalSafe - arc := by
        exact congrArg
          (fun z : ℂ => (bottomCore + bottomTail) + z + verticalSafe - arc)
          hneg
      _ = (bottomCore + -topCore) + (bottomTail + -topTail) +
            verticalSafe - arc := by
        exact congrArg (fun z : ℂ => z + verticalSafe - arc)
          (add_add_add_comm bottomCore bottomTail (-topCore) (-topTail))
      _ = (bottomCore + -topCore) +
            ((bottomTail + -topTail) + verticalSafe) - arc := by
        exact congrArg (fun z : ℂ => z - arc)
          (add_assoc (bottomCore + -topCore) (bottomTail + -topTail) verticalSafe)
  have htail :
      (bottomTail + -topTail) + verticalSafe =
        (bottomTail - topTail) + verticalSafe := by
    exact congrArg (fun z : ℂ => z + verticalSafe)
      (sub_eq_add_neg bottomTail topTail).symm
  have hsplit :
      (bottomCore + -topCore) + ((bottomTail - topTail) + verticalSafe) -
          arc =
        (((bottomCore + -topCore) + verticalTangent) - arc) +
          (((bottomTail - topTail) + verticalSafe) - verticalTangent) :=
    Complex.add_canceling_split
      (bottomCore + -topCore)
      ((bottomTail - topTail) + verticalSafe)
      verticalTangent
      arc
  exact Eq.trans hfirst (Eq.trans
    (congrArg
      (fun z : ℂ => (bottomCore + -topCore) + z - arc)
      htail)
    hsplit)

/-- Algebraic boundary bookkeeping for splitting the tangent-box cap into lower
and upper quarter-caps. -/
theorem Complex.rightTangentBoxCap_split_algebra
    (bottom top verticalLower verticalUpper arcLower arcUpper : ℂ) :
    bottom + -top + Complex.I * (verticalLower + verticalUpper) -
        (arcLower + arcUpper) =
      ((bottom + Complex.I * verticalLower) - arcLower) +
        (((-top) + Complex.I * verticalUpper) - arcUpper) := by
  calc
    bottom + -top + Complex.I * (verticalLower + verticalUpper) -
        (arcLower + arcUpper) =
        bottom + -top +
          (Complex.I * verticalLower + Complex.I * verticalUpper) -
          (arcLower + arcUpper) := by
      exact congrArg
        (fun z : ℂ => bottom + -top + z - (arcLower + arcUpper))
        (mul_add Complex.I verticalLower verticalUpper)
    _ =
        (bottom + Complex.I * verticalLower + ((-top) + Complex.I * verticalUpper)) -
          (arcLower + arcUpper) := by
      exact congrArg
        (fun z : ℂ => z - (arcLower + arcUpper))
        (add_add_add_comm
          bottom (-top)
          (Complex.I * verticalLower) (Complex.I * verticalUpper))
    _ =
        (bottom + Complex.I * verticalLower + ((-top) + Complex.I * verticalUpper)) -
          arcLower - arcUpper :=
      sub_add_eq_sub_sub
        (bottom + Complex.I * verticalLower + ((-top) + Complex.I * verticalUpper))
        arcLower arcUpper
    _ =
        ((bottom + Complex.I * verticalLower) - arcLower) +
          (((-top) + Complex.I * verticalUpper) - arcUpper) :=
      Complex.add_sub_sub_eq_sub_add_sub
        (bottom + Complex.I * verticalLower)
        ((-top) + Complex.I * verticalUpper)
        arcLower arcUpper

/-- Rectangle/annulus exhaustion for the right deleted half-rectangle collar.

This is the true local topological input.  The curvilinear half-collar is
obtained as a finite rectangle/annular exhaustion; Cauchy-Goursat kills the
piece boundaries and the internal straight/circular edges cancel, leaving
exactly the named outer boundary integral. -/
theorem Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_semicircularCore_add_rectangularTail
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ)
    (_hρa : ρ ≤ a)
    (hbottom₁ :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        volume c.re (c.re + ρ))
    (hbottom₂ :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        volume (c.re + ρ) (c.re + a))
    (htop₁ :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        volume c.re (c.re + ρ))
    (htop₂ :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        volume (c.re + ρ) (c.re + a)) :
    Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ =
      Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundaryIntegral f c ρ +
        Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral f c a ρ := by
  have hbottom_split :
      (∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) =
        (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
          ∫ x : ℝ in (c.re + ρ)..(c.re + a),
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
    exact (intervalIntegral.integral_add_adjacent_intervals hbottom₁ hbottom₂).symm
  have htop_split :
      (∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) =
        (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
          ∫ x : ℝ in (c.re + ρ)..(c.re + a),
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) := by
    exact (intervalIntegral.integral_add_adjacent_intervals htop₁ htop₂).symm
  unfold Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral
  unfold Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundaryIntegral
  unfold Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral
  exact hbottom_split ▸ htop_split ▸ by
    exact
      Complex.rightCoreBoundary_split_algebra
        (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        (∫ x : ℝ in (c.re + ρ)..(c.re + a),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        (∫ x : ℝ in (c.re + ρ)..(c.re + a),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        (Complex.I *
          ∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
            f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        (Complex.I *
          ∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
            f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))

/-- The full right tangent-box cap boundary is the sum of its lower and upper
quarter-cap boundaries.

This is only interval splitting and orientation bookkeeping.  The Cauchy
theorem for the two quarter-caps is proved separately. -/
theorem Complex.rightDeletedDiskTangentBoxCapBoundary_eq_lower_add_upper
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (hvertical_lower :
      IntervalIntegrable
        (fun y : ℝ =>
          f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        volume (c.im - ρ) c.im)
    (hvertical_upper :
      IntervalIntegrable
        (fun y : ℝ =>
          f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        volume c.im (c.im + ρ))
    (harc_lower :
      IntervalIntegrable
        (fun θ : ℝ =>
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ))))
        volume (-(Real.pi / 2)) 0)
    (harc_upper :
      IntervalIntegrable
        (fun θ : ℝ =>
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ))))
        volume 0 (Real.pi / 2)) :
    Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c ρ ρ =
      Complex.rightDeletedDiskLowerTangentBoxCapBoundaryIntegral f c ρ +
        Complex.rightDeletedDiskUpperTangentBoxCapBoundaryIntegral f c ρ := by
  have hvertical_split :
      (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        (∫ y : ℝ in (c.im - ρ)..c.im,
          f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) +
          ∫ y : ℝ in c.im..(c.im + ρ),
            f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)) := by
    exact
      (intervalIntegral.integral_add_adjacent_intervals
        hvertical_lower hvertical_upper).symm
  have harc_split :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) *
            Complex.exp (Complex.I * (θ : ℂ)))) =
        (∫ θ : ℝ in (-(Real.pi / 2))..0,
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ)))) +
          ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2),
            f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) *
                Complex.exp (Complex.I * (θ : ℂ))) := by
    exact
      (intervalIntegral.integral_add_adjacent_intervals
        harc_lower harc_upper).symm
  unfold Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral
  unfold Complex.rightDeletedDiskLowerTangentBoxCapBoundaryIntegral
  unfold Complex.rightDeletedDiskUpperTangentBoxCapBoundaryIntegral
  exact hvertical_split ▸ harc_split ▸ by
    exact
      Complex.rightTangentBoxCap_split_algebra
        (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        (∫ y : ℝ in (c.im - ρ)..c.im,
          f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        (∫ y : ℝ in c.im..(c.im + ρ),
          f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        (∫ θ : ℝ in (-(Real.pi / 2))..0,
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))

/-- The lower quarter tangent-box cap is contained in the full tangent-box
core. -/
theorem Complex.rightDeletedDiskLowerTangentBoxCapDomain_subset_core
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    Complex.rightDeletedDiskLowerTangentBoxCapDomain c ρ ⊆
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  intro z hz
  rcases hz with ⟨hbox, hnot_ball⟩
  rcases hbox with ⟨hre, him⟩
  have hre_core : z.re ∈ Set.uIcc c.re (c.re + ρ) := hre
  have him_lower_bounds :
      c.im - ρ ≤ z.im ∧ z.im ≤ c.im := by
    exact
      Real.bounds_of_mem_uIcc
        (Real.binet_sub_radius_le c.im ρ hρ.le)
        him
  have him_core : z.im ∈ Set.uIcc (c.im - ρ) (c.im + ρ) := by
    have hleft : c.im - ρ ≤ z.im := him_lower_bounds.1
    have hright : z.im ≤ c.im + ρ :=
      him_lower_bounds.2.trans (Real.binet_le_add_radius c.im ρ hρ.le)
    exact
      Real.mem_uIcc_of_bounds
        (Real.binet_sub_radius_le_add_radius c.im ρ hρ.le)
        (And.intro hleft hright)
  exact ⟨⟨hre_core, him_core⟩, hnot_ball⟩

/-- The upper quarter tangent-box cap is contained in the full tangent-box
core. -/
theorem Complex.rightDeletedDiskUpperTangentBoxCapDomain_subset_core
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    Complex.rightDeletedDiskUpperTangentBoxCapDomain c ρ ⊆
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  intro z hz
  rcases hz with ⟨hbox, hnot_ball⟩
  rcases hbox with ⟨hre, him⟩
  have hre_core : z.re ∈ Set.uIcc c.re (c.re + ρ) := hre
  have him_upper_bounds :
      c.im ≤ z.im ∧ z.im ≤ c.im + ρ := by
    exact
      Real.bounds_of_mem_uIcc
        (Real.binet_le_add_radius c.im ρ hρ.le)
        him
  have him_core : z.im ∈ Set.uIcc (c.im - ρ) (c.im + ρ) := by
    have hleft : c.im - ρ ≤ z.im :=
      (Real.binet_sub_radius_le c.im ρ hρ.le).trans him_upper_bounds.1
    have hright : z.im ≤ c.im + ρ := him_upper_bounds.2
    exact
      Real.mem_uIcc_of_bounds
        (Real.binet_sub_radius_le_add_radius c.im ρ hρ.le)
        (And.intro hleft hright)
  exact ⟨⟨hre_core, him_core⟩, hnot_ball⟩

/-- The lower tangent-box cap is equivalently the lower graph region to the
right of the circular boundary. -/
theorem Complex.rightDeletedDiskLowerTangentBoxCapDomain_eq_graphDomain
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    Complex.rightDeletedDiskLowerTangentBoxCapDomain c ρ =
      Complex.rightDeletedDiskLowerTangentBoxGraphDomain c ρ := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hbox, hnot_ball⟩
    rcases hbox with ⟨hre, him⟩
    have hre_bounds : c.re ≤ z.re ∧ z.re ≤ c.re + ρ := by
      exact
        Real.bounds_of_mem_uIcc
          (Real.binet_le_add_radius c.re ρ hρ.le)
          hre
    have him_bounds : c.im - ρ ≤ z.im ∧ z.im ≤ c.im := by
      exact
        Real.bounds_of_mem_uIcc
          (Real.binet_sub_radius_le c.im ρ hρ.le)
          him
    have hx : z.re - c.re ∈ Set.uIcc 0 ρ := by
      have hleft : 0 ≤ z.re - c.re :=
        Real.binet_nonneg_sub_of_le hre_bounds.1
      have hright : z.re - c.re ≤ ρ :=
        Real.binet_sub_le_radius_of_le_add hre_bounds.2
      exact Real.mem_uIcc_of_bounds hρ.le (And.intro hleft hright)
    have hy : z.im - c.im ∈ Set.uIcc (-ρ) 0 := by
      have hleft : -ρ ≤ z.im - c.im :=
        Real.binet_neg_radius_le_sub_of_sub_le him_bounds.1
      have hright : z.im - c.im ≤ 0 :=
        Real.binet_sub_nonpos_of_le him_bounds.2
      exact
        Real.mem_uIcc_of_bounds
          (Real.binet_neg_radius_le_zero hρ.le)
          (And.intro hleft hright)
    have hdist_ge : ρ ≤ dist z c := by
      exact le_of_not_gt (fun hlt => hnot_ball (Metric.mem_ball.mpr hlt))
    have hcircle :
        ρ ≤ Real.sqrt ((z.re - c.re) ^ 2 + (z.im - c.im) ^ 2) := by
      exact
        Eq.mp
          (congrArg
            (fun r : ℝ => ρ ≤ r)
            (Complex.dist_eq_re_im z c))
          hdist_ge
    have hgraph_shift :
        Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) ≤ z.re - c.re :=
      (Real.lowerTangentBox_outside_circle_iff_graph_right hρ hx hy).mp hcircle
    have him_graph : z.im ∈ Set.uIcc (c.im - ρ) c.im := him
    have hre_graph : z.re ∈
        Set.uIcc
          (Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im)
          (c.re + ρ) := by
      have hleft :
          Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im ≤ z.re := by
        exact
          Complex.rightDeletedDiskTangentBoxCircleGraphRe_le_of_shift
            hgraph_shift
      have hright : z.re ≤ c.re + ρ := hre_bounds.2
      exact
        Real.mem_uIcc_of_bounds
          (Complex.rightDeletedDiskTangentBoxCircleGraphRe_le_right_edge c hρ.le)
          (And.intro hleft hright)
    exact ⟨him_graph, hre_graph⟩
  · intro hz
    rcases hz with ⟨him, hre_graph⟩
    have him_bounds : c.im - ρ ≤ z.im ∧ z.im ≤ c.im := by
      exact
        Real.bounds_of_mem_uIcc
          (Real.binet_sub_radius_le c.im ρ hρ.le)
          him
    have hre_graph_bounds :
        Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im ≤ z.re ∧
          z.re ≤ c.re + ρ := by
      exact
        Real.bounds_of_mem_uIcc
          (Complex.rightDeletedDiskTangentBoxCircleGraphRe_le_right_edge c hρ.le)
          hre_graph
    have hre_bounds : c.re ≤ z.re ∧ z.re ≤ c.re + ρ := by
      have hleft : c.re ≤ z.re := by
        exact Complex.center_re_le_of_graphRe_le hre_graph_bounds.1
      exact ⟨hleft, hre_graph_bounds.2⟩
    have hx : z.re - c.re ∈ Set.uIcc 0 ρ := by
      have hleft : 0 ≤ z.re - c.re :=
        Real.binet_nonneg_sub_of_le hre_bounds.1
      have hright : z.re - c.re ≤ ρ :=
        Real.binet_sub_le_radius_of_le_add hre_bounds.2
      exact Real.mem_uIcc_of_bounds hρ.le (And.intro hleft hright)
    have hy : z.im - c.im ∈ Set.uIcc (-ρ) 0 := by
      have hleft : -ρ ≤ z.im - c.im :=
        Real.binet_neg_radius_le_sub_of_sub_le him_bounds.1
      have hright : z.im - c.im ≤ 0 :=
        Real.binet_sub_nonpos_of_le him_bounds.2
      exact
        Real.mem_uIcc_of_bounds
          (Real.binet_neg_radius_le_zero hρ.le)
          (And.intro hleft hright)
    have hgraph_shift :
        Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) ≤ z.re - c.re := by
      exact
        Complex.rightDeletedDiskTangentBox_shift_le_of_graphRe_le
          hre_graph_bounds.1
    have hcircle :
        ρ ≤ Real.sqrt ((z.re - c.re) ^ 2 + (z.im - c.im) ^ 2) :=
      (Real.lowerTangentBox_outside_circle_iff_graph_right hρ hx hy).mpr
        hgraph_shift
    have hnot_ball : z ∉ Metric.ball c ρ := by
      intro hball
      have hdist_lt : dist z c < ρ := by
        exact Metric.mem_ball.mp hball
      have hdist_ge : ρ ≤ dist z c := by
        exact
          Eq.mpr
            (congrArg
              (fun r : ℝ => ρ ≤ r)
              (Complex.dist_eq_re_im z c))
            hcircle
      exact not_lt_of_ge hdist_ge hdist_lt
    have hre_box : z.re ∈ Set.uIcc c.re (c.re + ρ) := by
      exact
        Real.mem_uIcc_of_bounds
          (Real.binet_le_add_radius c.re ρ hρ.le)
          hre_bounds
    exact ⟨⟨hre_box, him⟩, hnot_ball⟩

/-- The upper tangent-box cap is equivalently the upper graph region to the
right of the circular boundary. -/
theorem Complex.rightDeletedDiskUpperTangentBoxCapDomain_eq_graphDomain
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    Complex.rightDeletedDiskUpperTangentBoxCapDomain c ρ =
      Complex.rightDeletedDiskUpperTangentBoxGraphDomain c ρ := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hbox, hnot_ball⟩
    rcases hbox with ⟨hre, him⟩
    have hre_bounds : c.re ≤ z.re ∧ z.re ≤ c.re + ρ := by
      exact
        Real.bounds_of_mem_uIcc
          (Real.binet_le_add_radius c.re ρ hρ.le)
          hre
    have him_bounds : c.im ≤ z.im ∧ z.im ≤ c.im + ρ := by
      exact
        Real.bounds_of_mem_uIcc
          (Real.binet_le_add_radius c.im ρ hρ.le)
          him
    have hx : z.re - c.re ∈ Set.uIcc 0 ρ := by
      have hleft : 0 ≤ z.re - c.re :=
        Real.binet_nonneg_sub_of_le hre_bounds.1
      have hright : z.re - c.re ≤ ρ :=
        Real.binet_sub_le_radius_of_le_add hre_bounds.2
      exact Real.mem_uIcc_of_bounds hρ.le (And.intro hleft hright)
    have hy : z.im - c.im ∈ Set.uIcc 0 ρ := by
      have hleft : 0 ≤ z.im - c.im :=
        Real.binet_nonneg_sub_of_le him_bounds.1
      have hright : z.im - c.im ≤ ρ :=
        Real.binet_sub_le_radius_of_le_add him_bounds.2
      exact Real.mem_uIcc_of_bounds hρ.le (And.intro hleft hright)
    have hdist_ge : ρ ≤ dist z c := by
      exact le_of_not_gt (fun hlt => hnot_ball (Metric.mem_ball.mpr hlt))
    have hcircle :
        ρ ≤ Real.sqrt ((z.re - c.re) ^ 2 + (z.im - c.im) ^ 2) := by
      exact
        Eq.mp
          (congrArg
            (fun r : ℝ => ρ ≤ r)
            (Complex.dist_eq_re_im z c))
          hdist_ge
    have hgraph_shift :
        Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) ≤ z.re - c.re :=
      (Real.upperTangentBox_outside_circle_iff_graph_right hρ hx hy).mp hcircle
    have him_graph : z.im ∈ Set.uIcc c.im (c.im + ρ) := him
    have hre_graph : z.re ∈
        Set.uIcc
          (Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im)
          (c.re + ρ) := by
      have hleft :
          Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im ≤ z.re := by
        exact
          Complex.rightDeletedDiskTangentBoxCircleGraphRe_le_of_shift
            hgraph_shift
      have hright : z.re ≤ c.re + ρ := hre_bounds.2
      exact
        Real.mem_uIcc_of_bounds
          (Complex.rightDeletedDiskTangentBoxCircleGraphRe_le_right_edge c hρ.le)
          (And.intro hleft hright)
    exact ⟨him_graph, hre_graph⟩
  · intro hz
    rcases hz with ⟨him, hre_graph⟩
    have him_bounds : c.im ≤ z.im ∧ z.im ≤ c.im + ρ := by
      exact
        Real.bounds_of_mem_uIcc
          (Real.binet_le_add_radius c.im ρ hρ.le)
          him
    have hre_graph_bounds :
        Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im ≤ z.re ∧
          z.re ≤ c.re + ρ := by
      exact
        Real.bounds_of_mem_uIcc
          (Complex.rightDeletedDiskTangentBoxCircleGraphRe_le_right_edge c hρ.le)
          hre_graph
    have hre_bounds : c.re ≤ z.re ∧ z.re ≤ c.re + ρ := by
      have hleft : c.re ≤ z.re := by
        exact Complex.center_re_le_of_graphRe_le hre_graph_bounds.1
      exact ⟨hleft, hre_graph_bounds.2⟩
    have hx : z.re - c.re ∈ Set.uIcc 0 ρ := by
      have hleft : 0 ≤ z.re - c.re :=
        Real.binet_nonneg_sub_of_le hre_bounds.1
      have hright : z.re - c.re ≤ ρ :=
        Real.binet_sub_le_radius_of_le_add hre_bounds.2
      exact Real.mem_uIcc_of_bounds hρ.le (And.intro hleft hright)
    have hy : z.im - c.im ∈ Set.uIcc 0 ρ := by
      have hleft : 0 ≤ z.im - c.im :=
        Real.binet_nonneg_sub_of_le him_bounds.1
      have hright : z.im - c.im ≤ ρ :=
        Real.binet_sub_le_radius_of_le_add him_bounds.2
      exact Real.mem_uIcc_of_bounds hρ.le (And.intro hleft hright)
    have hgraph_shift :
        Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) ≤ z.re - c.re := by
      exact
        Complex.rightDeletedDiskTangentBox_shift_le_of_graphRe_le
          hre_graph_bounds.1
    have hcircle :
        ρ ≤ Real.sqrt ((z.re - c.re) ^ 2 + (z.im - c.im) ^ 2) :=
      (Real.upperTangentBox_outside_circle_iff_graph_right hρ hx hy).mpr
        hgraph_shift
    have hnot_ball : z ∉ Metric.ball c ρ := by
      intro hball
      have hdist_lt : dist z c < ρ := by
        exact Metric.mem_ball.mp hball
      have hdist_ge : ρ ≤ dist z c := by
        exact
          Eq.mpr
            (congrArg
              (fun r : ℝ => ρ ≤ r)
              (Complex.dist_eq_re_im z c))
            hcircle
      exact not_lt_of_ge hdist_ge hdist_lt
    have hre_box : z.re ∈ Set.uIcc c.re (c.re + ρ) := by
      exact
        Real.mem_uIcc_of_bounds
          (Real.binet_le_add_radius c.re ρ hρ.le)
          hre_bounds
    exact ⟨⟨hre_box, him⟩, hnot_ball⟩

/-- If a sequence is identically zero and tends to `a`, then `a = 0`. -/
theorem Complex.eq_zero_of_tendsto_identically_zero
    {ι : Type*}
    {l : Filter ι}
    [l.NeBot]
    {u : ι → ℂ}
    {a : ℂ}
    (hzero : u =ᶠ[l] fun _ => 0)
    (htend : Tendsto u l (𝓝 a)) :
    a = 0 := by
  exact tendsto_nhds_unique (Tendsto.congr' hzero htend) tendsto_const_nhds

end

end LFunctions
end Boundary
