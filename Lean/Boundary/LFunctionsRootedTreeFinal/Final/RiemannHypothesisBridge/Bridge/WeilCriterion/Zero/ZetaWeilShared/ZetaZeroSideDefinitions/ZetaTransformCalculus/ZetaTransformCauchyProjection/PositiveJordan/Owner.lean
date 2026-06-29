import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.PositiveContour.Owner

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

noncomputable def scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant
    (a x T : ℝ) : ℝ :=
  (Real.pi * T / (T - a)) * ((T * x)⁻¹)

/-- The shifted Jordan denominator tends to infinity with the radius. -/
theorem scalarFourierLaplacePlemelj_jordanShiftedDenominator_tendsto_atTop
    (a : ℝ) :
    Tendsto
      (fun T : ℝ => T - a)
      atTop
      atTop :=
  tendsto_atTop_add_const_right (-a) tendsto_id

/-- The Jordan prefactor remainder tends to zero. -/
theorem scalarFourierLaplacePlemelj_jordanPrefactorRemainder_tendsto_zero
    (a : ℝ) :
    Tendsto
      (fun T : ℝ => Real.pi * a / (T - a))
      atTop
      (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (scalarFourierLaplacePlemelj_jordanShiftedDenominator_tendsto_atTop a)

/-- Pointwise algebra splitting of the Jordan prefactor away from its shifted
denominator pole. -/
theorem scalarFourierLaplacePlemelj_jordanPrefactor_eq_pi_add_remainder_of_ne
    (a T : ℝ) (hT : T ≠ a) :
    Real.pi * T / (T - a) =
      Real.pi + Real.pi * a / (T - a) := by
  have hden : T - a ≠ 0 :=
    sub_ne_zero.mpr hT
  calc
    Real.pi * T / (T - a) =
        Real.pi * ((T - a) + a) / (T - a) := by
      exact congrArg
        (fun y : ℝ => Real.pi * y / (T - a))
        (sub_add_cancel T a).symm
    _ = (Real.pi * (T - a) + Real.pi * a) / (T - a) := by
      exact congrArg
        (fun y : ℝ => y / (T - a))
        (mul_add Real.pi (T - a) a)
    _ =
        Real.pi * (T - a) / (T - a) +
          Real.pi * a / (T - a) := by
      exact add_div (Real.pi * (T - a)) (Real.pi * a) (T - a)
    _ =
        Real.pi * ((T - a) / (T - a)) +
          Real.pi * a / (T - a) := by
      exact congrArg
        (fun y : ℝ => y + Real.pi * a / (T - a))
        (mul_div_assoc Real.pi (T - a) (T - a))
    _ = Real.pi * 1 + Real.pi * a / (T - a) := by
      exact congrArg
        (fun y : ℝ => Real.pi * y + Real.pi * a / (T - a))
        (div_self hden)
    _ = Real.pi + Real.pi * a / (T - a) := by
      exact congrArg
        (fun y : ℝ => y + Real.pi * a / (T - a))
        (mul_one Real.pi)

/-- Eventually, the Jordan prefactor splits into its limit plus a vanishing
remainder. -/
theorem scalarFourierLaplacePlemelj_jordanPrefactor_eventually_eq_pi_add_remainder
    (a : ℝ) :
    (fun T : ℝ => Real.pi * T / (T - a)) =ᶠ[atTop]
      (fun T : ℝ => Real.pi + Real.pi * a / (T - a)) := by
  exact
    (eventually_ne_atTop a).mono
      (fun T hT =>
        scalarFourierLaplacePlemelj_jordanPrefactor_eq_pi_add_remainder_of_ne
          a T hT)

/-- The positive upper-arc Jordan prefactor has a finite limit. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_tendsto_pi
    (a : ℝ) :
    Tendsto
      (fun T : ℝ => Real.pi * T / (T - a))
      atTop
      (𝓝 Real.pi) := by
  exact
    Tendsto.congr'
      (scalarFourierLaplacePlemelj_jordanPrefactor_eventually_eq_pi_add_remainder
        a).symm
      (tendsto_const_nhds.add
        (scalarFourierLaplacePlemelj_jordanPrefactorRemainder_tendsto_zero
          a))

/-- The positive upper-arc reciprocal linear factor tends to zero. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanReciprocal_tendsto_zero
    (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ => (T * x)⁻¹)
      atTop
      (𝓝 0) := by
  exact
    tendsto_inv_atTop_zero.comp
      (Tendsto.atTop_mul_const
        (Set.mem_Ioi.mp hx)
        tendsto_id)

/-- The positive upper-arc Jordan majorant tends to zero. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_tendsto_zero
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T)
      atTop
      (𝓝 0) := by
  exact
    (scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_tendsto_pi
      a).mul
      (scalarFourierLaplacePlemelj_positiveUpperArcJordanReciprocal_tendsto_zero
        x hx)

/-- The circular velocity on a positive-radius semicircle has norm equal to the
radius. -/
theorem scalarFourierLaplacePlemelj_semicircleVelocity_norm_eq_radius
    (T : ℝ) (hT : 0 < T) (θ : ℝ) :
    ‖Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = T := by
  have hexp_arg :
      Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I :=
    mul_comm Complex.I (θ : ℂ)
  have hexp_norm :
      ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := by
    exact
      (congrArg
        (fun z : ℂ => ‖Complex.exp z‖)
        hexp_arg).trans
        (Complex.norm_exp_ofReal_mul_I θ)
  have hTnorm :
      ‖(T : ℂ)‖ = T := by
    exact (RCLike.norm_ofReal (K := ℂ) T).trans
      (abs_of_pos hT)
  calc
    ‖Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ =
        ‖Complex.I * (T : ℂ)‖ *
          ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
      exact norm_mul (Complex.I * (T : ℂ))
        (Complex.exp (Complex.I * (θ : ℂ)))
    _ =
        (‖Complex.I‖ * ‖(T : ℂ)‖) *
          ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖Complex.exp (Complex.I * (θ : ℂ))‖)
        (norm_mul Complex.I (T : ℂ))
    _ = (1 * ‖(T : ℂ)‖) *
          ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
      exact congrArg
        (fun r : ℝ => (r * ‖(T : ℂ)‖) *
          ‖Complex.exp (Complex.I * (θ : ℂ))‖)
        Complex.norm_I
    _ = ‖(T : ℂ)‖ *
          ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖Complex.exp (Complex.I * (θ : ℂ))‖)
        (one_mul ‖(T : ℂ)‖)
    _ = T * ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖Complex.exp (Complex.I * (θ : ℂ))‖)
        hTnorm
    _ = T * 1 := by
      exact congrArg
        (fun r : ℝ => T * r)
        hexp_norm
    _ = T := by
      exact mul_one T

/-- Real coordinate of the scalar semicircle point. -/
theorem scalarFourierLaplacePlemelj_semicirclePoint_re
    (T θ : ℝ) :
    ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re =
      T * Real.cos θ := by
  have harg :
      Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I :=
    mul_comm Complex.I (θ : ℂ)
  have hexp_im :
      (Complex.exp (Complex.I * (θ : ℂ))).im = Real.sin θ :=
    (congrArg
      (fun z : ℂ => (Complex.exp z).im)
      harg).trans
      (Complex.exp_ofReal_mul_I_im θ)
  calc
    ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re =
        (T : ℂ).re * (Complex.exp (Complex.I * (θ : ℂ))).re -
          (T : ℂ).im * (Complex.exp (Complex.I * (θ : ℂ))).im := by
      exact Complex.mul_re (T : ℂ)
        (Complex.exp (Complex.I * (θ : ℂ)))
    _ =
        T * (Complex.exp (Complex.I * (θ : ℂ))).re -
          (T : ℂ).im * (Complex.exp (Complex.I * (θ : ℂ))).im := by
      exact congrArg
        (fun r : ℝ =>
          r * (Complex.exp (Complex.I * (θ : ℂ))).re -
            (T : ℂ).im * (Complex.exp (Complex.I * (θ : ℂ))).im)
        (Complex.ofReal_re T)
    _ =
        T * (Complex.exp (Complex.I * (θ : ℂ))).re -
          0 * (Complex.exp (Complex.I * (θ : ℂ))).im := by
      exact congrArg
        (fun r : ℝ =>
          T * (Complex.exp (Complex.I * (θ : ℂ))).re -
            r * (Complex.exp (Complex.I * (θ : ℂ))).im)
        (Complex.ofReal_im T)
    _ =
        T * (Complex.exp (Complex.I * (θ : ℂ))).re - 0 := by
      exact congrArg
        (fun r : ℝ =>
          T * (Complex.exp (Complex.I * (θ : ℂ))).re - r)
        (zero_mul (Complex.exp (Complex.I * (θ : ℂ))).im)
    _ = T * (Complex.exp (Complex.I * (θ : ℂ))).re := by
      exact sub_zero (T * (Complex.exp (Complex.I * (θ : ℂ))).re)
    _ = T * Real.cos θ := by
      exact congrArg
        (fun r : ℝ => T * r)
        hexp_re

/-- Imaginary coordinate of the scalar semicircle point. -/
theorem scalarFourierLaplacePlemelj_semicirclePoint_im
    (T θ : ℝ) :
    ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im =
      T * Real.sin θ := by
  have harg :
      Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I :=
    mul_comm Complex.I (θ : ℂ)
  have hexp_re :
      (Complex.exp (Complex.I * (θ : ℂ))).re = Real.cos θ :=
    (congrArg
      (fun z : ℂ => (Complex.exp z).re)
      harg).trans
      (Complex.exp_ofReal_mul_I_re θ)
  have hexp_im :
      (Complex.exp (Complex.I * (θ : ℂ))).im = Real.sin θ :=
    (congrArg
      (fun z : ℂ => (Complex.exp z).im)
      harg).trans
      (Complex.exp_ofReal_mul_I_im θ)
  calc
    ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im =
        (T : ℂ).re * (Complex.exp (Complex.I * (θ : ℂ))).im +
          (T : ℂ).im * (Complex.exp (Complex.I * (θ : ℂ))).re := by
      exact Complex.mul_im (T : ℂ)
        (Complex.exp (Complex.I * (θ : ℂ)))
    _ =
        T * (Complex.exp (Complex.I * (θ : ℂ))).im +
          (T : ℂ).im * (Complex.exp (Complex.I * (θ : ℂ))).re := by
      exact congrArg
        (fun r : ℝ =>
          r * (Complex.exp (Complex.I * (θ : ℂ))).im +
            (T : ℂ).im * (Complex.exp (Complex.I * (θ : ℂ))).re)
        (Complex.ofReal_re T)
    _ =
        T * (Complex.exp (Complex.I * (θ : ℂ))).im +
          0 * (Complex.exp (Complex.I * (θ : ℂ))).re := by
      exact congrArg
        (fun r : ℝ =>
          T * (Complex.exp (Complex.I * (θ : ℂ))).im +
            r * (Complex.exp (Complex.I * (θ : ℂ))).re)
        (Complex.ofReal_im T)
    _ =
        T * (Complex.exp (Complex.I * (θ : ℂ))).im + 0 := by
      exact congrArg
        (fun r : ℝ =>
          T * (Complex.exp (Complex.I * (θ : ℂ))).im + r)
        (zero_mul (Complex.exp (Complex.I * (θ : ℂ))).re)
    _ = T * (Complex.exp (Complex.I * (θ : ℂ))).im := by
      exact add_zero (T * (Complex.exp (Complex.I * (θ : ℂ))).im)
    _ = T * Real.sin θ := by
      exact congrArg
        (fun r : ℝ => T * r)
        hexp_im

/-- Real part after multiplication by `Complex.I` on the left. -/
theorem scalarFourierLaplacePlemelj_I_mul_semicirclePoint_re
    (T θ : ℝ) :
    (Complex.I * ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re =
      -(T * Real.sin θ) := by
  calc
    (Complex.I * ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re =
        -((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im := by
      exact Complex.I_mul_re
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
    _ = -(T * Real.sin θ) := by
      exact congrArg Neg.neg
        (scalarFourierLaplacePlemelj_semicirclePoint_im T θ)

/-- Real scalar rearrangement for the circular exponent damping term. -/
theorem scalarFourierLaplacePlemelj_semicircleExponent_scalar_rearrange
    (x T θ : ℝ) :
    (-(T * Real.sin θ)) * x = -(T * x * Real.sin θ) := by
  have hinner :
      (T * Real.sin θ) * x = T * x * Real.sin θ := by
    calc
      (T * Real.sin θ) * x = T * (Real.sin θ * x) := by
        exact mul_assoc T (Real.sin θ) x
      _ = T * (x * Real.sin θ) := by
        exact congrArg
          (fun r : ℝ => T * r)
          (mul_comm (Real.sin θ) x)
      _ = T * x * Real.sin θ := by
        exact (mul_assoc T x (Real.sin θ)).symm
  calc
    (-(T * Real.sin θ)) * x =
        -((T * Real.sin θ) * x) := by
      exact neg_mul (T * Real.sin θ) x
    _ = -(T * x * Real.sin θ) := by
      exact congrArg Neg.neg hinner

/-- Real part of the scalar Fourier-Laplace exponent on a circular arc. -/
theorem scalarFourierLaplacePlemelj_semicircleExponent_re
    (x T θ : ℝ) :
    (Complex.I *
      ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (x : ℂ)).re =
      -(T * x * Real.sin θ) := by
  calc
    (Complex.I *
      ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (x : ℂ)).re =
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re *
          (x : ℂ).re -
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).im *
          (x : ℂ).im := by
      exact Complex.mul_re
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (x : ℂ)
    _ =
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re *
          x -
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).im *
          (x : ℂ).im := by
      exact congrArg
        (fun r : ℝ =>
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re *
            r -
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).im *
            (x : ℂ).im)
        (Complex.ofReal_re x)
    _ =
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re *
          x -
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).im *
          0 := by
      exact congrArg
        (fun r : ℝ =>
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re *
            x -
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).im *
            r)
        (Complex.ofReal_im x)
    _ =
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re * x -
        0 := by
      exact congrArg
        (fun r : ℝ =>
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re * x - r)
        (mul_zero
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).im)
    _ =
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re * x := by
      exact sub_zero
        ((Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re * x)
    _ = (-(T * Real.sin θ)) * x := by
      exact congrArg
        (fun r : ℝ => r * x)
        (scalarFourierLaplacePlemelj_I_mul_semicirclePoint_re T θ)
    _ = -(T * x * Real.sin θ) := by
      exact scalarFourierLaplacePlemelj_semicircleExponent_scalar_rearrange
        x T θ

/-- The denominator arc factor has radius norm. -/
theorem scalarFourierLaplacePlemelj_semicirclePoint_mul_I_norm_eq_radius
    (T : ℝ) (hT : 0 < T) (θ : ℝ) :
    ‖((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I‖ = T := by
  have harg :
      Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I :=
    mul_comm Complex.I (θ : ℂ)
  have hexp_norm :
      ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 :=
    (congrArg
      (fun z : ℂ => ‖Complex.exp z‖)
      harg).trans
      (Complex.norm_exp_ofReal_mul_I θ)
  have hTnorm :
      ‖(T : ℂ)‖ = T :=
    (RCLike.norm_ofReal (K := ℂ) T).trans
      (abs_of_pos hT)
  calc
    ‖((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I‖ =
        ‖(T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ *
          ‖Complex.I‖ := by
      exact norm_mul
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        Complex.I
    _ =
        (‖(T : ℂ)‖ *
          ‖Complex.exp (Complex.I * (θ : ℂ))‖) *
          ‖Complex.I‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖Complex.I‖)
        (norm_mul (T : ℂ) (Complex.exp (Complex.I * (θ : ℂ))))
    _ =
        (T * ‖Complex.exp (Complex.I * (θ : ℂ))‖) *
          ‖Complex.I‖ := by
      exact congrArg
        (fun r : ℝ =>
          (r * ‖Complex.exp (Complex.I * (θ : ℂ))‖) *
            ‖Complex.I‖)
        hTnorm
    _ = (T * 1) * ‖Complex.I‖ := by
      exact congrArg
        (fun r : ℝ => (T * r) * ‖Complex.I‖)
        hexp_norm
    _ = T * ‖Complex.I‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖Complex.I‖)
        (mul_one T)
    _ = T * 1 := by
      exact congrArg
        (fun r : ℝ => T * r)
        Complex.norm_I
    _ = T := by
      exact mul_one T

/-- Reverse-triangle lower bound for the scalar Cauchy denominator on a
semicircle of radius larger than `a`. -/
theorem scalarFourierLaplacePlemelj_semicircleDenominator_norm_ge_radius_sub
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : a < T) (θ : ℝ) :
    T - a ≤
      ‖(a : ℂ) +
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I‖ := by
  let zI : ℂ :=
    ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I
  have hTpos : 0 < T :=
    ha.trans hT
  have hzI_norm : ‖zI‖ = T := by
    exact scalarFourierLaplacePlemelj_semicirclePoint_mul_I_norm_eq_radius
      T hTpos θ
  have hneg_norm : ‖(-(a : ℂ))‖ = a := by
    calc
      ‖(-(a : ℂ))‖ = ‖(a : ℂ)‖ := by
        exact norm_neg (a : ℂ)
      _ = |a| := by
        exact RCLike.norm_ofReal (K := ℂ) a
      _ = a := by
        exact abs_of_pos ha
  have hdenom :
      zI - (-(a : ℂ)) =
        (a : ℂ) +
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I := by
    calc
      zI - (-(a : ℂ)) = zI + -(-(a : ℂ)) := by
        exact sub_eq_add_neg zI (-(a : ℂ))
      _ = zI + (a : ℂ) := by
        exact congrArg
          (fun w : ℂ => zI + w)
          (neg_neg (a : ℂ))
      _ = (a : ℂ) + zI := by
        exact add_comm zI (a : ℂ)
      _ =
          (a : ℂ) +
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              Complex.I := by
        exact rfl
  calc
    T - a = ‖zI‖ - ‖(-(a : ℂ))‖ := by
      exact congrArg₂ HSub.hSub hzI_norm.symm hneg_norm.symm
    _ ≤ ‖zI - (-(a : ℂ))‖ := by
      exact norm_sub_norm_le zI (-(a : ℂ))
    _ =
        ‖(a : ℂ) +
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            Complex.I‖ := by
      exact congrArg norm hdenom

/-- Inverse form of the scalar Cauchy denominator lower bound on a semicircle. -/
theorem scalarFourierLaplacePlemelj_semicircleDenominator_inv_norm_le
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : a < T) (θ : ℝ) :
    ‖(-1 /
      ((a : ℂ) +
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I))‖ ≤
      (T - a)⁻¹ := by
  let den : ℂ :=
    (a : ℂ) +
      ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I
  have hsub_pos : 0 < T - a :=
    sub_pos.mpr hT
  have hden_ge : T - a ≤ ‖den‖ :=
    scalarFourierLaplacePlemelj_semicircleDenominator_norm_ge_radius_sub
      a ha T hT θ
  have hnorm :
      ‖(-1 : ℂ) / den‖ = ‖den‖⁻¹ := by
    calc
      ‖(-1 : ℂ) / den‖ = ‖(-1 : ℂ)‖ / ‖den‖ := by
        exact norm_div (-1 : ℂ) den
      _ = ‖(1 : ℂ)‖ / ‖den‖ := by
        exact congrArg
          (fun r : ℝ => r / ‖den‖)
          (norm_neg (1 : ℂ))
      _ = 1 / ‖den‖ := by
        exact congrArg
          (fun r : ℝ => r / ‖den‖)
          norm_one
      _ = ‖den‖⁻¹ := by
        exact one_div ‖den‖
  exact hnorm.trans_le
    (inv_anti₀ hsub_pos hden_ge)

/-- Algebraic normal form of the Jordan pointwise density. -/
theorem scalarFourierLaplacePlemelj_jordanDensity_eq_inv_mul_exp_mul_radius
    (a T E : ℝ) :
    (T / (T - a)) * E = ((T - a)⁻¹ * E) * T := by
  calc
    (T / (T - a)) * E = (T * (T - a)⁻¹) * E := by
      exact congrArg
        (fun r : ℝ => r * E)
        (div_eq_mul_inv T (T - a))
    _ = T * ((T - a)⁻¹ * E) := by
      exact mul_assoc T (T - a)⁻¹ E
    _ = ((T - a)⁻¹ * E) * T := by
      exact mul_comm T ((T - a)⁻¹ * E)

/-- Algebraic normal form for the Jordan density integral majorant. -/
theorem scalarFourierLaplacePlemelj_jordanPrefactor_mul_pi_inv_eq_majorant
    (a T Y : ℝ) :
    (T / (T - a)) * (Real.pi * Y⁻¹) =
      (Real.pi * T / (T - a)) * Y⁻¹ := by
  calc
    (T / (T - a)) * (Real.pi * Y⁻¹) =
        (T * (T - a)⁻¹) * (Real.pi * Y⁻¹) := by
      exact congrArg
        (fun r : ℝ => r * (Real.pi * Y⁻¹))
        (div_eq_mul_inv T (T - a))
    _ = ((T * (T - a)⁻¹) * Real.pi) * Y⁻¹ := by
      exact mul_assoc (T * (T - a)⁻¹) Real.pi Y⁻¹
    _ = (Real.pi * (T * (T - a)⁻¹)) * Y⁻¹ := by
      exact congrArg
        (fun r : ℝ => r * Y⁻¹)
        (mul_comm (T * (T - a)⁻¹) Real.pi)
    _ = ((Real.pi * T) * (T - a)⁻¹) * Y⁻¹ := by
      exact congrArg
        (fun r : ℝ => r * Y⁻¹)
        (mul_assoc Real.pi T (T - a)⁻¹)
    _ = (Real.pi * T / (T - a)) * Y⁻¹ := by
      exact congrArg
        (fun r : ℝ => r * Y⁻¹)
        (div_eq_mul_inv (Real.pi * T) (T - a)).symm

/-- Denominator part of the positive upper-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_denominator_norm_inv_le
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : a < T) (θ : ℝ) :
    ‖(-1 /
      ((a : ℂ) +
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I))‖ ≤
      (T - a)⁻¹ := by
  exact
    scalarFourierLaplacePlemelj_semicircleDenominator_inv_norm_le
      a ha T hT θ

/-- Exponential damping part of the positive upper-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_exponential_norm_eq_damping
    (x T θ : ℝ) :
    ‖Complex.exp
      (Complex.I *
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (x : ℂ))‖ =
      Real.exp (-(T * x * Real.sin θ)) := by
  calc
    ‖Complex.exp
      (Complex.I *
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (x : ℂ))‖ =
        Complex.abs
          (Complex.exp
            (Complex.I *
              ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (x : ℂ))) := by
      exact Complex.norm_eq_abs
        (Complex.exp
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (x : ℂ)))
    _ =
        Real.exp
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (x : ℂ)).re := by
      exact Complex.abs_exp
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (x : ℂ))
    _ = Real.exp (-(T * x * Real.sin θ)) := by
      exact congrArg Real.exp
        (scalarFourierLaplacePlemelj_semicircleExponent_re x T θ)

/-- Velocity part of the positive upper-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_velocity_norm_eq_radius
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : a < T) (θ : ℝ) :
    ‖Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = T := by
  exact
    scalarFourierLaplacePlemelj_semicircleVelocity_norm_eq_radius
      T (ha.trans hT) θ

/-- Product assembly for the positive upper-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcIntegrand_norm_le_jordanDensity_of_factors
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) (θ : ℝ)
    (hden :
      ‖(-1 /
        ((a : ℂ) +
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I))‖ ≤
        (T - a)⁻¹)
    (hexp :
      ‖Complex.exp
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (x : ℂ))‖ =
        Real.exp (-(T * x * Real.sin θ)))
    (hvel :
      ‖Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = T) :
    ‖scalarFourierLaplacePlemelj_positiveUpperArcIntegrand a x T θ‖ ≤
      scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ := by
  let D : ℂ :=
    -1 /
      ((a : ℂ) +
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I)
  let E : ℂ :=
    Complex.exp
      (Complex.I *
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (x : ℂ))
  let V : ℂ :=
    Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  let R : ℝ :=
    Real.exp (-(T * x * Real.sin θ))
  have hER : ‖E‖ = R := by
    exact hexp
  have hVR : ‖V‖ = T := by
    exact hvel
  have hV_nonneg : 0 ≤ ‖V‖ :=
    norm_nonneg V
  have hstep :
      (‖D‖ * ‖E‖) * ‖V‖ ≤
        ((T - a)⁻¹ * ‖E‖) * ‖V‖ := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hden (norm_nonneg E))
      hV_nonneg
  calc
    ‖scalarFourierLaplacePlemelj_positiveUpperArcIntegrand a x T θ‖ =
        ‖D * E * V‖ := by
      exact rfl
    _ = ‖D * E‖ * ‖V‖ := by
      exact norm_mul (D * E) V
    _ = (‖D‖ * ‖E‖) * ‖V‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖V‖)
        (norm_mul D E)
    _ ≤ ((T - a)⁻¹ * ‖E‖) * ‖V‖ := by
      exact hstep
    _ = ((T - a)⁻¹ * R) * ‖V‖ := by
      exact congrArg
        (fun r : ℝ => ((T - a)⁻¹ * r) * ‖V‖)
        hER
    _ = ((T - a)⁻¹ * R) * T := by
      exact congrArg
        (fun r : ℝ => ((T - a)⁻¹ * R) * r)
        hVR
    _ = (T / (T - a)) * R := by
      exact
        (scalarFourierLaplacePlemelj_jordanDensity_eq_inv_mul_exp_mul_radius
          a T R).symm
    _ = scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ := by
      exact rfl

/-- Pointwise Jordan domination of the positive upper-arc integrand. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcIntegrand_norm_le_jordanDensity
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) (θ : ℝ) :
    ‖scalarFourierLaplacePlemelj_positiveUpperArcIntegrand a x T θ‖ ≤
      scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ := by
  exact
    scalarFourierLaplacePlemelj_positiveUpperArcIntegrand_norm_le_jordanDensity_of_factors
      a ha x hx T hT θ
      (scalarFourierLaplacePlemelj_positiveUpperArc_denominator_norm_inv_le
        a ha T hT θ)
      (scalarFourierLaplacePlemelj_positiveUpperArc_exponential_norm_eq_damping
        x T θ)
      (scalarFourierLaplacePlemelj_positiveUpperArc_velocity_norm_eq_radius
        a ha T hT θ)

/-- The positive upper-arc Jordan density is interval-integrable. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_intervalIntegrable
    (a x T : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ)
      MeasureTheory.volume
      (0 : ℝ)
      Real.pi := by
  have harg :
      Continuous
        (fun θ : ℝ => -(T * x * Real.sin θ)) := by
    exact (continuous_const.mul Real.continuous_sin).neg
  have hexp :
      Continuous
        (fun θ : ℝ => Real.exp (-(T * x * Real.sin θ))) := by
    exact Real.continuous_exp.comp harg
  have hdensity :
      Continuous
        (fun θ : ℝ =>
          scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ) := by
    exact continuous_const.mul hexp
  exact hdensity.intervalIntegrable (0 : ℝ) Real.pi

/-- The positive upper-arc Jordan density is nonnegative when the radius is
larger than the pole height. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_nonneg
    (a : ℝ) (ha : 0 < a) (x T θ : ℝ) (hT : a < T) :
    0 ≤ scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ := by
  have hTpos : 0 < T :=
    ha.trans hT
  have hdenpos : 0 < T - a :=
    sub_pos.mpr hT
  have hpref_nonneg : 0 ≤ T / (T - a) :=
    div_nonneg hTpos.le hdenpos.le
  exact mul_nonneg hpref_nonneg (Real.exp_pos _).le

/-- The positive Jordan density interval integral factors into the constant
prefactor times the scalar sine-damping integral. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_integral_eq_prefactor_mul
    (a : ℝ) (T x : ℝ) :
    ∫ θ in (0 : ℝ)..Real.pi,
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ =
      (T / (T - a)) *
        ∫ θ in (0 : ℝ)..Real.pi,
          Real.exp (-(T * x * Real.sin θ)) := by
  exact intervalIntegral.integral_const_mul
    (T / (T - a))
    (fun θ : ℝ => Real.exp (-(T * x * Real.sin θ)))

/-- The upper sine-damping integrand is interval-integrable on any finite
interval. -/
theorem scalarFourierLaplacePlemelj_upperSineDamping_intervalIntegrable
    (c a b : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ => Real.exp (-(c * Real.sin θ)))
      MeasureTheory.volume
      a
      b := by
  have harg :
      Continuous
        (fun θ : ℝ => -(c * Real.sin θ)) := by
    exact (continuous_const.mul Real.continuous_sin).neg
  have hintegrand :
      Continuous
        (fun θ : ℝ => Real.exp (-(c * Real.sin θ))) := by
    exact Real.continuous_exp.comp harg
  exact hintegrand.intervalIntegrable a b

/-- The upper sine-damping integral splits at `π / 2`. -/
theorem scalarFourierLaplacePlemelj_upperSineDampingIntegral_split_half
    (c : ℝ) :
    ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-(c * Real.sin θ)) =
      (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(c * Real.sin θ))) +
      ∫ θ in (Real.pi / 2)..Real.pi,
        Real.exp (-(c * Real.sin θ)) := by
  have hleft :
      IntervalIntegrable
        (fun θ : ℝ => Real.exp (-(c * Real.sin θ)))
        MeasureTheory.volume
        (0 : ℝ)
        (Real.pi / 2) :=
    scalarFourierLaplacePlemelj_upperSineDamping_intervalIntegrable
      c (0 : ℝ) (Real.pi / 2)
  have hright :
      IntervalIntegrable
        (fun θ : ℝ => Real.exp (-(c * Real.sin θ)))
        MeasureTheory.volume
        (Real.pi / 2)
        Real.pi :=
    scalarFourierLaplacePlemelj_upperSineDamping_intervalIntegrable
      c (Real.pi / 2) Real.pi
  exact
    (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm

/-- Pointwise reflection identity for the sine-damping integrand. -/
theorem scalarFourierLaplacePlemelj_upperSineDamping_pi_sub_eq
    (c θ : ℝ) :
    Real.exp (-(c * Real.sin (Real.pi - θ))) =
      Real.exp (-(c * Real.sin θ)) := by
  exact congrArg
    (fun r : ℝ => Real.exp (-(c * r)))
    (Real.sin_pi_sub θ)

/-- Endpoint transport for reflecting the right half interval. -/
theorem scalarFourierLaplacePlemelj_upperSineDamping_reflectedEndpointIntegral_eq
    (c : ℝ) :
    (∫ θ in (Real.pi - Real.pi / 2)..(Real.pi - 0),
        Real.exp (-(c * Real.sin θ))) =
      ∫ θ in (Real.pi / 2)..Real.pi,
        Real.exp (-(c * Real.sin θ)) := by
  have hleft : Real.pi - Real.pi / 2 = Real.pi / 2 :=
    sub_half Real.pi
  have hright : Real.pi - 0 = Real.pi :=
    sub_zero Real.pi
  exact congrArg₂
    (fun u v : ℝ =>
      ∫ θ in u..v, Real.exp (-(c * Real.sin θ)))
    hleft
    hright

/-- Reflection of the upper sine-damping right half onto the left half. -/
theorem scalarFourierLaplacePlemelj_upperSineDampingIntegral_rightHalf_eq_leftHalf
    (c : ℝ) :
    ∫ θ in (Real.pi / 2)..Real.pi,
        Real.exp (-(c * Real.sin θ)) =
      ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(c * Real.sin θ)) := by
  calc
    ∫ θ in (Real.pi / 2)..Real.pi,
        Real.exp (-(c * Real.sin θ)) =
        ∫ θ in (Real.pi - Real.pi / 2)..(Real.pi - 0),
          Real.exp (-(c * Real.sin θ)) := by
      exact
        (scalarFourierLaplacePlemelj_upperSineDamping_reflectedEndpointIntegral_eq
          c).symm
    _ = ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(c * Real.sin (Real.pi - θ))) := by
      exact
        (intervalIntegral.integral_comp_sub_left
          (f := fun θ : ℝ => Real.exp (-(c * Real.sin θ)))
          (a := (0 : ℝ))
          (b := Real.pi / 2)
          (d := Real.pi)).symm
    _ = ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(c * Real.sin θ)) := by
      exact intervalIntegral.integral_congr
        (fun θ _hθ =>
          scalarFourierLaplacePlemelj_upperSineDamping_pi_sub_eq c θ)

/-- Symmetry of the upper semicircle sine-damping integral around `π / 2`. -/
theorem scalarFourierLaplacePlemelj_upperSineDampingIntegral_eq_two_half
    (c : ℝ) :
    ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-(c * Real.sin θ)) =
      2 * ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(c * Real.sin θ)) := by
  let L : ℝ :=
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
      Real.exp (-(c * Real.sin θ))
  calc
    ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-(c * Real.sin θ)) =
        L +
        ∫ θ in (Real.pi / 2)..Real.pi,
          Real.exp (-(c * Real.sin θ)) := by
      exact scalarFourierLaplacePlemelj_upperSineDampingIntegral_split_half c
    _ = L + L := by
      exact congrArg
        (fun r : ℝ => L + r)
        (scalarFourierLaplacePlemelj_upperSineDampingIntegral_rightHalf_eq_leftHalf
          c)
    _ = 2 * L := by
      exact (two_mul L).symm

/-- Jordan lower bound converted into an upper bound for the upper half
sine-damping exponential. -/
theorem scalarFourierLaplacePlemelj_upperSineDamping_integrand_le_linearExp
    (c θ : ℝ) (hc : 0 < c)
    (hθ0 : 0 ≤ θ) (hθhalf : θ ≤ Real.pi / 2) :
    Real.exp (-(c * Real.sin θ)) ≤
      Real.exp (-(((2 * c) / Real.pi) * θ)) := by
  have hsin : (2 / Real.pi : ℝ) * θ ≤ Real.sin θ :=
    Real.mul_le_sin hθ0 hθhalf
  have hmul : c * ((2 / Real.pi : ℝ) * θ) ≤ c * Real.sin θ :=
    mul_le_mul_of_nonneg_left hsin hc.le
  have halg :
      ((2 * c) / Real.pi) * θ =
        c * ((2 / Real.pi : ℝ) * θ) := by
    calc
      ((2 * c) / Real.pi) * θ =
          ((2 * c) * Real.pi⁻¹) * θ := by
        exact congrArg
          (fun r : ℝ => r * θ)
          (div_eq_mul_inv (2 * c) Real.pi)
      _ = (c * (2 * Real.pi⁻¹)) * θ := by
        have htwo_c : 2 * c = c * 2 :=
          mul_comm 2 c
        exact congrArg
          (fun r : ℝ => (r * Real.pi⁻¹) * θ)
          htwo_c
      _ = c * ((2 * Real.pi⁻¹) * θ) := by
        exact mul_assoc c (2 * Real.pi⁻¹) θ
      _ = c * ((2 / Real.pi : ℝ) * θ) := by
        exact congrArg
          (fun r : ℝ => c * (r * θ))
          (div_eq_mul_inv 2 Real.pi).symm
  have harg :
      -(c * Real.sin θ) ≤ -(((2 * c) / Real.pi) * θ) := by
    exact neg_le_neg
      (halg.trans_le hmul)
  exact Real.exp_le_exp.mpr harg

/-- Elementary exponential integral bound on the upper half interval. -/
theorem scalarFourierLaplacePlemelj_upperLinearExp_integral_eq_scaled_one_sub_exp
    (c : ℝ) (hc : 0 < c) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(((2 * c) / Real.pi) * θ)) =
      ((Real.pi / 2) * c⁻¹) * (1 - Real.exp (-c)) := by
  let k : ℝ := (2 * c) / Real.pi
  let A : ℝ := (Real.pi / 2) * c⁻¹
  have hpi_ne : Real.pi ≠ 0 :=
    Real.pi_pos.ne'
  have hc_ne : c ≠ 0 :=
    hc.ne'
  have hk_pos : 0 < k := by
    exact div_pos (mul_pos zero_lt_two hc) Real.pi_pos
  have hk_ne : k ≠ 0 :=
    hk_pos.ne'
  have harg :
      (fun θ : ℝ => Real.exp (-(((2 * c) / Real.pi) * θ))) =
        fun θ : ℝ => Real.exp ((-k) * θ) := by
    exact funext
      (fun θ : ℝ =>
        calc
          Real.exp (-(((2 * c) / Real.pi) * θ)) =
              Real.exp (-(k * θ)) := by
            exact congrArg Real.exp
              (congrArg Neg.neg
                (congrArg (fun r : ℝ => r * θ) rfl))
          _ = Real.exp ((-k) * θ) := by
            exact congrArg Real.exp
              (neg_mul k θ).symm)
  have hendpoint_zero : (-k) * (0 : ℝ) = 0 :=
    mul_zero (-k)
  have hendpoint_half : (-k) * (Real.pi / 2) = -c := by
    calc
      (-k) * (Real.pi / 2) =
          -(k * (Real.pi / 2)) := by
        exact neg_mul k (Real.pi / 2)
      _ = -(((2 * c) / Real.pi) * (Real.pi / 2)) := by
        exact congrArg Neg.neg
          (congrArg (fun r : ℝ => r * (Real.pi / 2)) rfl)
      _ = -(((2 * c) * Real.pi⁻¹) * (Real.pi / 2)) := by
        exact congrArg Neg.neg
          (congrArg (fun r : ℝ => r * (Real.pi / 2))
            (div_eq_mul_inv (2 * c) Real.pi))
      _ = -((2 * c) * (Real.pi⁻¹ * (Real.pi / 2))) := by
        exact congrArg Neg.neg
          (mul_assoc (2 * c) Real.pi⁻¹ (Real.pi / 2))
      _ = -((2 * c) * ((Real.pi⁻¹ * Real.pi) / 2)) := by
        exact congrArg
          (fun r : ℝ => -((2 * c) * r))
          (mul_div_assoc Real.pi⁻¹ Real.pi 2).symm
      _ = -((2 * c) * (1 / 2)) := by
        exact congrArg
          (fun r : ℝ => -((2 * c) * (r / 2)))
          (inv_mul_cancel₀ hpi_ne)
      _ = -(((2 * c) / 2)) := by
        exact congrArg Neg.neg
          (mul_div_assoc 2 c 2)
      _ = -c := by
        exact congrArg Neg.neg
          (mul_div_cancel_left₀ c two_ne_zero)
  have hscale_mul_k : A * k = 1 := by
    calc
      A * k =
          ((Real.pi / 2) * c⁻¹) * ((2 * c) / Real.pi) := by
        exact rfl
      _ = ((Real.pi / 2) * c⁻¹) * ((2 * c) * Real.pi⁻¹) := by
        exact congrArg
          (fun r : ℝ => ((Real.pi / 2) * c⁻¹) * r)
          (div_eq_mul_inv (2 * c) Real.pi)
      _ = (Real.pi / 2) * (c⁻¹ * ((2 * c) * Real.pi⁻¹)) := by
        exact mul_assoc (Real.pi / 2) c⁻¹ ((2 * c) * Real.pi⁻¹)
      _ = (Real.pi / 2) * ((c⁻¹ * (2 * c)) * Real.pi⁻¹) := by
        exact congrArg
          (fun r : ℝ => (Real.pi / 2) * r)
          (mul_assoc c⁻¹ (2 * c) Real.pi⁻¹)
      _ = (Real.pi / 2) * (((c⁻¹ * c) * 2) * Real.pi⁻¹) := by
        have htwo_c : 2 * c = c * 2 :=
          mul_comm 2 c
        have hstep :
            c⁻¹ * (2 * c) = (c⁻¹ * c) * 2 := by
          calc
            c⁻¹ * (2 * c) = c⁻¹ * (c * 2) := by
              exact congrArg (fun r : ℝ => c⁻¹ * r) htwo_c
            _ = (c⁻¹ * c) * 2 := by
              exact mul_assoc c⁻¹ c 2
        exact congrArg
          (fun r : ℝ => (Real.pi / 2) * (r * Real.pi⁻¹))
          hstep
      _ = (Real.pi / 2) * ((1 * 2) * Real.pi⁻¹) := by
        exact congrArg
          (fun r : ℝ => (Real.pi / 2) * ((r * 2) * Real.pi⁻¹))
          (inv_mul_cancel₀ hc_ne)
      _ = (Real.pi / 2) * (2 * Real.pi⁻¹) := by
        exact congrArg
          (fun r : ℝ => (Real.pi / 2) * (r * Real.pi⁻¹))
          (one_mul 2)
      _ = ((Real.pi / 2) * 2) * Real.pi⁻¹ := by
        exact (mul_assoc (Real.pi / 2) 2 Real.pi⁻¹).symm
      _ = Real.pi * Real.pi⁻¹ := by
        exact congrArg
          (fun r : ℝ => r * Real.pi⁻¹)
          (div_mul_cancel₀ Real.pi two_ne_zero)
      _ = 1 := by
        exact mul_inv_cancel₀ hpi_ne
  have hneg_inv : (-k)⁻¹ = -A := by
    have hmul : (-A) * (-k) = 1 := by
      calc
        (-A) * (-k) = A * k := by
          exact neg_mul_neg A k
        _ = 1 := hscale_mul_k
    exact eq_inv_of_mul_eq_one_left hmul
  have hintegral :
      ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp ((-k) * θ) =
        (-k)⁻¹ *
          (Real.exp ((-k) * (Real.pi / 2)) -
            Real.exp ((-k) * (0 : ℝ))) := by
    calc
      ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp ((-k) * θ) =
          (-k)⁻¹ •
            ∫ y in ((-k) * (0 : ℝ))..((-k) * (Real.pi / 2)),
              Real.exp y := by
        exact intervalIntegral.integral_comp_mul_left
          (f := Real.exp)
          (a := (0 : ℝ))
          (b := Real.pi / 2)
          (c := -k)
          (neg_ne_zero.mpr hk_ne)
      _ =
          (-k)⁻¹ *
            (Real.exp ((-k) * (Real.pi / 2)) -
              Real.exp ((-k) * (0 : ℝ))) := by
        exact congrArg
          (fun r : ℝ => (-k)⁻¹ * r)
          (integral_exp
            (a := (-k) * (0 : ℝ))
            (b := (-k) * (Real.pi / 2)))
  calc
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(((2 * c) / Real.pi) * θ)) =
        ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp ((-k) * θ) := by
      exact congrArg
        (fun f : ℝ → ℝ => ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ)
        harg
    _ =
        (-k)⁻¹ *
          (Real.exp ((-k) * (Real.pi / 2)) -
            Real.exp ((-k) * (0 : ℝ))) := by
      exact hintegral
    _ = (-A) * (Real.exp (-c) - Real.exp ((-k) * (0 : ℝ))) := by
      exact congrArg₂
        (fun u v : ℝ =>
          u * (Real.exp v - Real.exp ((-k) * (0 : ℝ))))
        hneg_inv
        hendpoint_half
    _ = (-A) * (Real.exp (-c) - Real.exp 0) := by
      exact congrArg
        (fun r : ℝ => (-A) * (Real.exp (-c) - Real.exp r))
        hendpoint_zero
    _ = (-A) * (Real.exp (-c) - 1) := by
      exact congrArg
        (fun r : ℝ => (-A) * (Real.exp (-c) - r))
        Real.exp_zero
    _ = A * (1 - Real.exp (-c)) := by
      calc
        (-A) * (Real.exp (-c) - 1) =
            A * (-(Real.exp (-c) - 1)) := by
          exact neg_mul_eq_mul_neg A (Real.exp (-c) - 1)
        _ = A * (1 - Real.exp (-c)) := by
          exact congrArg
            (fun r : ℝ => A * r)
            (neg_sub (Real.exp (-c)) 1)
    _ = ((Real.pi / 2) * c⁻¹) * (1 - Real.exp (-c)) := by
      exact rfl

/-- The finite exponential loss factor is bounded by one. -/
theorem scalarFourierLaplacePlemelj_one_sub_exp_neg_le_one
    (c : ℝ) :
    1 - Real.exp (-c) ≤ 1 := by
  exact sub_le_self 1 (Real.exp_pos (-c)).le

/-- The scale factor in the elementary exponential integral is nonnegative. -/
theorem scalarFourierLaplacePlemelj_upperLinearExp_scale_nonneg
    (c : ℝ) (hc : 0 < c) :
    0 ≤ (Real.pi / 2) * c⁻¹ := by
  have hhalf_nonneg : 0 ≤ Real.pi / 2 :=
    half_nonneg Real.pi_nonneg
  have hinv_nonneg : 0 ≤ c⁻¹ :=
    inv_nonneg.mpr hc.le
  exact mul_nonneg hhalf_nonneg hinv_nonneg

/-- Elementary exponential integral bound on the upper half interval. -/
theorem scalarFourierLaplacePlemelj_upperLinearExp_integral_le
    (c : ℝ) (hc : 0 < c) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(((2 * c) / Real.pi) * θ)) ≤
      (Real.pi / 2) * c⁻¹ := by
  calc
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(((2 * c) / Real.pi) * θ)) =
        ((Real.pi / 2) * c⁻¹) * (1 - Real.exp (-c)) := by
      exact
        scalarFourierLaplacePlemelj_upperLinearExp_integral_eq_scaled_one_sub_exp
          c hc
    _ ≤ ((Real.pi / 2) * c⁻¹) * 1 := by
      exact mul_le_mul_of_nonneg_left
        (scalarFourierLaplacePlemelj_one_sub_exp_neg_le_one c)
        (scalarFourierLaplacePlemelj_upperLinearExp_scale_nonneg c hc)
    _ = (Real.pi / 2) * c⁻¹ := by
      exact mul_one ((Real.pi / 2) * c⁻¹)

/-- Pointwise Jordan's inequality integrates to comparison with the elementary
linear exponential on the upper half interval. -/
theorem scalarFourierLaplacePlemelj_upperSineDamping_halfIntegral_le_linearExpIntegral
    (c : ℝ) (hc : 0 < c) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(c * Real.sin θ)) ≤
      ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(((2 * c) / Real.pi) * θ)) := by
  have hhalf_nonneg : (0 : ℝ) ≤ Real.pi / 2 :=
    half_nonneg Real.pi_nonneg
  have hsine_cont :
      Continuous
        (fun θ : ℝ => Real.exp (-(c * Real.sin θ))) := by
    have harg :
        Continuous
          (fun θ : ℝ => -(c * Real.sin θ)) := by
      exact (continuous_const.mul Real.continuous_sin).neg
    exact Real.continuous_exp.comp harg
  have hlinear_cont :
      Continuous
        (fun θ : ℝ => Real.exp (-(((2 * c) / Real.pi) * θ))) := by
    have harg :
        Continuous
          (fun θ : ℝ => -(((2 * c) / Real.pi) * θ)) := by
      exact (continuous_const.mul continuous_id).neg
    exact Real.continuous_exp.comp harg
  have hsine_int :
      IntervalIntegrable
        (fun θ : ℝ => Real.exp (-(c * Real.sin θ)))
        MeasureTheory.volume
        (0 : ℝ)
        (Real.pi / 2) :=
    hsine_cont.intervalIntegrable (0 : ℝ) (Real.pi / 2)
  have hlinear_int :
      IntervalIntegrable
        (fun θ : ℝ => Real.exp (-(((2 * c) / Real.pi) * θ)))
        MeasureTheory.volume
        (0 : ℝ)
        (Real.pi / 2) :=
    hlinear_cont.intervalIntegrable (0 : ℝ) (Real.pi / 2)
  exact intervalIntegral.integral_mono_on
    hhalf_nonneg
    hsine_int
    hlinear_int
    (fun θ hθ =>
      scalarFourierLaplacePlemelj_upperSineDamping_integrand_le_linearExp
        c θ hc hθ.1 hθ.2)

/-- Upper half-interval Jordan sine-damping integral bound. -/
theorem scalarFourierLaplacePlemelj_upperSineDamping_halfIntegral_le
    (c : ℝ) (hc : 0 < c) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(c * Real.sin θ)) ≤
      (Real.pi / 2) * c⁻¹ := by
  exact
    (scalarFourierLaplacePlemelj_upperSineDamping_halfIntegral_le_linearExpIntegral
      c hc).trans
      (scalarFourierLaplacePlemelj_upperLinearExp_integral_le c hc)

/-- The doubled half-interval majorant is the full Jordan majorant. -/
theorem scalarFourierLaplacePlemelj_two_mul_upperHalfMajorant_eq
    (c : ℝ) :
    2 * ((Real.pi / 2) * c⁻¹) = Real.pi * c⁻¹ := by
  calc
    2 * ((Real.pi / 2) * c⁻¹) =
        (2 * (Real.pi / 2)) * c⁻¹ := by
      exact mul_assoc 2 (Real.pi / 2) c⁻¹
    _ = ((2 * Real.pi) / 2) * c⁻¹ := by
      exact congrArg
        (fun r : ℝ => r * c⁻¹)
        (mul_div_assoc 2 Real.pi 2).symm
    _ = Real.pi * c⁻¹ := by
      have htwo_ne : (2 : ℝ) ≠ 0 :=
        two_ne_zero
      have hcancel : (2 * Real.pi) / 2 = Real.pi := by
        exact mul_div_cancel_left₀ Real.pi htwo_ne
      exact congrArg
        (fun r : ℝ => r * c⁻¹)
        hcancel

/-- Full upper semicircle Jordan sine-damping integral bound. -/
theorem scalarFourierLaplacePlemelj_upperSineDamping_integral_le
    (c : ℝ) (hc : 0 < c) :
    ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-(c * Real.sin θ)) ≤
      Real.pi * c⁻¹ := by
  calc
    ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-(c * Real.sin θ)) =
        2 * ∫ θ in (0 : ℝ)..(Real.pi / 2),
          Real.exp (-(c * Real.sin θ)) := by
      exact scalarFourierLaplacePlemelj_upperSineDampingIntegral_eq_two_half c
    _ ≤ 2 * ((Real.pi / 2) * c⁻¹) := by
      exact mul_le_mul_of_nonneg_left
        (scalarFourierLaplacePlemelj_upperSineDamping_halfIntegral_le c hc)
        (by exact zero_le_two)
    _ = Real.pi * c⁻¹ := by
      exact scalarFourierLaplacePlemelj_two_mul_upperHalfMajorant_eq c

/-- Jordan's sine estimate for the positive upper-arc damping integral. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_sineDampingIntegral_le
    (T x : ℝ) (hTx : 0 < T * x) :
    ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-(T * x * Real.sin θ)) ≤
      Real.pi * (T * x)⁻¹ := by
  exact
    scalarFourierLaplacePlemelj_upperSineDamping_integral_le
      (T * x) hTx

/-- Multiplication by the positive Jordan prefactor transports the scalar
sine-damping estimate to the full density. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_integral_le_majorant_of_sine
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T)
    (hsine :
      ∫ θ in (0 : ℝ)..Real.pi,
          Real.exp (-(T * x * Real.sin θ)) ≤
        Real.pi * (T * x)⁻¹) :
    ∫ θ in (0 : ℝ)..Real.pi,
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ ≤
      scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T := by
  have hTpos : 0 < T :=
    ha.trans hT
  have hdenpos : 0 < T - a :=
    sub_pos.mpr hT
  have hpref_nonneg : 0 ≤ T / (T - a) :=
    div_nonneg hTpos.le hdenpos.le
  calc
    ∫ θ in (0 : ℝ)..Real.pi,
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ =
        (T / (T - a)) *
          ∫ θ in (0 : ℝ)..Real.pi,
            Real.exp (-(T * x * Real.sin θ)) := by
      exact
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_integral_eq_prefactor_mul
          a T x
    _ ≤ (T / (T - a)) * (Real.pi * (T * x)⁻¹) := by
      exact mul_le_mul_of_nonneg_left hsine hpref_nonneg
    _ = (Real.pi * T / (T - a)) * (T * x)⁻¹ := by
      exact
        scalarFourierLaplacePlemelj_jordanPrefactor_mul_pi_inv_eq_majorant
          a T (T * x)
    _ = scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T := by
      exact rfl

/-- Integral form of Jordan's sine estimate for the positive upper arc. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_integral_le_majorant
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) :
    ∫ θ in (0 : ℝ)..Real.pi,
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ ≤
      scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T := by
  have hTpos : 0 < T :=
    ha.trans hT
  have hxpos : 0 < x :=
    Set.mem_Ioi.mp hx
  have hTx : 0 < T * x :=
    mul_pos hTpos hxpos
  exact
    scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_integral_le_majorant_of_sine
      a ha x hx T hT
      (scalarFourierLaplacePlemelj_positiveUpperArc_sineDampingIntegral_le
        T x hTx)

/-- Interval-integral norm domination for the positive upper arc by the Jordan
density. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_norm_le_jordanDensity_integral
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) :
    ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T‖ ≤
      ∫ θ in (0 : ℝ)..Real.pi,
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ := by
  have hdensity_int :
      IntervalIntegrable
        (fun θ : ℝ =>
          scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ)
        MeasureTheory.volume
        (0 : ℝ)
        Real.pi :=
    scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_intervalIntegrable
      a x T
  have hnorm_abs :
      ‖∫ θ in (0 : ℝ)..Real.pi,
          scalarFourierLaplacePlemelj_positiveUpperArcIntegrand a x T θ‖ ≤
        |∫ θ in (0 : ℝ)..Real.pi,
          scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ| := by
    exact intervalIntegral.norm_integral_le_of_norm_le
      (Eventually.of_forall
        (fun θ _hθ =>
          scalarFourierLaplacePlemelj_positiveUpperArcIntegrand_norm_le_jordanDensity
            a ha x hx T hT θ))
      hdensity_int
  have hnonneg_integral :
      0 ≤ ∫ θ in (0 : ℝ)..Real.pi,
          scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ := by
    exact intervalIntegral.integral_nonneg
      Real.pi_nonneg
      (fun θ _hθ =>
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_nonneg
          a ha x T θ hT)
  calc
    ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T‖ =
        ‖∫ θ in (0 : ℝ)..Real.pi,
          scalarFourierLaplacePlemelj_positiveUpperArcIntegrand a x T θ‖ := by
      exact congrArg norm
        (scalarFourierLaplacePlemelj_positiveUpperArc_eq_integral_integrand
          a x T)
    _ ≤ |∫ θ in (0 : ℝ)..Real.pi,
          scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ| := by
      exact hnorm_abs
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ := by
      exact abs_of_nonneg hnonneg_integral

/-- The positive upper arc is eventually bounded by the Jordan majorant. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_norm_eventually_le_jordanMajorant
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ∀ᶠ T in atTop,
      ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T‖ ≤
        scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T := by
  exact
    (eventually_gt_atTop a).mono
      (fun T hT =>
        (scalarFourierLaplacePlemelj_positiveUpperArc_norm_le_jordanDensity_integral
          a ha x hx T hT).trans
          (scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_integral_le_majorant
            a ha x hx T hT))

/-- Jordan norm estimate for the positive upper semicircle correction. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_norm_tendsto_zero_jordanEstimate
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ => ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T‖)
      atTop
      (𝓝 0) := by
  exact squeeze_zero'
    (Eventually.of_forall
      (fun T : ℝ =>
        norm_nonneg (scalarFourierLaplacePlemelj_positiveUpperArc a x T)))
    (scalarFourierLaplacePlemelj_positiveUpperArc_norm_eventually_le_jordanMajorant
      a ha x hx)
    (scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_tendsto_zero
      a ha x hx)

/-- The upper semicircle correction term vanishes for positive time. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_tendsto_zero
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ => scalarFourierLaplacePlemelj_positiveUpperArc a x T)
      atTop
      (𝓝 0) := by
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (scalarFourierLaplacePlemelj_positiveUpperArc_norm_tendsto_zero_jordanEstimate
      a ha x hx)

/-- Positive-time finite-window contour limit before multiplying by the
compensating `exp (a x)` factor. -/
theorem scalarFourierLaplacePlemelj_positive_window_tendsto_residueValue
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)))
      atTop
      (𝓝
        ((-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ)))) := by
  let W : ℝ → ℂ :=
    fun T : ℝ =>
      ∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))
  let A : ℝ → ℂ :=
    fun T : ℝ => scalarFourierLaplacePlemelj_positiveUpperArc a x T
  let R : ℂ :=
    (-2 * (Real.pi : ℂ)) *
      Complex.exp (-(a : ℂ) * (x : ℂ))
  have hsum_eventual :
      ∀ᶠ T in atTop, W T + A T = R := by
    unfold W
    unfold A
    unfold R
    exact
      scalarFourierLaplacePlemelj_positive_window_add_upperArc_eq_residueValue
        a ha x hx
  have hsum :
      Tendsto (fun T : ℝ => W T + A T) atTop (𝓝 R) :=
    tendsto_nhds_of_eventually_eq hsum_eventual
  have hnegA :
      Tendsto (fun T : ℝ => -A T) atTop (𝓝 0) := by
    have hA :
        Tendsto A atTop (𝓝 0) := by
      unfold A
      exact
        scalarFourierLaplacePlemelj_positiveUpperArc_tendsto_zero
          a ha x hx
    exact Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun T : ℝ => -A T) atTop (𝓝 z))
      neg_zero
      hA.neg
  have hW :
      Tendsto (fun T : ℝ => W T + A T + -A T) atTop (𝓝 (R + 0)) :=
    hsum.add hnegA
  have hpoint :
      (fun T : ℝ => W T + A T + -A T) = W := by
    funext T
    calc
      W T + A T + -A T = W T + (A T + -A T) := by
        exact add_assoc (W T) (A T) (-A T)
      _ = W T + 0 := by
        exact congrArg (fun z : ℂ => W T + z) (add_neg_cancel (A T))
      _ = W T := by
        exact add_zero (W T)
  have htarget : R + 0 = R :=
    add_zero R
  exact Eq.subst
    (motive := fun u : ℝ → ℂ => Tendsto u atTop (𝓝 R))
    hpoint
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun T : ℝ => W T + A T + -A T) atTop (𝓝 z))
      htarget
      hW)

/-- Multiplying a convergent positive-time residue window by `exp (a x)`. -/
theorem scalarFourierLaplacePlemelj_positive_window_tendsto_residueValue_mul_exp
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        (∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ))) *
          Complex.exp ((a : ℂ) * (x : ℂ)))
      atTop
      (𝓝
        (((-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ))) *
          Complex.exp ((a : ℂ) * (x : ℂ)))) := by
  exact
    (scalarFourierLaplacePlemelj_positive_window_tendsto_residueValue
      a ha x hx).mul
      (tendsto_const_nhds :
        Tendsto
          (fun _T : ℝ => Complex.exp ((a : ℂ) * (x : ℂ)))
          atTop
          (𝓝 (Complex.exp ((a : ℂ) * (x : ℂ)))))

/-- Pointwise algebra moving the compensating exponential inside the
positive-time finite window. -/
theorem scalarFourierLaplacePlemelj_positive_window_mul_exp_eq_window_with_exp
    (a : ℝ) (x T : ℝ) :
    (∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))) *
      Complex.exp ((a : ℂ) * (x : ℂ)) =
    ∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp ((a : ℂ) * (x : ℂ)) := by
  exact (intervalIntegral.integral_mul_const
    (f := fun t : ℝ =>
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)))
    (c := Complex.exp ((a : ℂ) * (x : ℂ)))
    (-T) T).symm

/-- Positive-time residue limit after moving the compensating exponential
inside the symmetric finite window. -/
theorem scalarFourierLaplacePlemelj_positive_window_tendsto_residueValue_with_exp
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)))
      atTop
      (𝓝
        (((-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ))) *
          Complex.exp ((a : ℂ) * (x : ℂ)))) := by
  exact Eq.subst
    (motive := fun u : ℝ → ℂ =>
      Tendsto u atTop
        (𝓝
          (((-2 * (Real.pi : ℂ)) *
            Complex.exp (-(a : ℂ) * (x : ℂ))) *
            Complex.exp ((a : ℂ) * (x : ℂ)))))
    (funext
      (fun T : ℝ =>
        scalarFourierLaplacePlemelj_positive_window_mul_exp_eq_window_with_exp
          a x T))
    (scalarFourierLaplacePlemelj_positive_window_tendsto_residueValue_mul_exp
      a ha x hx)

/-- Positive-time scalar Plemelj window after the Laplace denominator has been
evaluated by the one-sided exponential transform. -/
theorem scalarFourierLaplacePlemelj_positive_window_tendsto_laplaceJump
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)))
      atTop
      (𝓝
        ((-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ)))) := by
  exact
    scalarFourierLaplacePlemelj_positive_window_tendsto_residueValue_with_exp
      a ha x hx

/-- The positive-time Laplace jump collapses after multiplying by the compensating
`exp (a x)` factor. -/
theorem scalarFourierLaplacePlemelj_positive_laplaceJump_mul_eq_constant
    (a : ℝ) (x : ℝ) :
    ((-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) *
        Complex.exp ((a : ℂ) * (x : ℂ))) =
      (-2 * (Real.pi : ℂ)) := by
  have hsum :
      (-(a : ℂ) * (x : ℂ)) + ((a : ℂ) * (x : ℂ)) = 0 :=
    neg_add_cancel ((a : ℂ) * (x : ℂ))
  have hexp :
      Complex.exp (-(a : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ)) =
        1 := by
    calc
      Complex.exp (-(a : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ))
          = Complex.exp
              ((-(a : ℂ) * (x : ℂ)) + ((a : ℂ) * (x : ℂ))) := by
            exact (Complex.exp_add (-(a : ℂ) * (x : ℂ))
              ((a : ℂ) * (x : ℂ))).symm
      _ = Complex.exp 0 := by
            exact congrArg Complex.exp hsum
      _ = 1 := by
            exact Complex.exp_zero
  calc
    ((-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) *
        Complex.exp ((a : ℂ) * (x : ℂ)))
        =
        (-2 * (Real.pi : ℂ)) *
          (Complex.exp (-(a : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ))) := by
          exact mul_assoc (-2 * (Real.pi : ℂ))
            (Complex.exp (-(a : ℂ) * (x : ℂ)))
            (Complex.exp ((a : ℂ) * (x : ℂ)))
    _ = (-2 * (Real.pi : ℂ)) * 1 := by
          exact congrArg
            (fun z : ℂ => (-2 * (Real.pi : ℂ)) * z)
            hexp
    _ = (-2 * (Real.pi : ℂ)) := by
          exact mul_one (-2 * (Real.pi : ℂ))

/-- Positive-time normalized Fourier-Laplace Plemelj value. -/
theorem scalarFourierLaplacePlemelj_pointwise_positive
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)))
      atTop
      (𝓝 (-2 * (Real.pi : ℂ))) := by
  exact Eq.subst
    (motive := fun y : ℂ =>
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / ((a : ℂ) + t * Complex.I)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp ((a : ℂ) * (x : ℂ)))
        atTop
        (𝓝 y))
    (scalarFourierLaplacePlemelj_positive_laplaceJump_mul_eq_constant a x)
    (scalarFourierLaplacePlemelj_positive_window_tendsto_laplaceJump
      a ha x hx)

/-- Lower semicircle correction term for the negative-time scalar
Fourier-Laplace contour.  The real segment runs from `-T` to `T`, and this arc
returns from `T` to `-T` through the lower half-plane. -/

end FixedLineCauchyProjection

end
end Boundary
