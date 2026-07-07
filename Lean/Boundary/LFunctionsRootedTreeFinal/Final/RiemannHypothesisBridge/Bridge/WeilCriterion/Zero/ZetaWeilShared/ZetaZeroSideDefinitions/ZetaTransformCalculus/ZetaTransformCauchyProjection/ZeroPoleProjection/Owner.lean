import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.CompactSupportProjection.Owner

/-!
# Right zero-pole Cauchy projection

This file owns the fixed-line Cauchy projection needed by the isolated
`s = 0` correction pole.  It is a specialization of the generic fixed-right
Fourier-Cauchy projection with line parameter `c + 1` and time-side kernel
`φ(x) exp(-x / 2)`.
-/

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

/-- The time-side kernel for the right zero-pole projection. -/
noncomputable def zetaLaplaceTransform_rightZeroPoleProjectionKernel
    (φ : LFunctions.ZetaTestFunction) : ℝ → ℂ :=
  fun x : ℝ =>
    φ x *
      Complex.exp (-(1 / 2 : ℂ) * (x : ℂ))

/-- The right zero-pole Cauchy/Laplace projection value. -/
noncomputable def zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
    (φ : LFunctions.ZetaTestFunction) (_c : ℝ) : ℂ :=
  ∫ x in Set.Ici (0 : ℝ),
    (-2 * (Real.pi : ℂ)) *
      zetaLaplaceTransform_rightZeroPoleProjectionKernel φ x

/-- Continuity of the right zero-pole projection kernel. -/
theorem zetaLaplaceTransform_rightZeroPoleProjectionKernel_continuous
    (φ : LFunctions.ZetaTestFunction) :
    Continuous (zetaLaplaceTransform_rightZeroPoleProjectionKernel φ) :=
  φ.continuous.mul
    (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))

/-- Compact support of the right zero-pole projection kernel. -/
theorem zetaLaplaceTransform_rightZeroPoleProjectionKernel_hasCompactSupport
    (φ : LFunctions.ZetaTestFunction) :
    HasCompactSupport (zetaLaplaceTransform_rightZeroPoleProjectionKernel φ) :=
  φ.hasCompactSupport.mul_right

/-- Smoothness of the right zero-pole projection kernel. -/
theorem zetaLaplaceTransform_rightZeroPoleProjectionKernel_contDiff_admissible
    (f : LFunctions.ZetaAdmissibleFunction) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (zetaLaplaceTransform_rightZeroPoleProjectionKernel f.toZetaTestFunction') := by
  have hexp :
      ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ => Complex.exp (-(1 / 2 : ℂ) * (x : ℂ))) := by
    have harg :
        ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ => -(1 / 2 : ℂ) * (x : ℂ)) := by
      exact contDiff_const.mul Complex.ofRealCLM.contDiff
    exact Complex.contDiff_exp.comp harg
  exact f.smooth.mul hexp

/-- Real affine identity for the zero-pole vertical slice. -/
theorem zetaLaplaceTransform_rightZeroPoleProjectionKernel_verticalSlice_realAffine_eq
    (c : ℝ) :
    c - 1 / 2 = -(1 / 2) + c := by
  calc
    c - 1 / 2 = c + -(1 / 2 : ℝ) := by
      exact sub_eq_add_neg c (1 / 2)
    _ = -(1 / 2 : ℝ) + c := by
      exact add_comm c (-(1 / 2 : ℝ))

/-- Complex affine identity for the zero-pole vertical slice. -/
theorem zetaLaplaceTransform_rightZeroPoleProjectionKernel_verticalSlice_realCoefficient_eq
    (c : ℝ) :
    (c : ℂ) - 1 / 2 = -(1 / 2 : ℂ) + (c : ℂ) := by
  calc
    (c : ℂ) - 1 / 2 = (c : ℂ) + -(1 / 2 : ℂ) := by
      exact sub_eq_add_neg (c : ℂ) (1 / 2 : ℂ)
    _ = -(1 / 2 : ℂ) + (c : ℂ) := by
      exact add_comm (c : ℂ) (-(1 / 2 : ℂ))

/-- Coefficient identity before multiplying the zero-pole vertical slice by
the time variable. -/
theorem zetaLaplaceTransform_rightZeroPoleProjectionKernel_verticalSlice_coefficient_eq
    (c t : ℝ) :
    ((c : ℂ) - 1 / 2) + t * Complex.I =
      -(1 / 2 : ℂ) + Complex.I * (t : ℂ) + (c : ℂ) := by
  calc
    ((c : ℂ) - 1 / 2) + t * Complex.I =
        (-(1 / 2 : ℂ) + (c : ℂ)) + t * Complex.I := by
      exact congrArg
        (fun z : ℂ => z + t * Complex.I)
        (zetaLaplaceTransform_rightZeroPoleProjectionKernel_verticalSlice_realCoefficient_eq
          c)
    _ = (-(1 / 2 : ℂ) + (c : ℂ)) + Complex.I * (t : ℂ) := by
      exact congrArg
        (fun z : ℂ => (-(1 / 2 : ℂ) + (c : ℂ)) + z)
        (mul_comm (t : ℂ) Complex.I)
    _ = -(1 / 2 : ℂ) + ((c : ℂ) + Complex.I * (t : ℂ)) := by
      exact add_assoc (-(1 / 2 : ℂ)) (c : ℂ) (Complex.I * (t : ℂ))
    _ = -(1 / 2 : ℂ) + (Complex.I * (t : ℂ) + (c : ℂ)) := by
      exact congrArg
        (fun z : ℂ => -(1 / 2 : ℂ) + z)
        (add_comm (c : ℂ) (Complex.I * (t : ℂ)))
    _ = -(1 / 2 : ℂ) + Complex.I * (t : ℂ) + (c : ℂ) := by
      exact (add_assoc (-(1 / 2 : ℂ)) (Complex.I * (t : ℂ)) (c : ℂ)).symm

/-- Exponent-coordinate identity behind the right zero-pole vertical slice. -/
theorem zetaLaplaceTransform_rightZeroPoleProjectionKernel_verticalSlice_exponent_eq
    (c t x : ℝ) :
    ((((c : ℂ) - 1 / 2) + t * Complex.I) * (x : ℂ)) =
      -(1 / 2 : ℂ) * (x : ℂ) +
        Complex.I * (t : ℂ) * (x : ℂ) +
          (c : ℂ) * (x : ℂ) := by
  calc
    ((((c : ℂ) - 1 / 2) + t * Complex.I) * (x : ℂ)) =
        ((-(1 / 2 : ℂ) + Complex.I * (t : ℂ) + (c : ℂ)) *
          (x : ℂ)) := by
      exact congrArg
        (fun z : ℂ => z * (x : ℂ))
        (zetaLaplaceTransform_rightZeroPoleProjectionKernel_verticalSlice_coefficient_eq
          c t)
    _ =
        (-(1 / 2 : ℂ) + Complex.I * (t : ℂ)) * (x : ℂ) +
          (c : ℂ) * (x : ℂ) :=
      add_mul
        (-(1 / 2 : ℂ) + Complex.I * (t : ℂ))
        (c : ℂ)
        (x : ℂ)
    _ =
        (-(1 / 2 : ℂ) * (x : ℂ) +
            Complex.I * (t : ℂ) * (x : ℂ)) +
          (c : ℂ) * (x : ℂ) := by
      exact congrArg
        (fun z : ℂ => z + (c : ℂ) * (x : ℂ))
        (add_mul (-(1 / 2 : ℂ)) (Complex.I * (t : ℂ)) (x : ℂ))
    _ =
        -(1 / 2 : ℂ) * (x : ℂ) +
          Complex.I * (t : ℂ) * (x : ℂ) +
            (c : ℂ) * (x : ℂ) := by
      exact rfl

/-- Pointwise exponential algebra for the right zero-pole vertical slice. -/
theorem zetaLaplaceTransform_rightZeroPoleProjectionKernel_verticalSlice_integrand_eq
    (φ : LFunctions.ZetaTestFunction) (c t x : ℝ) :
    φ x *
        Complex.exp
          ((((c : ℂ) - 1 / 2) + t * Complex.I) * (x : ℂ)) =
      zetaLaplaceTransform_rightZeroPoleProjectionKernel φ x *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp ((c : ℂ) * (x : ℂ)) := by
  unfold zetaLaplaceTransform_rightZeroPoleProjectionKernel
  calc
    φ x *
        Complex.exp
          ((((c : ℂ) - 1 / 2) + t * Complex.I) * (x : ℂ))
        =
        φ x *
          Complex.exp
            (-(1 / 2 : ℂ) * (x : ℂ) +
              Complex.I * (t : ℂ) * (x : ℂ) +
                (c : ℂ) * (x : ℂ)) := by
      exact congrArg
        (fun z : ℂ => φ x * Complex.exp z)
        (zetaLaplaceTransform_rightZeroPoleProjectionKernel_verticalSlice_exponent_eq
          c t x)
    _ =
        φ x *
          (Complex.exp
            (-(1 / 2 : ℂ) * (x : ℂ) +
              Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((c : ℂ) * (x : ℂ))) := by
      exact congrArg
        (fun z : ℂ => φ x * z)
        (Complex.exp_add
          (-(1 / 2 : ℂ) * (x : ℂ) +
            Complex.I * (t : ℂ) * (x : ℂ))
          ((c : ℂ) * (x : ℂ)))
    _ =
        φ x *
          ((Complex.exp (-(1 / 2 : ℂ) * (x : ℂ)) *
              Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) *
            Complex.exp ((c : ℂ) * (x : ℂ))) := by
      exact congrArg
        (fun z : ℂ =>
          φ x * (z * Complex.exp ((c : ℂ) * (x : ℂ))))
        (Complex.exp_add
          (-(1 / 2 : ℂ) * (x : ℂ))
          (Complex.I * (t : ℂ) * (x : ℂ)))
    _ =
        (φ x * Complex.exp (-(1 / 2 : ℂ) * (x : ℂ))) *
            Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp ((c : ℂ) * (x : ℂ)) := by
      exact
        calc
          φ x *
              ((Complex.exp (-(1 / 2 : ℂ) * (x : ℂ)) *
                  Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) *
                Complex.exp ((c : ℂ) * (x : ℂ)))
              =
              (φ x *
                (Complex.exp (-(1 / 2 : ℂ) * (x : ℂ)) *
                  Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))) *
                Complex.exp ((c : ℂ) * (x : ℂ)) := by
            exact (mul_assoc (φ x)
              (Complex.exp (-(1 / 2 : ℂ) * (x : ℂ)) *
                Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))
              (Complex.exp ((c : ℂ) * (x : ℂ)))).symm
          _ =
              ((φ x * Complex.exp (-(1 / 2 : ℂ) * (x : ℂ))) *
                  Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) *
                Complex.exp ((c : ℂ) * (x : ℂ)) := by
            exact congrArg
              (fun z : ℂ => z * Complex.exp ((c : ℂ) * (x : ℂ)))
              ((mul_assoc (φ x)
                (Complex.exp (-(1 / 2 : ℂ) * (x : ℂ)))
                (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))).symm)

/-- The zero-pole right vertical Laplace slice is the Fourier transform of the
zero-pole projection kernel. -/
theorem zetaLaplaceTransform_rightZeroPoleProjectionKernel_verticalSlice_eq_fourier
    (φ : LFunctions.ZetaTestFunction) (c t : ℝ) :
    zetaLaplaceTransform φ (((c : ℂ) - 1 / 2) + t * Complex.I) =
      ∫ x : ℝ,
        zetaLaplaceTransform_rightZeroPoleProjectionKernel φ x *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp ((c : ℂ) * (x : ℂ)) := by
  unfold zetaLaplaceTransform
  exact
    integral_congr_ae
      (Eventually.of_forall
        (fun x : ℝ =>
          zetaLaplaceTransform_rightZeroPoleProjectionKernel_verticalSlice_integrand_eq
            φ c t x))

/-- The shifted fixed-line parameter `c + 1` is genuinely right of `1`. -/
theorem zetaLaplaceTransform_rightZeroPole_shiftedLine_gt_one
    (c : ℝ) (hc : 0 < c) :
    1 < c + 1 := by
  calc
    1 = 0 + 1 := by
      exact (zero_add (1 : ℝ)).symm
    _ < c + 1 := by
      exact add_lt_add_right hc 1

/-- Full-line Cauchy inversion for the right zero-pole projection kernel. -/
theorem zetaLaplaceTransform_rightZeroPoleProjectionKernel_fullLineCauchyValue
    (f : LFunctions.ZetaAdmissibleFunction) (c : ℝ) (hc : 0 < c) :
    (∫ t : ℝ,
        (-1 / ((c : ℂ) + (t : ℂ) * Complex.I)) *
          zetaLaplaceTransform f.toZetaTestFunction'
            (((c : ℂ) - 1 / 2) + t * Complex.I)) =
      zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
        f.toZetaTestFunction' c := by
  let cp : ℝ := c + 1
  have hcp : 1 < cp :=
    zetaLaplaceTransform_rightZeroPole_shiftedLine_gt_one c hc
  have hden :
      ∀ t : ℝ,
        (((cp : ℂ) + (t : ℂ) * Complex.I) - 1) =
          (c : ℂ) + (t : ℂ) * Complex.I := by
    intro t
    calc
      (((cp : ℂ) + (t : ℂ) * Complex.I) - 1) =
          ((cp : ℂ) - 1) + (t : ℂ) * Complex.I := by
        exact add_sub_right_comm (cp : ℂ) ((t : ℂ) * Complex.I) (1 : ℂ)
      _ = ((c + 1 : ℝ) : ℂ) - 1 + (t : ℂ) * Complex.I := by
        exact rfl
      _ = ((c : ℂ) + (1 : ℂ)) - 1 + (t : ℂ) * Complex.I := by
        exact congrArg
          (fun z : ℂ => z - 1 + (t : ℂ) * Complex.I)
          (Complex.ofReal_add c 1)
      _ = (c : ℂ) + (t : ℂ) * Complex.I := by
        exact congrArg
          (fun z : ℂ => z + (t : ℂ) * Complex.I)
          (add_sub_cancel_right (c : ℂ) (1 : ℂ))
  have hgeneric :
      (∫ t : ℝ,
          (-1 / (((cp : ℂ) + (t : ℂ) * Complex.I) - 1)) *
            (∫ x : ℝ,
              zetaLaplaceTransform_rightZeroPoleProjectionKernel
                  f.toZetaTestFunction' x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((cp - 1 : ℝ) : ℂ) * (x : ℂ)))) =
        ∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) *
            zetaLaplaceTransform_rightZeroPoleProjectionKernel
              f.toZetaTestFunction' x :=
    fixedRightLine_fourierCauchy_fullLine_oneSidedProjection
      (zetaLaplaceTransform_rightZeroPoleProjectionKernel f.toZetaTestFunction')
      (zetaLaplaceTransform_rightZeroPoleProjectionKernel_continuous
        f.toZetaTestFunction')
      (zetaLaplaceTransform_rightZeroPoleProjectionKernel_hasCompactSupport
        f.toZetaTestFunction')
      (zetaLaplaceTransform_rightZeroPoleProjectionKernel_contDiff_admissible f)
      cp hcp
  have hleft :
      (∫ t : ℝ,
          (-1 / ((c : ℂ) + (t : ℂ) * Complex.I)) *
            zetaLaplaceTransform f.toZetaTestFunction'
              (((c : ℂ) - 1 / 2) + t * Complex.I)) =
        (∫ t : ℝ,
          (-1 / (((cp : ℂ) + (t : ℂ) * Complex.I) - 1)) *
            (∫ x : ℝ,
              zetaLaplaceTransform_rightZeroPoleProjectionKernel
                  f.toZetaTestFunction' x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((cp - 1 : ℝ) : ℂ) * (x : ℂ)))) := by
    exact
      integral_congr_ae
        (Eventually.of_forall
          (fun t : ℝ =>
            calc
              (-1 / ((c : ℂ) + (t : ℂ) * Complex.I)) *
                  zetaLaplaceTransform f.toZetaTestFunction'
                    (((c : ℂ) - 1 / 2) + t * Complex.I)
                  =
                  (-1 / (((cp : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                    zetaLaplaceTransform f.toZetaTestFunction'
                      (((c : ℂ) - 1 / 2) + t * Complex.I) := by
                exact congrArg
                  (fun z : ℂ =>
                    (-1 / z) *
                      zetaLaplaceTransform f.toZetaTestFunction'
                        (((c : ℂ) - 1 / 2) + t * Complex.I))
                  (hden t).symm
              _ =
                  (-1 / (((cp : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                    (∫ x : ℝ,
                      zetaLaplaceTransform_rightZeroPoleProjectionKernel
                          f.toZetaTestFunction' x *
                        Complex.exp
                          (Complex.I * (t : ℂ) * (x : ℂ)) *
                        Complex.exp (((cp - 1 : ℝ) : ℂ) * (x : ℂ))) := by
                have hcp_sub :
                    ((cp - 1 : ℝ) : ℂ) = (c : ℂ) := by
                  unfold cp
                  calc
                    (((c + 1) - 1 : ℝ) : ℂ) = ((c + (1 - 1) : ℝ) : ℂ) := by
                      exact congrArg (fun r : ℝ => (r : ℂ))
                        (add_sub_assoc c 1 1)
                    _ = ((c + 0 : ℝ) : ℂ) := by
                      exact congrArg
                        (fun r : ℝ => ((c + r : ℝ) : ℂ))
                        (sub_self (1 : ℝ))
                    _ = (c : ℂ) := by
                      exact congrArg (fun r : ℝ => (r : ℂ)) (add_zero c)
                exact congrArg
                  (fun z : ℂ =>
                    (-1 / (((cp : ℂ) + (t : ℂ) * Complex.I) - 1)) * z)
                  ((zetaLaplaceTransform_rightZeroPoleProjectionKernel_verticalSlice_eq_fourier
                    f.toZetaTestFunction' c t).trans
                    (congrArg
                      (fun a : ℂ =>
                        ∫ x : ℝ,
                          zetaLaplaceTransform_rightZeroPoleProjectionKernel
                              f.toZetaTestFunction' x *
                            Complex.exp
                              (Complex.I * (t : ℂ) * (x : ℂ)) *
                            Complex.exp (a * (x : ℂ)))
                      hcp_sub.symm))))
  calc
    (∫ t : ℝ,
        (-1 / ((c : ℂ) + (t : ℂ) * Complex.I)) *
          zetaLaplaceTransform f.toZetaTestFunction'
            (((c : ℂ) - 1 / 2) + t * Complex.I)) =
        (∫ t : ℝ,
          (-1 / (((cp : ℂ) + (t : ℂ) * Complex.I) - 1)) *
            (∫ x : ℝ,
              zetaLaplaceTransform_rightZeroPoleProjectionKernel
                  f.toZetaTestFunction' x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((cp - 1 : ℝ) : ℂ) * (x : ℂ)))) := hleft
    _ =
        ∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) *
            zetaLaplaceTransform_rightZeroPoleProjectionKernel
              f.toZetaTestFunction' x := hgeneric
    _ =
        zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' c := by
      exact rfl

end FixedLineCauchyProjection

end
end Boundary
