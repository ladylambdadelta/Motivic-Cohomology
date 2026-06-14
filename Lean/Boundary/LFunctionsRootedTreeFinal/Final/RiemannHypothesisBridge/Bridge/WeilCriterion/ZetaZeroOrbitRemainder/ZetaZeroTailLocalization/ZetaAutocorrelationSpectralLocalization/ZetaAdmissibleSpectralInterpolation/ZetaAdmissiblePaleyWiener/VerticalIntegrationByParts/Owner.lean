import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.HorizontalTwist.Owner

/-!
# Paley-Wiener vertical-line decomposition

This file owns the first vertical integration-by-parts layer: the vertical
oscillation, vertical-line kernel decomposition, and transport of the Laplace
transform to the vertical-line kernel integral. It is copy-first extracted from
the current Paley-Wiener owner file and is not imported by that parent yet, so
declaration names intentionally match the existing owner surface.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff

namespace ZetaAdmissibleFunction

/-- The pure vertical oscillatory kernel on the line `re z = x`. -/
noncomputable def zetaPaleyWienerVerticalOscillation
    (y t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (y : ℂ) * (t : ℂ))

/-- The imaginary vertical phase can be written as a real scalar times `I`. -/
theorem zetaPaleyWienerVerticalPhase_eq_real_mul_I
    (y t : ℝ) :
    Complex.I * (y : ℂ) * (t : ℂ) = ((y * t : ℝ) : ℂ) * Complex.I := by
  calc
    Complex.I * (y : ℂ) * (t : ℂ)
        = ((y : ℂ) * (t : ℂ)) * Complex.I := by
          exact Eq.trans
            (mul_assoc Complex.I (y : ℂ) (t : ℂ))
            (Eq.trans
              (congrArg (fun v : ℂ => Complex.I * v) (mul_comm (y : ℂ) (t : ℂ)))
              (Eq.trans
                (mul_comm Complex.I ((t : ℂ) * (y : ℂ)))
                (congrArg (fun v : ℂ => v * Complex.I) (mul_comm (t : ℂ) (y : ℂ)))))
    _ = ((y * t : ℝ) : ℂ) * Complex.I := by
          exact congrArg
            (fun v : ℂ => v * Complex.I)
            (Complex.ofReal_mul y t).symm

/-- The vertical phase has zero real part. -/
theorem zetaPaleyWienerVerticalPhase_re_zero
    (y t : ℝ) :
    (Complex.I * (y : ℂ) * (t : ℂ)).re = 0 := by
  exact Eq.trans
    (congrArg Complex.re (zetaPaleyWienerVerticalPhase_eq_real_mul_I y t))
    (paley_ofReal_mul_I_re_zero (y * t))

/-- The vertical oscillatory kernel has norm one. -/
theorem zetaPaleyWienerVerticalOscillation_norm_eq_one
    (y t : ℝ) :
    ‖zetaPaleyWienerVerticalOscillation y t‖ = 1 := by
  unfold zetaPaleyWienerVerticalOscillation
  exact Eq.trans
    (complexExp_norm_eq_realExp_re (Complex.I * (y : ℂ) * (t : ℂ)))
    (Eq.trans
      (congrArg Real.exp (zetaPaleyWienerVerticalPhase_re_zero y t))
      Real.exp_zero)

/-- The vertical oscillatory kernel has norm bounded by one. -/
theorem zetaPaleyWienerVerticalOscillation_norm_le_one
    (y t : ℝ) :
    ‖zetaPaleyWienerVerticalOscillation y t‖ ≤ 1 :=
  le_of_eq (zetaPaleyWienerVerticalOscillation_norm_eq_one y t)

/-- Multiplying by the vertical oscillation does not increase a pointwise norm. -/
theorem norm_mul_zetaPaleyWienerVerticalOscillation_le
    (w : ℂ) (y t : ℝ) :
    ‖w * zetaPaleyWienerVerticalOscillation y t‖ ≤ ‖w‖ := by
  have hmul :
      ‖w * zetaPaleyWienerVerticalOscillation y t‖ =
        ‖w‖ * ‖zetaPaleyWienerVerticalOscillation y t‖ :=
    norm_mul w (zetaPaleyWienerVerticalOscillation y t)
  have hosc :
      ‖zetaPaleyWienerVerticalOscillation y t‖ = 1 :=
    zetaPaleyWienerVerticalOscillation_norm_eq_one y t
  exact le_of_eq
    (Eq.trans hmul
      (Eq.trans
        (congrArg (fun v : ℝ => ‖w‖ * v) hosc)
        (mul_one ‖w‖)))

/-- The vertical-line kernel after splitting the horizontal exponential from the oscillatory
factor. -/
noncomputable def zetaPaleyWienerVerticalLineKernel
    (f : ZetaAdmissibleFunction) (x y t : ℝ) : ℂ :=
  zetaPaleyWienerHorizontalTwist f x t *
    zetaPaleyWienerVerticalOscillation y t

/-- Complex multiplication by a real variable splits into horizontal and vertical parts. -/
theorem complex_mul_real_verticalLine_decomposition_re
    (z : ℂ) (t : ℝ) :
    (z * (t : ℂ)).re =
      ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)).re := by
  exact Eq.trans
    (complex_mul_real_re z t)
    (complex_verticalLine_decomposition_rhs_re z t).symm

/-- Imaginary coordinate of the vertical-line complex decomposition. -/
theorem complex_mul_real_verticalLine_decomposition_im
    (z : ℂ) (t : ℝ) :
    (z * (t : ℂ)).im =
      ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)).im := by
  exact Eq.trans
    (complex_mul_real_im z t)
    (complex_verticalLine_decomposition_rhs_im z t).symm

/-- Complex multiplication by a real variable splits into horizontal and vertical parts. -/
theorem complex_mul_real_verticalLine_decomposition
    (z : ℂ) (t : ℝ) :
    z * (t : ℂ) =
      (z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ) := by
  exact Complex.ext
    (complex_mul_real_verticalLine_decomposition_re z t)
    (complex_mul_real_verticalLine_decomposition_im z t)

/-- The exponential on a vertical line splits into horizontal and oscillatory factors. -/
theorem complex_exp_verticalLine_decomposition_from_add
    (z : ℂ) (t : ℝ) :
    Complex.exp ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)) =
      (Real.exp (z.re * t) : ℂ) *
        Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)) := by
  have hadd :
      Complex.exp ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)) =
        Complex.exp (z.re * t : ℂ) *
          Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)) :=
    Complex.exp_add (z.re * t : ℂ) (Complex.I * (z.im : ℂ) * (t : ℂ))
  have hreal :
      Complex.exp (z.re * t : ℂ) = (Real.exp (z.re * t) : ℂ) :=
    Complex.ofReal_exp (z.re * t)
  exact Eq.trans hadd
    (congrArg
      (fun v : ℂ => v * Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)))
      hreal)

/-- The exponential on a vertical line splits into horizontal and oscillatory factors. -/
theorem complex_exp_verticalLine_decomposition
    (z : ℂ) (t : ℝ) :
    Complex.exp (z * (t : ℂ)) =
      (Real.exp (z.re * t) : ℂ) *
        Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)) := by
  have hdecomp :
      z * (t : ℂ) =
        (z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ) :=
    complex_mul_real_verticalLine_decomposition z t
  exact Eq.trans
    (congrArg Complex.exp hdecomp)
    (complex_exp_verticalLine_decomposition_from_add z t)

/-- The Laplace kernel equals the explicit vertical-line product pointwise. -/
theorem zetaPaleyWienerLaplaceKernel_eq_verticalLineKernel_pointwise
    (f : ZetaAdmissibleFunction) (z : ℂ) (t : ℝ) :
    f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ)) =
      (f.toZetaTestFunction' t * (Real.exp (z.re * t) : ℂ)) *
        Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)) := by
  have hexp :
      Complex.exp (z * (t : ℂ)) =
        (Real.exp (z.re * t) : ℂ) *
          Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)) :=
    complex_exp_verticalLine_decomposition z t
  calc
    f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ))
        = f.toZetaTestFunction' t *
          ((Real.exp (z.re * t) : ℂ) *
            Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ))) := by
          exact congrArg (fun v : ℂ => f.toZetaTestFunction' t * v) hexp
    _ = (f.toZetaTestFunction' t * (Real.exp (z.re * t) : ℂ)) *
          Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)) := by
          exact (mul_assoc
            (f.toZetaTestFunction' t)
            (Real.exp (z.re * t) : ℂ)
            (Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)))).symm

/-- The original Laplace kernel factors into horizontal twist times vertical oscillation on
the vertical line through `z.re`. -/
theorem zetaPaleyWienerLaplaceKernel_eq_verticalLineKernel
    (f : ZetaAdmissibleFunction) (z : ℂ) (t : ℝ) :
    zetaPaleyWienerLaplaceKernel f z t =
      zetaPaleyWienerVerticalLineKernel f z.re z.im t := by
  unfold zetaPaleyWienerLaplaceKernel
  unfold zetaPaleyWienerVerticalLineKernel
  unfold zetaPaleyWienerHorizontalTwist
  unfold zetaPaleyWienerVerticalOscillation
  exact zetaPaleyWienerLaplaceKernel_eq_verticalLineKernel_pointwise f z t

/-- Pointwise equality of integrands transports their real-line integrals. -/
theorem complex_integral_congr_of_pointwise_eq
    (u v : ℝ → ℂ) (h : ∀ t : ℝ, u t = v t) :
    (∫ t : ℝ, u t) = ∫ t : ℝ, v t := by
  exact integral_congr_ae (Filter.Eventually.of_forall h)

/-- The zeta Laplace transform is the integral of the vertical-line kernel. -/
theorem zetaLaplaceTransform_eq_verticalLineKernelIntegral
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    Boundary.zetaLaplaceTransform f.toZetaTestFunction' z =
      ∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f z.re z.im t := by
  have hkernel :
      (∫ t : ℝ, zetaPaleyWienerLaplaceKernel f z t) =
        ∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f z.re z.im t :=
    complex_integral_congr_of_pointwise_eq
      (zetaPaleyWienerLaplaceKernel f z)
      (zetaPaleyWienerVerticalLineKernel f z.re z.im)
      (fun t : ℝ => zetaPaleyWienerLaplaceKernel_eq_verticalLineKernel f z t)
  exact (zetaPaleyWienerLaplaceKernel_integral_eq_transform f z).symm.trans hkernel

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
