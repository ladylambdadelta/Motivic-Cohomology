import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.VerticalIntegrationByParts.Owner

/-!
# Paley-Wiener vertical derivative sources

This file owns the derivative source used by one vertical-line integration by
parts, the iterated horizontal-twist derivative family, and support/vanishing
lemmas for those sources. It is copy-first extracted from the current
Paley-Wiener owner file and is not imported by that parent yet, so declaration
names intentionally match the existing owner surface.
-/

namespace Boundary
namespace LFunctions

noncomputable section

  open scoped ContDiff
  open MeasureTheory

  namespace ZetaAdmissibleFunction

/-- The derivative source used by vertical-line integration by parts after the horizontal
factor has been absorbed into the source. -/
noncomputable def zetaPaleyWienerVerticalLineIBPDerivative
    (f : ZetaAdmissibleFunction) (x t : ℝ) : ℂ :=
  deriv (fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u) t

/-- The derivative of the horizontal twist is represented by its named derivative source. -/
theorem hasDerivAt_zetaPaleyWienerHorizontalTwist
    (f : ZetaAdmissibleFunction) (x t : ℝ) :
    HasDerivAt
      (fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u)
      (zetaPaleyWienerVerticalLineIBPDerivative f x t)
      t := by
    exact
      ((zetaPaleyWienerHorizontalTwist_contDiff f x).differentiable
        (show 1 ≤ (∞ : WithTop ℕ∞) from
          WithTop.coe_le_coe.2 (OrderTop.le_top (1 : ℕ∞))) t).hasDerivAt

/-- The derivative source of the horizontal twist is continuous. -/
theorem zetaPaleyWienerVerticalLineIBPDerivative_continuous
    (f : ZetaAdmissibleFunction) (x : ℝ) :
      Continuous (fun t : ℝ => zetaPaleyWienerVerticalLineIBPDerivative f x t) := by
    unfold zetaPaleyWienerVerticalLineIBPDerivative
    exact (zetaPaleyWienerHorizontalTwist_contDiff f x).continuous_deriv
      (show 1 ≤ (∞ : WithTop (ℕ∞)) from
        WithTop.coe_le_coe.2 (OrderTop.le_top (1 : ℕ∞)))

/-- The derivative source of the horizontal twist has compact support. -/
theorem zetaPaleyWienerVerticalLineIBPDerivative_hasCompactSupport
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    HasCompactSupport (fun t : ℝ => zetaPaleyWienerVerticalLineIBPDerivative f x t) := by
  unfold zetaPaleyWienerVerticalLineIBPDerivative
  exact (zetaPaleyWienerHorizontalTwist_hasCompactSupport f x).deriv

/-- The vertical-line kernel is integrable. -/
theorem zetaPaleyWienerVerticalLineKernel_integrable
    (f : ZetaAdmissibleFunction) (x y : ℝ) :
    Integrable (fun t : ℝ => zetaPaleyWienerVerticalLineKernel f x y t) := by
  have hcontinuous :
      Continuous (fun t : ℝ => zetaPaleyWienerVerticalLineKernel f x y t) := by
    unfold zetaPaleyWienerVerticalLineKernel
    exact (zetaPaleyWienerHorizontalTwist_continuous f x).mul
      (Complex.continuous_exp.comp
        ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal))
  have hsupport :
      HasCompactSupport (fun t : ℝ => zetaPaleyWienerVerticalLineKernel f x y t) := by
    unfold zetaPaleyWienerVerticalLineKernel
    exact (zetaPaleyWienerHorizontalTwist_hasCompactSupport f x).mul_right
  exact hcontinuous.integrable_of_hasCompactSupport hsupport

/-- The transformed derivative source is integrable. -/
theorem zetaPaleyWienerVerticalLineIBPDerivative_integrable
    (f : ZetaAdmissibleFunction) (x y : ℝ) :
    Integrable
      (fun t : ℝ =>
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t) := by
  have hcontinuous :
      Continuous
        (fun t : ℝ =>
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t) := by
    exact (zetaPaleyWienerVerticalLineIBPDerivative_continuous f x).mul
      (Complex.continuous_exp.comp
        ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal))
  have hsupport :
      HasCompactSupport
        (fun t : ℝ =>
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t) := by
    exact (zetaPaleyWienerVerticalLineIBPDerivative_hasCompactSupport f x).mul_right
  exact hcontinuous.integrable_of_hasCompactSupport hsupport

/-- The iterated `t`-derivatives of the horizontal twist.  This is the source family
produced by repeated integration by parts on the vertical oscillation. -/
noncomputable def zetaPaleyWienerHorizontalTwistIteratedDerivative
    (f : ZetaAdmissibleFunction) (n : ℕ) (x t : ℝ) : ℂ :=
  iteratedDeriv n (fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u) t

/-- The zero-th iterated horizontal-twist derivative is the horizontal twist. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_zero
    (f : ZetaAdmissibleFunction) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f 0 x t =
      zetaPaleyWienerHorizontalTwist f x t := by
  exact congrFun
    (iteratedDeriv_zero
      (f := fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u))
    t

/-- The zero-th iterated horizontal-twist derivative agrees with the zero-th vertical
parameter jet. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_zero_eq_verticalJet_zero
    (f : ZetaAdmissibleFunction) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f 0 x t =
      zetaPaleyWienerHorizontalTwistVerticalJet f 0 x t := by
  exact Eq.trans
    (zetaPaleyWienerHorizontalTwistIteratedDerivative_zero f x t)
    (zetaPaleyWienerHorizontalTwistVerticalJet_zero f x t).symm

/-- The one-variable iterated vertical derivative of the horizontal twist is the
vertical-direction parameter jet. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_verticalJet
    (f : ZetaAdmissibleFunction) (n : ℕ) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t =
      zetaPaleyWienerHorizontalTwistVerticalJet f n x t := by
  unfold zetaPaleyWienerHorizontalTwistIteratedDerivative
  unfold zetaPaleyWienerHorizontalTwistVerticalJet
  exact iteratedDeriv_verticalLine_eq_iteratedFDeriv_verticalDirection
    (zetaPaleyWienerHorizontalTwistParameter f)
    (zetaPaleyWienerHorizontalTwistParameter_contDiff f)
    n x t

/-- The one-variable iterated derivative source is the iterated derivative of the parameter
twist restricted to the vertical affine line. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_parameterVerticalLine_iteratedDeriv
    (f : ZetaAdmissibleFunction) (n : ℕ) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t =
      iteratedDeriv n
        (fun u : ℝ =>
          zetaPaleyWienerHorizontalTwistParameter f
            (zetaPaleyWienerVerticalLineEmbedding x u))
        t := by
  rfl

/-- The first iterated derivative of the horizontal twist is the derivative source used in
one vertical-line integration-by-parts step. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_one
    (f : ZetaAdmissibleFunction) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f 1 x t =
      zetaPaleyWienerVerticalLineIBPDerivative f x t := by
  exact congrFun
    (iteratedDeriv_one
      (f := fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u))
    t

/-- Successor iterated derivatives are ordinary derivatives of the previous iterated
derivative source. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_succ
    (f : ZetaAdmissibleFunction) (n : ℕ) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f (n + 1) x t =
      deriv (fun u : ℝ =>
        zetaPaleyWienerHorizontalTwistIteratedDerivative f n x u) t := by
  exact congrFun
    (iteratedDeriv_succ
      (n := n)
      (f := fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u))
    t

/-- The transformed derivative source appearing after one vertical-line integration by parts. -/
noncomputable def zetaPaleyWienerVerticalLineIBPDerivativeIntegral
    (f : ZetaAdmissibleFunction) (x y : ℝ) : ℂ :=
  ∫ t : ℝ,
    zetaPaleyWienerVerticalLineIBPDerivative f x t *
      zetaPaleyWienerVerticalOscillation y t

/-- The nonzero vertical-frequency condition used by one integration-by-parts step. -/
theorem zetaPaleyWienerVerticalFrequency_ne_zero_of_high
    {y : ℝ} (hy : 1 ≤ ‖y‖) :
    (y : ℂ) ≠ 0 := by
  intro hyzero
  have hy_real_zero : y = 0 := by
    have hre :
        ((y : ℂ).re) = (0 : ℂ).re :=
      congrArg Complex.re hyzero
    exact Eq.trans (Complex.ofReal_re y).symm (hre.trans Complex.zero_re)
  have hnorm_zero : ‖y‖ = 0 := by
    exact (congrArg (fun v : ℝ => ‖v‖) hy_real_zero).trans norm_zero
  have hnot : ¬ (1 : ℝ) ≤ 0 := by
    exact not_le_of_gt zero_lt_one
  exact hnot (Eq.subst (motive := fun v : ℝ => 1 ≤ v) hnorm_zero hy)

/-- The vertical oscillation differentiates by multiplication with `I * y`. -/
theorem hasDerivAt_zetaPaleyWienerVerticalOscillation
    (y t : ℝ) :
    HasDerivAt
      (fun u : ℝ => zetaPaleyWienerVerticalOscillation y u)
      (Complex.I * (y : ℂ) *
        zetaPaleyWienerVerticalOscillation y t)
      t := by
    have hlinear_complex :
        HasDerivAt
          (fun w : ℂ => Complex.I * (y : ℂ) * w)
          (Complex.I * (y : ℂ))
          (t : ℂ) := by
      have hid :
          HasDerivAt
            (fun w : ℂ => w)
            (1 : ℂ)
            (t : ℂ) :=
        hasDerivAt_id (t : ℂ)
      have hconst_mul :
          HasDerivAt
            (fun w : ℂ => Complex.I * (y : ℂ) * w)
            (Complex.I * (y : ℂ) * 1)
            (t : ℂ) :=
        hid.const_mul (Complex.I * (y : ℂ))
      have hone :
          Complex.I * (y : ℂ) * 1 = Complex.I * (y : ℂ) :=
        mul_one (Complex.I * (y : ℂ))
      exact Eq.subst
        (motive := fun v : ℂ =>
          HasDerivAt
            (fun w : ℂ => Complex.I * (y : ℂ) * w)
            v
            (t : ℂ))
        hone
        hconst_mul
    have hlinear_real :
        HasDerivAt
          (fun u : ℝ => Complex.I * (y : ℂ) * (u : ℂ))
          (Complex.I * (y : ℂ))
          t :=
      hlinear_complex.comp_ofReal
    have hexp :
        HasDerivAt
          (fun u : ℝ => Complex.exp (Complex.I * (y : ℂ) * (u : ℂ)))
          (Complex.exp (Complex.I * (y : ℂ) * (t : ℂ)) *
            (Complex.I * (y : ℂ)))
          t :=
      (Complex.hasDerivAt_exp (Complex.I * (y : ℂ) * (t : ℂ))).comp
        t hlinear_real
    have hcomm :
        Complex.exp (Complex.I * (y : ℂ) * (t : ℂ)) *
            (Complex.I * (y : ℂ)) =
          Complex.I * (y : ℂ) *
            Complex.exp (Complex.I * (y : ℂ) * (t : ℂ)) :=
      mul_comm
        (Complex.exp (Complex.I * (y : ℂ) * (t : ℂ)))
        (Complex.I * (y : ℂ))
    exact Eq.subst
      (motive := fun v : ℂ =>
        HasDerivAt
          (fun u : ℝ => zetaPaleyWienerVerticalOscillation y u)
          v
          t)
      hcomm
      hexp

/-- The horizontal twist vanishes strictly above the certified support interval. -/
theorem zetaPaleyWienerHorizontalTwist_eq_zero_of_supportInterval_lt
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x t : ℝ) (ht : I.upper < t) :
    zetaPaleyWienerHorizontalTwist f x t = 0 := by
  have hsource :
      f.toZetaTestFunction t = 0 :=
    zetaPaleyWiener_eq_zero_of_supportUpperBound_lt f I ht
  have htest :
      f.toZetaTestFunction' t = f.toZetaTestFunction t :=
    ZetaAdmissibleFunction.toZetaTestFunction'_apply f t
  unfold zetaPaleyWienerHorizontalTwist
  calc
    f.toZetaTestFunction' t * (Real.exp (x * t) : ℂ)
        = f.toZetaTestFunction t * (Real.exp (x * t) : ℂ) := by
          exact congrArg
            (fun v : ℂ => v * (Real.exp (x * t) : ℂ))
            htest
    _ = 0 * (Real.exp (x * t) : ℂ) := by
          exact congrArg
            (fun v : ℂ => v * (Real.exp (x * t) : ℂ))
            hsource
    _ = 0 := zero_mul (Real.exp (x * t) : ℂ)

/-- The horizontal twist vanishes strictly below the certified support interval. -/
theorem zetaPaleyWienerHorizontalTwist_eq_zero_of_lt_supportInterval
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x t : ℝ) (ht : t < I.lower) :
    zetaPaleyWienerHorizontalTwist f x t = 0 := by
  have hsource :
      f.toZetaTestFunction t = 0 :=
    zetaPaleyWiener_eq_zero_of_lt_supportLowerBound f I ht
  have htest :
      f.toZetaTestFunction' t = f.toZetaTestFunction t :=
    ZetaAdmissibleFunction.toZetaTestFunction'_apply f t
  unfold zetaPaleyWienerHorizontalTwist
  calc
    f.toZetaTestFunction' t * (Real.exp (x * t) : ℂ)
        = f.toZetaTestFunction t * (Real.exp (x * t) : ℂ) := by
          exact congrArg
            (fun v : ℂ => v * (Real.exp (x * t) : ℂ))
            htest
    _ = 0 * (Real.exp (x * t) : ℂ) := by
          exact congrArg
            (fun v : ℂ => v * (Real.exp (x * t) : ℂ))
            hsource
    _ = 0 := zero_mul (Real.exp (x * t) : ℂ)

/-- The zero-th vertical jet vanishes below the certified support interval. -/
theorem zetaPaleyWienerHorizontalTwistVerticalJet_zero_eq_zero_off_supportInterval
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x t : ℝ) (ht : t < I.lower) :
    zetaPaleyWienerHorizontalTwistVerticalJet f 0 x t = 0 := by
  exact Eq.trans
    (zetaPaleyWienerHorizontalTwistVerticalJet_zero f x t)
    (zetaPaleyWienerHorizontalTwist_eq_zero_of_lt_supportInterval f I x t ht)

/-- The zero-th vertical jet vanishes above the certified support interval. -/
theorem zetaPaleyWienerHorizontalTwistVerticalJet_zero_eq_zero_of_supportInterval_lt
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x t : ℝ) (ht : I.upper < t) :
    zetaPaleyWienerHorizontalTwistVerticalJet f 0 x t = 0 := by
  exact Eq.trans
    (zetaPaleyWienerHorizontalTwistVerticalJet_zero f x t)
    (zetaPaleyWienerHorizontalTwist_eq_zero_of_supportInterval_lt f I x t ht)

/-- The `ZetaTestFunction` wrapper has the same topological support as the admissible
carrier. -/
theorem zetaPaleyWienerTestFunction_tsupport_eq
    (f : ZetaAdmissibleFunction) :
    tsupport f.toZetaTestFunction' = tsupport f.toZetaTestFunction := by
  exact congrArg tsupport
    (funext
      (fun u : ℝ =>
        ZetaAdmissibleFunction.toZetaTestFunction'_apply f u))

/-- The horizontal twist has no support outside the source support. -/
theorem zetaPaleyWienerHorizontalTwist_tsupport_subset_source
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    tsupport (fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u) ⊆
      tsupport f.toZetaTestFunction := by
  intro t ht
  have hleft :
      t ∈ tsupport (fun u : ℝ => f.toZetaTestFunction' u) := by
    unfold zetaPaleyWienerHorizontalTwist at ht
    exact tsupport_mul_subset_left ht
  exact Eq.subst
    (motive := fun S : Set ℝ => t ∈ S)
    (zetaPaleyWienerTestFunction_tsupport_eq f)
    hleft

/-- Topological support of the derivative is contained in the topological support of the
original one-variable source. -/
theorem zetaPaleyWiener_tsupport_deriv_subset
    (g : ℝ → ℂ) :
    tsupport (deriv g) ⊆ tsupport g := by
  exact closure_minimal support_deriv_subset isClosed_closure

/-- The derivative source produced by the horizontal twist has no support outside the
original admissible source support. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_tsupport_subset_source
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    tsupport (fun t : ℝ => zetaPaleyWienerVerticalLineIBPDerivative f x t) ⊆
      tsupport f.toZetaTestFunction := by
    intro t ht
    have hderiv :
        t ∈ tsupport
          (deriv (fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u)) := by
      unfold zetaPaleyWienerVerticalLineIBPDerivative at ht
      exact ht
    have htwist :
        t ∈ tsupport (fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u) :=
      zetaPaleyWiener_tsupport_deriv_subset
        (fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u)
        hderiv
    exact zetaPaleyWienerHorizontalTwist_tsupport_subset_source f x htwist

/-- Every iterated derivative of the horizontal twist has support contained in the original
admissible source support. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_tsupport_subset_source
    (f : ZetaAdmissibleFunction) (n : ℕ) (x : ℝ) :
    tsupport
        (fun t : ℝ =>
          zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t) ⊆
      tsupport f.toZetaTestFunction := by
  induction n with
  | zero =>
      intro t ht
      exact zetaPaleyWienerHorizontalTwist_tsupport_subset_source f x ht
  | succ n ih =>
      intro t ht
      have hderiv :
          t ∈ tsupport
            (deriv
              (fun u : ℝ =>
                zetaPaleyWienerHorizontalTwistIteratedDerivative f n x u)) := by
        exact Eq.subst
          (motive := fun h : ℝ → ℂ => t ∈ tsupport h)
          (funext
            (fun u : ℝ =>
              zetaPaleyWienerHorizontalTwistIteratedDerivative_succ f n x u))
          ht
      have hprev :
          t ∈ tsupport
            (fun u : ℝ =>
              zetaPaleyWienerHorizontalTwistIteratedDerivative f n x u) :=
        zetaPaleyWiener_tsupport_deriv_subset
          (fun u : ℝ =>
            zetaPaleyWienerHorizontalTwistIteratedDerivative f n x u)
          hderiv
      exact ih hprev

/-- Iterated horizontal-twist derivatives vanish away from the original admissible source
support. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_not_mem_source
    (f : ZetaAdmissibleFunction) (n : ℕ) (x t : ℝ)
    (ht : t ∉ tsupport f.toZetaTestFunction) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t = 0 := by
  exact Function.nmem_support.mp
    (fun hmem =>
      ht
        (zetaPaleyWienerHorizontalTwistIteratedDerivative_tsupport_subset_source
          f n x
          (subset_tsupport _ hmem)))

/-- Iterated horizontal-twist derivatives vanish below the certified support interval. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_off_supportInterval
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (n : ℕ) (x t : ℝ) (ht_lower : t < I.lower) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t = 0 := by
  have hsource_not :
      t ∉ tsupport f.toZetaTestFunction := by
    intro ht
    exact (not_lt_of_ge (I.lower_mem t ht)) ht_lower
  exact zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_not_mem_source
    f n x t hsource_not

/-- Iterated horizontal-twist derivatives vanish above the certified support interval. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_supportInterval_lt
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (n : ℕ) (x t : ℝ) (ht_upper : I.upper < t) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t = 0 := by
  have hsource_not :
      t ∉ tsupport f.toZetaTestFunction := by
    intro ht
    exact (not_lt_of_ge (I.upper_mem t ht)) ht_upper
  exact zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_not_mem_source
    f n x t hsource_not

/-- The derivative source is zero away from the original admissible source support. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_eq_zero_of_not_mem_source
    (f : ZetaAdmissibleFunction) (x t : ℝ)
    (ht : t ∉ tsupport f.toZetaTestFunction) :
    zetaPaleyWienerVerticalLineIBPDerivative f x t = 0 := by
  exact Eq.subst
    (motive := fun v : ℂ => v = 0)
    (zetaPaleyWienerHorizontalTwistIteratedDerivative_one f x t)
    (zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_not_mem_source
      f 1 x t ht)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
