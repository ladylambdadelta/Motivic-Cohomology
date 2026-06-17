import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.BoundaryLogAssembly.BoundaryCircleCore

/-!
# Boundary-circle zero regularity for Jensen formula

This split owns the finite circle-zero and boundary-arc injectivity facts needed
by boundary-log assembly.  The heavier logarithmic-integrability gluing remains
in the next regularity layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The zero set of a nontrivial entire function meets each compact discrete
support in a finite set. -/
theorem entireFunction_zeroSet_finite_on_compact_of_discrete
    {S : Set ℂ}
    (hdisc : DiscreteTopology S)
    (hcomp : IsCompact S) :
    S.Finite := by
  exact hcomp.finite hdisc

/-- Nontriviality rules out the locally identically-zero branch at a zero. -/
theorem entireFunction_eventually_ne_zero_nhdsWithin_of_nontrivial
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    {x : ℂ} :
    ∀ᶠ w in 𝓝[≠] x, F w ≠ 0 := by
  exact
    Or.elim (hF x).eventually_eq_zero_or_eventually_ne_zero
      (fun hzero =>
        False.elim
          (Exists.elim hnontrivial
            (fun z0 hz0 =>
              let hU : AnalyticOnNhd ℂ F (Set.univ : Set ℂ) :=
                fun z _ => hF z
              let hEq : Set.EqOn F 0 (Set.univ : Set ℂ) :=
                hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero
                  isPreconnected_univ (by exact Set.mem_univ _) hzero
              hz0 (hEq (by exact Set.mem_univ _)))))
      (fun hne => hne)

/-- The zero set of a nontrivial entire function is discrete on each fixed
circle of radius `r`. -/
theorem entireFunction_circleZeros_discreteTopology
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (r : ℝ) :
    DiscreteTopology {z : ℂ | ‖z‖ = r ∧ F z = 0} := by
  exact
    (discreteTopology_subtype_iff).2
      (fun x hx =>
        let hne : ∀ᶠ w in 𝓝[≠] x, F w ≠ 0 :=
          entireFunction_eventually_ne_zero_nhdsWithin_of_nontrivial
            F hF hnontrivial
        let hScompl :
            ({z : ℂ | ‖z‖ = r ∧ F z = 0}ᶜ) ∈ 𝓝[≠] x :=
          Filter.mem_of_superset hne
            (fun w hw hsw => hw hsw.2)
        disjoint_iff.mp ((Filter.disjoint_principal_right).2 hScompl))

/-- The zero set of a nontrivial entire function meets each fixed circle in a
finite set. -/
theorem entireFunction_circleZeros_finite
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (r : ℝ) :
    Set.Finite {z : ℂ | ‖z‖ = r ∧ F z = 0} := by
  have hdisc : DiscreteTopology {z : ℂ | ‖z‖ = r ∧ F z = 0} :=
    entireFunction_circleZeros_discreteTopology F hF hnontrivial r
  have hcircleClosed : IsClosed {z : ℂ | ‖z‖ = r} :=
    isClosed_eq continuous_norm continuous_const
  have hzeroClosed : IsClosed {z : ℂ | F z = 0} := by
    have hcontF : Continuous F :=
      continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
    exact isClosed_eq hcontF continuous_const
  have hclosed : IsClosed {z : ℂ | ‖z‖ = r ∧ F z = 0} :=
    hcircleClosed.inter hzeroClosed
  have hsubset :
      {z : ℂ | ‖z‖ = r ∧ F z = 0} ⊆ Metric.closedBall (0 : ℂ) r :=
    fun z hz =>
      Metric.mem_closedBall.2
        (calc
          dist z 0 = ‖z - 0‖ := dist_eq_norm z 0
          _ = ‖z‖ := congrArg norm (sub_zero z)
          _ ≤ r := hz.1.le)
  have hcomp : IsCompact {z : ℂ | ‖z‖ = r ∧ F z = 0} :=
    (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset hclosed hsubset
  exact entireFunction_zeroSet_finite_on_compact_of_discrete
    (S := {z : ℂ | ‖z‖ = r ∧ F z = 0}) hdisc hcomp

/-- Compatibility alias for the old finite-circle-zero owner name. -/
theorem entireFunction_finite_circle_zeros
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (r : ℝ) :
    Set.Finite {z : ℂ | ‖z‖ = r ∧ F z = 0} :=
  entireFunction_circleZeros_finite F hF hnontrivial r

/-- The zero set of a nontrivial entire function meets each doubled Jensen circle
in a finite set. -/
theorem entireFunction_jensenCircleZeros_finite
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ) :
    Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0} :=
  entireFunction_circleZeros_finite F hF hnontrivial (2 * R)

/-- Two parameters in the fundamental arc differ by less than one full period. -/
theorem real_abs_sub_lt_two_pi_of_mem_Ioc
    {θ₁ θ₂ : ℝ}
    (hθ₁ : θ₁ ∈ Set.Ioc 0 (2 * Real.pi))
    (hθ₂ : θ₂ ∈ Set.Ioc 0 (2 * Real.pi)) :
    |θ₁ - θ₂| < 2 * Real.pi := by
  have hleft : θ₁ - θ₂ < 2 * Real.pi :=
    (sub_lt_self θ₁ hθ₂.1).trans_le hθ₁.2
  have hright : θ₂ - θ₁ < 2 * Real.pi :=
    (sub_lt_self θ₂ hθ₁.1).trans_le hθ₂.2
  exact abs_sub_lt_iff.mpr ⟨hleft, hright⟩

/-- A real arc equality by an integer period is trivial inside the fundamental
arc. -/
theorem real_exp_arc_period_eq_of_mem_Ioc
    {θ₁ θ₂ : ℝ}
    (hθ₁ : θ₁ ∈ Set.Ioc 0 (2 * Real.pi))
    (hθ₂ : θ₂ ∈ Set.Ioc 0 (2 * Real.pi))
    {n : ℤ}
    (hθ : θ₁ = θ₂ + n * (2 * Real.pi)) :
    θ₁ = θ₂ := by
  have hdiff : θ₁ - θ₂ = n * (2 * Real.pi) := by
    calc
      θ₁ - θ₂ = (θ₂ + n * (2 * Real.pi)) - θ₂ := by
        exact congrArg (fun t : ℝ => t - θ₂) hθ
      _ = n * (2 * Real.pi) :=
        add_sub_cancel_left θ₂ (n * (2 * Real.pi))
  have hsmall : |θ₁ - θ₂| < 2 * Real.pi :=
    real_abs_sub_lt_two_pi_of_mem_Ioc hθ₁ hθ₂
  have hn0 : n = 0 :=
    match eq_or_ne n 0 with
    | Or.inl hn => hn
    | Or.inr hn =>
        False.elim
          (let hperiod : |θ₁ - θ₂| = |(n : ℝ)| * (2 * Real.pi) :=
            calc
              |θ₁ - θ₂| = |(n : ℝ) * (2 * Real.pi)| := by
                exact congrArg abs hdiff
              _ = |(n : ℝ)| * |2 * Real.pi| :=
                abs_mul (n : ℝ) (2 * Real.pi)
              _ = |(n : ℝ)| * (2 * Real.pi) := by
                exact congrArg (fun x : ℝ => |(n : ℝ)| * x)
                  (abs_of_pos Real.two_pi_pos)
          let hlarge : 2 * Real.pi ≤ |θ₁ - θ₂| :=
            calc
              2 * Real.pi ≤ |(n : ℝ)| * (2 * Real.pi) :=
                real_two_pi_le_abs_int_mul_two_pi n hn
              _ = |θ₁ - θ₂| := hperiod.symm
          not_lt_of_ge hlarge hsmall)
  have hzero_period :
      θ₁ = θ₂ + ((0 : ℤ) : ℝ) * (2 * Real.pi) :=
    Eq.subst
      (motive := fun m : ℤ => θ₁ = θ₂ + (m : ℝ) * (2 * Real.pi))
      hn0
      hθ
  calc
    θ₁ = θ₂ + ((0 : ℤ) : ℝ) * (2 * Real.pi) := hzero_period
    _ = θ₂ + 0 * (2 * Real.pi) := by
      exact congrArg
        (fun t : ℝ => θ₂ + t * (2 * Real.pi))
        Int.cast_zero
    _ = θ₂ + 0 := by
      exact congrArg (fun t : ℝ => θ₂ + t)
        (zero_mul (2 * Real.pi))
    _ = θ₂ := add_zero θ₂

/-- The circle parametrization is injective on the open fundamental arc
`(0, 2π]` at an arbitrary positive radius. -/
theorem entireFunction_boundaryCircleParam_injectiveOn_Ioc
    {R : ℝ}
    (hR : 0 < R) :
    Set.InjOn
      (fun θ : ℝ => (R : ℂ) * Complex.exp (θ * Complex.I))
      (Set.Ioc 0 (2 * Real.pi)) := by
  intro θ₁ hθ₁ θ₂ hθ₂ hEq
  have hRne : (R : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hR.ne'
  have hExp : Complex.exp (θ₁ * Complex.I) = Complex.exp (θ₂ * Complex.I) :=
    mul_left_cancel₀ hRne hEq
  exact
    Exists.elim (real_exp_arc_eq_of_complex_exp_eq θ₁ θ₂ hExp)
      (fun n hn =>
        real_exp_arc_period_eq_of_mem_Ioc hθ₁ hθ₂ hn)

/-- The doubled-circle parametrization is injective on the open fundamental arc
`(0, 2π]`. -/
theorem entireFunction_jensenBoundaryCircleParam_injectiveOn_Ioc
    {R : ℝ}
    (hR : 0 < R) :
    Set.InjOn
      (fun θ : ℝ => (2 * R : ℂ) * Complex.exp (θ * Complex.I))
      (Set.Ioc 0 (2 * Real.pi)) := by
  have htwoR_pos : 0 < 2 * R :=
    mul_pos zero_lt_two hR
  have hraw :
      Set.InjOn
        (fun θ : ℝ => ((2 * R : ℝ) : ℂ) * Complex.exp (θ * Complex.I))
        (Set.Ioc 0 (2 * Real.pi)) :=
    entireFunction_boundaryCircleParam_injectiveOn_Ioc htwoR_pos
  have hscale : ((2 * R : ℝ) : ℂ) = (2 : ℂ) * (R : ℂ) :=
    Complex.ofReal_mul 2 R
  intro θ₁ hθ₁ θ₂ hθ₂ hEq
  exact hraw hθ₁ hθ₂
    (calc
      ((2 * R : ℝ) : ℂ) * Complex.exp (θ₁ * Complex.I) =
          (2 : ℂ) * (R : ℂ) * Complex.exp (θ₁ * Complex.I) := by
        exact congrArg
          (fun x : ℂ => x * Complex.exp (θ₁ * Complex.I))
          hscale
      _ = (2 : ℂ) * (R : ℂ) * Complex.exp (θ₂ * Complex.I) :=
        hEq
      _ = ((2 * R : ℝ) : ℂ) * Complex.exp (θ₂ * Complex.I) := by
        exact congrArg
          (fun x : ℂ => x * Complex.exp (θ₂ * Complex.I))
          hscale.symm)

end
end LFunctions
end Boundary
