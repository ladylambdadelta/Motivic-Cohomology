import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseTailTelescoping

/-!
# Connector parametrizations for semicircle staircase cells

This file owns the translation from relative staircase coordinates to absolute
coordinates for horizontal connectors and their interval-integrability inputs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- Relative and absolute parametrizations of one horizontal staircase
connector agree. -/
theorem Complex.rightSemicircleStaircaseHorizontalIntegral_eq_absolute
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k =
      ∫ x : ℝ in
        (c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m k)..
          (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k),
        f ((x : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))) := by
  unfold Complex.rightSemicircleStaircaseHorizontalIntegral
  let G : ℝ → ℂ := fun x =>
    f ((x : ℂ) +
      Complex.I *
        (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))
  have htranslate :
      (∫ x : ℝ in
          Complex.rightSemicircleStaircasePrevSafeRe ρ m k..
            Complex.rightSemicircleStaircaseSafeRe ρ m k,
          G (x + c.re)) =
        ∫ x : ℝ in
          (Complex.rightSemicircleStaircasePrevSafeRe ρ m k + c.re)..
            (Complex.rightSemicircleStaircaseSafeRe ρ m k + c.re),
          G x := by
    exact
      intervalIntegral.integral_comp_add_right
        (f := G)
        (a := Complex.rightSemicircleStaircasePrevSafeRe ρ m k)
        (b := Complex.rightSemicircleStaircaseSafeRe ρ m k)
        c.re
  have hsource :
      (∫ x : ℝ in
          Complex.rightSemicircleStaircasePrevSafeRe ρ m k..
            Complex.rightSemicircleStaircaseSafeRe ρ m k,
          f (((c.re + x : ℝ) : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) =
        ∫ x : ℝ in
          Complex.rightSemicircleStaircasePrevSafeRe ρ m k..
            Complex.rightSemicircleStaircaseSafeRe ρ m k,
          G (x + c.re) := by
    exact
      intervalIntegral.integral_congr
        (fun x _hx =>
          congrArg
            (fun r : ℝ =>
              f ((r : ℂ) +
                Complex.I *
                  (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
            (add_comm c.re x))
  show
    (∫ x : ℝ in
        Complex.rightSemicircleStaircasePrevSafeRe ρ m k..
          Complex.rightSemicircleStaircaseSafeRe ρ m k,
        f (((c.re + x : ℝ) : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) =
      ∫ x : ℝ in
        (c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m k)..
          (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k),
        G x
  exact
    Eq.trans hsource
      (Eq.trans htranslate
        (congrArg₂
          (fun a b : ℝ => ∫ x : ℝ in a..b, G x)
          (add_comm (Complex.rightSemicircleStaircasePrevSafeRe ρ m k) c.re)
          (add_comm (Complex.rightSemicircleStaircaseSafeRe ρ m k) c.re)))

/-- Relative and absolute parametrizations of the top staircase connector
agree. -/
theorem Complex.rightSemicircleStaircaseTopConnectorIntegral_eq_absolute
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m =
      ∫ x : ℝ in
        (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m)..c.re,
        f ((x : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) := by
  unfold Complex.rightSemicircleStaircaseTopConnectorIntegral
  let G : ℝ → ℂ := fun x =>
    f ((x : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))
  have htranslate :
      (∫ x : ℝ in
          Complex.rightSemicircleStaircaseSafeRe ρ m m..0,
          G (x + c.re)) =
        ∫ x : ℝ in
          (Complex.rightSemicircleStaircaseSafeRe ρ m m + c.re)..(0 + c.re),
          G x := by
    exact
      intervalIntegral.integral_comp_add_right
        (f := G)
        (a := Complex.rightSemicircleStaircaseSafeRe ρ m m)
        (b := 0)
        c.re
  have hsource :
      (∫ x : ℝ in
          Complex.rightSemicircleStaircaseSafeRe ρ m m..0,
          f (((c.re + x : ℝ) : ℂ) +
            Complex.I * (((c.im + ρ : ℝ) : ℂ)))) =
        ∫ x : ℝ in
          Complex.rightSemicircleStaircaseSafeRe ρ m m..0,
          G (x + c.re) := by
    exact
      intervalIntegral.integral_congr
        (fun x _hx =>
          congrArg
            (fun r : ℝ =>
              f ((r : ℂ) + Complex.I * (((c.im + ρ : ℝ) : ℂ))))
            (add_comm c.re x))
  show
    (∫ x : ℝ in Complex.rightSemicircleStaircaseSafeRe ρ m m..0,
        f (((c.re + x : ℝ) : ℂ) +
          Complex.I * (((c.im + ρ : ℝ) : ℂ)))) =
      ∫ x : ℝ in
        (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m)..c.re,
        G x
  exact
    Eq.trans hsource
      (Eq.trans htranslate
        (congrArg₂
          (fun a b : ℝ => ∫ x : ℝ in a..b, G x)
          (add_comm (Complex.rightSemicircleStaircaseSafeRe ρ m m) c.re)
          (zero_add c.re)))

/-- A translated horizontal connector integrand is pointwise equal to the
absolute-coordinate horizontal connector integrand. -/
theorem Complex.rightSemicircleStaircaseHorizontal_absolute_integrand_eq
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    (fun x : ℝ =>
      f (((c.re + (x + -c.re) : ℝ) : ℂ) +
        Complex.I *
          (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) =
      fun x : ℝ =>
        f ((x : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))) :=
  funext
    (fun x : ℝ =>
      congrArg
        (fun r : ℝ =>
          f ((r : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
        (calc
          c.re + (x + -c.re) = (c.re + x) + -c.re := by
            exact Eq.symm (add_assoc c.re x (-c.re))
          _ = (c.re + -c.re) + x := by
            exact add_right_comm c.re x (-c.re)
          _ = 0 + x := by
            exact congrArg (fun r : ℝ => r + x) (add_neg_cancel c.re)
          _ = x := zero_add x))

/-- A translated top-connector integrand is pointwise equal to the
absolute-coordinate top-connector integrand. -/
theorem Complex.rightSemicircleStaircaseTopConnector_absolute_integrand_eq
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) :
    (fun x : ℝ =>
      f (((c.re + (x + -c.re) : ℝ) : ℂ) +
        Complex.I * (((c.im + ρ : ℝ) : ℂ)))) =
      fun x : ℝ =>
        f ((x : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) :=
  funext
    (fun x : ℝ =>
      congrArg
        (fun r : ℝ =>
          f ((r : ℂ) + Complex.I * (((c.im + ρ : ℝ) : ℂ))))
        (calc
          c.re + (x + -c.re) = (c.re + x) + -c.re := by
            exact Eq.symm (add_assoc c.re x (-c.re))
          _ = (c.re + -c.re) + x := by
            exact add_right_comm c.re x (-c.re)
          _ = 0 + x := by
            exact congrArg (fun r : ℝ => r + x) (add_neg_cancel c.re)
          _ = x := zero_add x))

/-- Absolute-coordinate interval-integrability for one horizontal staircase
connector. -/
theorem Complex.intervalIntegrable_rightSemicircleStaircaseHorizontal_absolute
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun x : ℝ =>
        f ((x : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
      volume
      (c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m k)
      (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k) := by
  have hrel :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((c.re + x : ℝ) : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
        volume
        (Complex.rightSemicircleStaircasePrevSafeRe ρ m k)
        (Complex.rightSemicircleStaircaseSafeRe ρ m k) :=
    Complex.intervalIntegrable_rightSemicircleStaircaseHorizontal
      f c hρ m k hk hcont
  have hshift := hrel.comp_add_right (-c.re)
  have hleft :
      Complex.rightSemicircleStaircasePrevSafeRe ρ m k - -c.re =
        c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m k := by
    calc
      Complex.rightSemicircleStaircasePrevSafeRe ρ m k - -c.re =
          Complex.rightSemicircleStaircasePrevSafeRe ρ m k + c.re :=
            sub_neg_eq_add
              (Complex.rightSemicircleStaircasePrevSafeRe ρ m k)
              c.re
      _ = c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m k :=
          add_comm (Complex.rightSemicircleStaircasePrevSafeRe ρ m k) c.re
  have hright :
      Complex.rightSemicircleStaircaseSafeRe ρ m k - -c.re =
        c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k := by
    calc
      Complex.rightSemicircleStaircaseSafeRe ρ m k - -c.re =
          Complex.rightSemicircleStaircaseSafeRe ρ m k + c.re :=
            sub_neg_eq_add
              (Complex.rightSemicircleStaircaseSafeRe ρ m k)
              c.re
      _ = c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k :=
          add_comm (Complex.rightSemicircleStaircaseSafeRe ρ m k) c.re
  have hfun :
      (fun x : ℝ =>
        f (((c.re + (x + -c.re) : ℝ) : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) =
        fun x : ℝ =>
          f ((x : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))) :=
    Complex.rightSemicircleStaircaseHorizontal_absolute_integrand_eq f c ρ m k
  exact
    Eq.subst
      (motive := fun a : ℝ =>
        IntervalIntegrable
          (fun x : ℝ =>
            f ((x : ℂ) +
              Complex.I *
                (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
          volume a (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k))
      hleft
      (Eq.subst
        (motive := fun b : ℝ =>
          IntervalIntegrable
            (fun x : ℝ =>
              f ((x : ℂ) +
                Complex.I *
                  (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
            volume
            (Complex.rightSemicircleStaircasePrevSafeRe ρ m k - -c.re) b)
        hright
        (Eq.subst
          (motive := fun G : ℝ → ℂ =>
            IntervalIntegrable G volume
              (Complex.rightSemicircleStaircasePrevSafeRe ρ m k - -c.re)
              (Complex.rightSemicircleStaircaseSafeRe ρ m k - -c.re))
          hfun
          hshift))

/-- Absolute-coordinate interval-integrability for the top connector. -/
theorem Complex.intervalIntegrable_rightSemicircleStaircaseTopConnector_absolute
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun x : ℝ =>
        f ((x : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
      volume
      (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m)
      c.re := by
  have hrel :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((c.re + x : ℝ) : ℂ) +
            Complex.I * (((c.im + ρ : ℝ) : ℂ))))
        volume
        (Complex.rightSemicircleStaircaseSafeRe ρ m m)
        0 :=
    Complex.intervalIntegrable_rightSemicircleStaircaseTopConnector
      f c hρ m hcont
  have hshift := hrel.comp_add_right (-c.re)
  have hleft :
      Complex.rightSemicircleStaircaseSafeRe ρ m m - -c.re =
        c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m := by
    calc
      Complex.rightSemicircleStaircaseSafeRe ρ m m - -c.re =
          Complex.rightSemicircleStaircaseSafeRe ρ m m + c.re :=
            sub_neg_eq_add
              (Complex.rightSemicircleStaircaseSafeRe ρ m m)
              c.re
      _ = c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m :=
          add_comm (Complex.rightSemicircleStaircaseSafeRe ρ m m) c.re
  have hright : (0 : ℝ) - -c.re = c.re := by
    calc
      (0 : ℝ) - -c.re = 0 + c.re := sub_neg_eq_add 0 c.re
      _ = c.re := zero_add c.re
  have hfun :
      (fun x : ℝ =>
        f (((c.re + (x + -c.re) : ℝ) : ℂ) +
          Complex.I * (((c.im + ρ : ℝ) : ℂ)))) =
        fun x : ℝ =>
          f ((x : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) :=
    Complex.rightSemicircleStaircaseTopConnector_absolute_integrand_eq f c ρ
  exact
    Eq.subst
      (motive := fun a : ℝ =>
        IntervalIntegrable
          (fun x : ℝ =>
            f ((x : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
          volume a c.re)
      hleft
      (Eq.subst
        (motive := fun b : ℝ =>
          IntervalIntegrable
            (fun x : ℝ =>
              f ((x : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
            volume
            (Complex.rightSemicircleStaircaseSafeRe ρ m m - -c.re) b)
        hright
        (Eq.subst
          (motive := fun G : ℝ → ℂ =>
            IntervalIntegrable G volume
              (Complex.rightSemicircleStaircaseSafeRe ρ m m - -c.re)
              ((0 : ℝ) - -c.re))
          hfun
          hshift))

/-- The absolute horizontal-tail coordinate at the zeroth previous safe point
is the center real coordinate. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_zero_add_re
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 = c.re := by
  calc
    c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 =
        c.re + 0 := by
      exact
        congrArg
          (fun x : ℝ => c.re + x)
          (Complex.rightSemicircleStaircasePrevSafeRe_zero ρ m)
    _ = c.re := add_zero c.re

/-- The absolute horizontal-tail coordinate at the successor previous safe
point is the current absolute safe coordinate. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_succ_add_re
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m (k + 1) =
      c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  exact
    congrArg
      (fun x : ℝ => c.re + x)
      (Complex.rightSemicircleStaircasePrevSafeRe_succ ρ m k)

/-- The zeroth horizontal-tail integrand is the bottom horizontal integrand. -/
theorem Complex.rightSemicircleStaircaseHorizontalTailIntegrand_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    (fun x : ℝ =>
      f ((x : ℂ) +
        Complex.I *
          (((c.im + Complex.rightSemicircleStaircaseY ρ m 0 : ℝ) : ℂ)))) =
      fun x : ℝ =>
        f ((x : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) :=
  funext
    (fun x : ℝ =>
      congrArg
        (fun y : ℝ =>
          f ((x : ℂ) + Complex.I * ((c.im + y : ℝ) : ℂ)))
        (Complex.rightSemicircleStaircaseY_zero ρ m))

/-- The final horizontal-tail integrand is the top horizontal integrand. -/
theorem Complex.rightSemicircleStaircaseHorizontalTailIntegrand_last
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    (fun x : ℝ =>
      f ((x : ℂ) +
        Complex.I *
          (((c.im + Complex.rightSemicircleStaircaseY ρ m (m + 1) : ℝ) : ℂ)))) =
      fun x : ℝ =>
        f ((x : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) :=
  funext
    (fun x : ℝ =>
      congrArg
        (fun y : ℝ =>
          f ((x : ℂ) + Complex.I * ((c.im + y : ℝ) : ℂ)))
        (Complex.rightSemicircleStaircaseY_last ρ m))

end

end LFunctions
end Boundary
