import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseBoundaryAlgebra

/-!
# Boundary normalization for semicircle staircase cells

This file owns the conversion from the coordinate-corner definition of one
cell boundary to the named horizontal and vertical staircase pieces.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- Multiplication by `I` commutes with a real scalar inside `ℂ`. -/
theorem Complex.ofReal_mul_I_eq_I_mul_ofReal
    (y : ℝ) :
    (y : ℂ) * Complex.I = Complex.I * (y : ℂ) :=
  mul_comm (y : ℂ) Complex.I

/-- The lower-cell horizontal integrand is the normalized bottom horizontal
integrand. -/
theorem Complex.rightSemicircleStaircaseCellBottomIntegrand_eq
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    (fun x : ℝ =>
      f ((x : ℂ) +
        ((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im : ℂ) *
          Complex.I)) =
      fun x : ℝ =>
        f ((x : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))) := by
  have him :
      (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im =
        c.im + Complex.rightSemicircleStaircaseY ρ m k :=
    Complex.rightSemicircleStaircaseCellLowerCorner_im c ρ m k
  exact funext
    (fun x : ℝ =>
      congrArg
        (fun z : ℂ => f ((x : ℂ) + z))
        (Eq.trans
          (congrArg (fun y : ℝ => (y : ℂ) * Complex.I) him)
          (Complex.ofReal_mul_I_eq_I_mul_ofReal
            (c.im + Complex.rightSemicircleStaircaseY ρ m k))))

/-- The upper-cell horizontal integrand is the normalized top horizontal
integrand. -/
theorem Complex.rightSemicircleStaircaseCellTopIntegrand_eq
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    (fun x : ℝ =>
      f ((x : ℂ) +
        ((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im : ℂ) *
          Complex.I)) =
      fun x : ℝ =>
        f ((x : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ))) := by
  have him :
      (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im =
        c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) :=
    Complex.rightSemicircleStaircaseCellUpperCorner_im c ρ m k
  exact funext
    (fun x : ℝ =>
      congrArg
        (fun z : ℂ => f ((x : ℂ) + z))
        (Eq.trans
          (congrArg (fun y : ℝ => (y : ℂ) * Complex.I) him)
          (Complex.ofReal_mul_I_eq_I_mul_ofReal
            (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)))))

/-- The outer-cell vertical integrand is the normalized outer vertical
integrand. -/
theorem Complex.rightSemicircleStaircaseCellOuterVerticalIntegrand_eq
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    (fun y : ℝ =>
      f (((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re : ℂ) +
        (y : ℂ) * Complex.I)) =
      fun y : ℝ =>
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)) := by
  have hre :
      (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re =
        c.re + ρ :=
    Complex.rightSemicircleStaircaseCellUpperCorner_re c ρ m k
  exact funext
    (fun y : ℝ =>
      congrArg₂
        (fun a b : ℂ => f (a + b))
        (congrArg (fun r : ℝ => (r : ℂ)) hre)
        (Complex.ofReal_mul_I_eq_I_mul_ofReal y))

/-- The inner-cell vertical integrand is the normalized inner vertical
integrand. -/
theorem Complex.rightSemicircleStaircaseCellInnerVerticalIntegrand_eq
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    (fun y : ℝ =>
      f (((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re : ℂ) +
        (y : ℂ) * Complex.I)) =
      fun y : ℝ =>
        f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
          Complex.I * (y : ℂ)) := by
  have hre :
      (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re =
        c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k :=
    Complex.rightSemicircleStaircaseCellLowerCorner_re c ρ m k
  exact funext
    (fun y : ℝ =>
      congrArg₂
        (fun a b : ℂ => f (a + b))
        (congrArg (fun r : ℝ => (r : ℂ)) hre)
        (Complex.ofReal_mul_I_eq_I_mul_ofReal y))

/-- The bottom side of one cell boundary is the normalized bottom horizontal
integral. -/
theorem Complex.rightSemicircleStaircaseCellBottomIntegral_eq
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    (∫ x : ℝ in
      (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re..
        (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re,
      f ((x : ℂ) +
        ((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im : ℂ) *
          Complex.I)) =
      ∫ x : ℝ in
        (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
        f ((x : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))) := by
  let G : ℝ → ℂ := fun x =>
    f ((x : ℂ) +
      ((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im : ℂ) *
        Complex.I)
  let H : ℝ → ℂ := fun x =>
    f ((x : ℂ) +
      Complex.I *
        (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))
  have hfun : G = H :=
    Complex.rightSemicircleStaircaseCellBottomIntegrand_eq f c ρ m k
  have hsame :
      (∫ x : ℝ in
        (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re..
          (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re,
        G x) =
        ∫ x : ℝ in
          (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re..
            (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re,
          H x := by
    exact intervalIntegral.integral_congr (fun x _hx => congrFun hfun x)
  have hleft :
      (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re =
        c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k :=
    Complex.rightSemicircleStaircaseCellLowerCorner_re c ρ m k
  have hright :
      (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re =
        c.re + ρ :=
    Complex.rightSemicircleStaircaseCellUpperCorner_re c ρ m k
  have hbounds :
      (∫ x : ℝ in
          (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re..
            (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re,
          H x) =
        ∫ x : ℝ in
          (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
          H x :=
    congrArg₂
      (fun a b : ℝ => ∫ x : ℝ in a..b, H x)
      hleft
      hright
  exact Eq.trans hsame hbounds

/-- The top side of one cell boundary is the normalized top horizontal
integral. -/
theorem Complex.rightSemicircleStaircaseCellTopIntegral_eq
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    (∫ x : ℝ in
      (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re..
        (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re,
      f ((x : ℂ) +
        ((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im : ℂ) *
          Complex.I)) =
      ∫ x : ℝ in
        (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
        f ((x : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ))) := by
  let G : ℝ → ℂ := fun x =>
    f ((x : ℂ) +
      ((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im : ℂ) *
        Complex.I)
  let H : ℝ → ℂ := fun x =>
    f ((x : ℂ) +
      Complex.I *
        (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))
  have hfun : G = H :=
    Complex.rightSemicircleStaircaseCellTopIntegrand_eq f c ρ m k
  have hsame :
      (∫ x : ℝ in
        (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re..
          (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re,
        G x) =
        ∫ x : ℝ in
          (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re..
            (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re,
          H x := by
    exact intervalIntegral.integral_congr (fun x _hx => congrFun hfun x)
  have hleft :
      (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re =
        c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k :=
    Complex.rightSemicircleStaircaseCellLowerCorner_re c ρ m k
  have hright :
      (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re =
        c.re + ρ :=
    Complex.rightSemicircleStaircaseCellUpperCorner_re c ρ m k
  have hbounds :
      (∫ x : ℝ in
          (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re..
            (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re,
          H x) =
        ∫ x : ℝ in
          (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
          H x :=
    congrArg₂
      (fun a b : ℝ => ∫ x : ℝ in a..b, H x)
      hleft
      hright
  exact Eq.trans hsame hbounds

/-- The outer side of one cell boundary is the normalized outer vertical
integral. -/
theorem Complex.rightSemicircleStaircaseCellOuterVerticalIntegral_eq
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    (∫ y : ℝ in
      (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im..
        (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im,
      f (((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re : ℂ) +
        (y : ℂ) * Complex.I)) =
      ∫ y : ℝ in
        (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
          (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)) := by
  let G : ℝ → ℂ := fun y =>
    f (((Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).re : ℂ) +
      (y : ℂ) * Complex.I)
  let H : ℝ → ℂ := fun y =>
    f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))
  have hfun : G = H :=
    Complex.rightSemicircleStaircaseCellOuterVerticalIntegrand_eq f c ρ m k
  have hsame :
      (∫ y : ℝ in
        (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im..
          (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im,
        G y) =
        ∫ y : ℝ in
          (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im..
            (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im,
          H y := by
    exact intervalIntegral.integral_congr (fun y _hy => congrFun hfun y)
  have hleft :
      (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im =
        c.im + Complex.rightSemicircleStaircaseY ρ m k :=
    Complex.rightSemicircleStaircaseCellLowerCorner_im c ρ m k
  have hright :
      (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im =
        c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) :=
    Complex.rightSemicircleStaircaseCellUpperCorner_im c ρ m k
  have hbounds :
      (∫ y : ℝ in
          (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im..
            (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im,
          H y) =
        ∫ y : ℝ in
          (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
            (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
          H y :=
    congrArg₂
      (fun a b : ℝ => ∫ y : ℝ in a..b, H y)
      hleft
      hright
  exact Eq.trans hsame hbounds

/-- The inner side of one cell boundary is the normalized inner vertical
integral. -/
theorem Complex.rightSemicircleStaircaseCellInnerVerticalIntegral_eq
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    (∫ y : ℝ in
      (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im..
        (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im,
      f (((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re : ℂ) +
        (y : ℂ) * Complex.I)) =
      ∫ y : ℝ in
        (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
          (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
        f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
          Complex.I * (y : ℂ)) := by
  let G : ℝ → ℂ := fun y =>
    f (((Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).re : ℂ) +
      (y : ℂ) * Complex.I)
  let H : ℝ → ℂ := fun y =>
    f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
      Complex.I * (y : ℂ))
  have hfun : G = H :=
    Complex.rightSemicircleStaircaseCellInnerVerticalIntegrand_eq f c ρ m k
  have hsame :
      (∫ y : ℝ in
        (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im..
          (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im,
        G y) =
        ∫ y : ℝ in
          (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im..
            (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im,
          H y := by
    exact intervalIntegral.integral_congr (fun y _hy => congrFun hfun y)
  have hleft :
      (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im =
        c.im + Complex.rightSemicircleStaircaseY ρ m k :=
    Complex.rightSemicircleStaircaseCellLowerCorner_im c ρ m k
  have hright :
      (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im =
        c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) :=
    Complex.rightSemicircleStaircaseCellUpperCorner_im c ρ m k
  have hbounds :
      (∫ y : ℝ in
          (Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k).im..
            (Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k).im,
          H y) =
        ∫ y : ℝ in
          (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
            (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
          H y :=
    congrArg₂
      (fun a b : ℝ => ∫ y : ℝ in a..b, H y)
      hleft
      hright
  exact Eq.trans hsame hbounds

/-- One coordinate-defined cell boundary is the normalized sum of its bottom,
top, outer, and inner staircase pieces. -/
theorem Complex.rightSemicircleStaircaseCellBoundaryIntegral_eq_parts
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    Complex.rightSemicircleStaircaseCellBoundaryIntegral f c ρ m k =
      ((∫ x : ℝ in
          (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
          f ((x : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) -
        (∫ x : ℝ in
          (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
          f ((x : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ))))) +
        Complex.I *
          (∫ y : ℝ in
            (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
              (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
            f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        Complex.I *
          (∫ y : ℝ in
            (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
              (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
            f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
              Complex.I * (y : ℂ))) := by
  let z₀ : ℂ := Complex.rightSemicircleStaircaseCellLowerCorner c ρ m k
  let z₁ : ℂ := Complex.rightSemicircleStaircaseCellUpperCorner c ρ m k
  let Braw : ℂ :=
    ∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)
  let Traw : ℂ :=
    ∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)
  let Oraw : ℂ :=
    ∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)
  let Jraw : ℂ :=
    ∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)
  let B : ℂ :=
    ∫ x : ℝ in
      (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
      f ((x : ℂ) +
        Complex.I *
          (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))
  let T : ℂ :=
    ∫ x : ℝ in
      (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
      f ((x : ℂ) +
        Complex.I *
          (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))
  let O : ℂ :=
    ∫ y : ℝ in
      (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
        (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
      f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))
  let J : ℂ :=
    ∫ y : ℝ in
      (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
        (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
      f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
        Complex.I * (y : ℂ))
  have hraw :
      Complex.rightSemicircleStaircaseCellBoundaryIntegral f c ρ m k =
        Braw - Traw + Complex.I * Oraw - Complex.I * Jraw := rfl
  have hB : Braw = B :=
    Complex.rightSemicircleStaircaseCellBottomIntegral_eq f c ρ m k
  have hT : Traw = T :=
    Complex.rightSemicircleStaircaseCellTopIntegral_eq f c ρ m k
  have hO : Oraw = O :=
    Complex.rightSemicircleStaircaseCellOuterVerticalIntegral_eq f c ρ m k
  have hJ : Jraw = J :=
    Complex.rightSemicircleStaircaseCellInnerVerticalIntegral_eq f c ρ m k
  have hparts :
      Braw - Traw + Complex.I * Oraw - Complex.I * Jraw =
        B - T + Complex.I * O - Complex.I * J :=
    congrArg₂
      (fun A D : ℂ => A - D)
      (congrArg₂
        (fun A C : ℂ => A + C)
        (congrArg₂ (fun A C : ℂ => A - C) hB hT)
        (congrArg (fun C : ℂ => Complex.I * C) hO))
      (congrArg (fun C : ℂ => Complex.I * C) hJ)
  exact Eq.trans hraw hparts

/-- The polygonal core boundary definition is the normalized fixed-side
expression with the staircase arc expanded into horizontal, vertical, and top
connector pieces. -/
theorem Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral_eq_parts
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m =
      (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
        (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
        Complex.I *
          (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
            f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        (((∑ k in Finset.range (m + 1),
            Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
          (∑ k in Finset.range (m + 1),
            Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k)) +
          Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) := by
  let B : ℂ :=
    ∫ x : ℝ in c.re..(c.re + ρ),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))
  let T : ℂ :=
    ∫ x : ℝ in c.re..(c.re + ρ),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))
  let O : ℂ :=
    ∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
      f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))
  let H : ℕ → ℂ := fun k =>
    Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k
  let V : ℕ → ℂ := fun k =>
    Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k
  let C : ℂ := Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m
  have harc :
      Complex.rightSemicirclePolygonalArcIntegral f c ρ m =
        (Finset.sum (Finset.range (m + 1)) H +
          Finset.sum (Finset.range (m + 1)) V) + C := by
    have hsum :
        Finset.sum (Finset.range (m + 1)) (fun k => H k + V k) =
          Finset.sum (Finset.range (m + 1)) H +
            Finset.sum (Finset.range (m + 1)) V :=
      Finset.sum_add_distrib
    exact
      Eq.trans
        (congrArg
          (fun z : ℂ => z + C)
          hsum)
        rfl
  have hraw :
      Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m =
        B - T + Complex.I * O - Complex.rightSemicirclePolygonalArcIntegral f c ρ m := rfl
  exact
    Eq.trans
      hraw
      (congrArg
        (fun z : ℂ => B - T + Complex.I * O - z)
        harc)

end

end LFunctions
end Boundary
