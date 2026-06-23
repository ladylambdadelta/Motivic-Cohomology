import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part09

/-!
# Explicit-formula finite rectangle residues

This owner layer contains finite-rectangle residue equalities, scheduled avoidance, and residue-window error transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The square inverse-kernel residue value from the more natural unscaled side
evaluations.  The right and left vertical side integrals are real constants before the
tangent factor `I` is applied. -/
theorem finiteRectangleSquareBoundaryIntegral_sub_inv_eq_twoPiI_of_unscaledSideValues
    (a : ℂ) (R : ℝ)
    (hbottom :
      finiteRectangleSquareSubInvBottomIntegral a R =
        (Real.pi / 2 : ℂ) * Complex.I)
    (htop :
      finiteRectangleSquareSubInvTopIntegral a R =
        -(Real.pi / 2 : ℂ) * Complex.I)
    (hright :
      finiteRectangleSquareSubInvRightIntegral a R =
        (Real.pi / 2 : ℂ))
    (hleft :
      finiteRectangleSquareSubInvLeftIntegral a R =
        -(Real.pi / 2 : ℂ)) :
    finiteRectangleSquareBoundaryIntegral (fun z : ℂ => (z - a)⁻¹) a R =
      (2 * Real.pi * Complex.I : ℂ) := by
  let q : ℂ := (Real.pi / 2 : ℂ)
  have hright_scaled :
      Complex.I • finiteRectangleSquareSubInvRightIntegral a R =
        (Real.pi / 2 : ℂ) * Complex.I := by
    calc
      Complex.I • finiteRectangleSquareSubInvRightIntegral a R =
          Complex.I • q := by
        exact congrArg (fun z : ℂ => Complex.I • z) hright
      _ = Complex.I * q := by
        rfl
      _ = q * Complex.I := by
        exact mul_comm Complex.I q
      _ = (Real.pi / 2 : ℂ) * Complex.I := by
        rfl
  have hleft_scaled :
      Complex.I • finiteRectangleSquareSubInvLeftIntegral a R =
        -(Real.pi / 2 : ℂ) * Complex.I := by
    calc
      Complex.I • finiteRectangleSquareSubInvLeftIntegral a R =
          Complex.I • (-q) := by
        exact congrArg (fun z : ℂ => Complex.I • z) hleft
      _ = Complex.I * (-q) := by
        rfl
      _ = -(Complex.I * q) := by
        exact mul_neg Complex.I q
      _ = -(q * Complex.I) := by
        exact congrArg Neg.neg (mul_comm Complex.I q)
      _ = -q * Complex.I := by
        exact (neg_mul q Complex.I).symm
      _ = -(Real.pi / 2 : ℂ) * Complex.I := by
        rfl
  exact
    finiteRectangleSquareBoundaryIntegral_sub_inv_eq_twoPiI_of_sideValues
      a R hbottom htop hright_scaled hleft_scaled

/-- Pointwise denominator simplification for the bottom side after translating the square
center to the origin. -/
theorem finiteRectangleSquareSubInvBottom_denominator_centered
    (a : ℂ) (R t : ℝ) :
    ((((t + a.re : ℝ) : ℂ) + (a.im - R) * Complex.I) - a) =
      (t : ℂ) - (R : ℂ) * Complex.I := by
  have hre :
      (((((t + a.re : ℝ) : ℂ) + (a.im - R) * Complex.I) - a).re) =
        (((t : ℂ) - (R : ℂ) * Complex.I).re) := by
    calc
      (((((t + a.re : ℝ) : ℂ) + (a.im - R) * Complex.I) - a).re) =
          ((((t + a.re : ℝ) : ℂ) + (a.im - R) * Complex.I).re) - a.re := by
        exact Complex.sub_re (((t + a.re : ℝ) : ℂ) + (a.im - R) * Complex.I) a
      _ = ((((t + a.re : ℝ) : ℂ).re) +
            (((a.im - R : ℝ) : ℂ) * Complex.I).re) - a.re := by
        exact congrArg
          (fun x : ℝ => x - a.re)
          (Complex.add_re ((t + a.re : ℝ) : ℂ) (((a.im - R : ℝ) : ℂ) * Complex.I))
      _ = ((t + a.re) + (((a.im - R : ℝ) : ℂ) * Complex.I).re) - a.re := by
        exact congrArg
          (fun x : ℝ => (x + (((a.im - R : ℝ) : ℂ) * Complex.I).re) - a.re)
          (Complex.ofReal_re (t + a.re))
      _ = ((t + a.re) + (-(((a.im - R : ℝ) : ℂ).im))) - a.re := by
        exact congrArg
          (fun x : ℝ => ((t + a.re) + x) - a.re)
          (Complex.mul_I_re ((a.im - R : ℝ) : ℂ))
      _ = ((t + a.re) + (-0)) - a.re := by
        exact congrArg
          (fun x : ℝ => ((t + a.re) + (-x)) - a.re)
          (Complex.ofReal_im (a.im - R))
      _ = ((t + a.re) + 0) - a.re := by
        exact congrArg (fun x : ℝ => ((t + a.re) + x) - a.re) (neg_zero.symm)
      _ = (t + a.re) - a.re := by
        exact congrArg (fun x : ℝ => x - a.re) (add_zero (t + a.re))
      _ = t + (a.re - a.re) := by
        exact (add_sub_assoc t a.re a.re).symm
      _ = t + 0 := by
        exact congrArg (fun x : ℝ => t + x) (sub_self a.re)
      _ = t := by
        exact add_zero t
      _ = t - 0 := by
        exact (sub_zero t).symm
      _ = ((t : ℂ).re) - (((R : ℂ) * Complex.I).re) := by
        exact
          Eq.subst
            (motive := fun u : ℝ => t - 0 = u - (((R : ℂ) * Complex.I).re))
            (Complex.ofReal_re t).symm
            (Eq.subst
              (motive := fun v : ℝ => t - 0 = t - v)
              (calc
                (((R : ℂ) * Complex.I).re) = -((R : ℂ).im) := by
                  exact Complex.mul_I_re (R : ℂ)
                _ = -0 := by
                  exact congrArg Neg.neg (Complex.ofReal_im R)
                _ = 0 := by
                  exact neg_zero)
              rfl)
      _ = (((t : ℂ) - (R : ℂ) * Complex.I).re) := by
        exact (Complex.sub_re (t : ℂ) ((R : ℂ) * Complex.I)).symm
  have him :
      (((((t + a.re : ℝ) : ℂ) + (a.im - R) * Complex.I) - a).im) =
        (((t : ℂ) - (R : ℂ) * Complex.I).im) := by
    calc
      (((((t + a.re : ℝ) : ℂ) + (a.im - R) * Complex.I) - a).im) =
          ((((t + a.re : ℝ) : ℂ) + (a.im - R) * Complex.I).im) - a.im := by
        exact Complex.sub_im (((t + a.re : ℝ) : ℂ) + (a.im - R) * Complex.I) a
      _ = ((((t + a.re : ℝ) : ℂ).im) +
            (((a.im - R : ℝ) : ℂ) * Complex.I).im) - a.im := by
        exact congrArg
          (fun x : ℝ => x - a.im)
          (Complex.add_im ((t + a.re : ℝ) : ℂ) (((a.im - R : ℝ) : ℂ) * Complex.I))
      _ = (0 + (((a.im - R : ℝ) : ℂ) * Complex.I).im) - a.im := by
        exact congrArg
          (fun x : ℝ => (x + (((a.im - R : ℝ) : ℂ) * Complex.I).im) - a.im)
          (Complex.ofReal_im (t + a.re))
      _ = (0 + ((a.im - R : ℝ) : ℂ).re) - a.im := by
        exact congrArg
          (fun x : ℝ => (0 + x) - a.im)
          (Complex.mul_I_im ((a.im - R : ℝ) : ℂ))
      _ = (0 + (a.im - R)) - a.im := by
        exact congrArg
          (fun x : ℝ => (0 + x) - a.im)
          (Complex.ofReal_re (a.im - R))
      _ = (a.im - R) - a.im := by
        exact congrArg (fun x : ℝ => x - a.im) (zero_add (a.im - R))
      _ = (a.im + -R) - a.im := by
        exact congrArg (fun x : ℝ => x - a.im) (sub_eq_add_neg a.im R)
      _ = -R + a.im - a.im := by
        exact congrArg (fun x : ℝ => x - a.im) (add_comm a.im (-R))
      _ = -R + (a.im - a.im) := by
        exact add_sub_assoc (-R) a.im a.im
      _ = -R + 0 := by
        exact congrArg (fun x : ℝ => -R + x) (sub_self a.im)
      _ = -R := by
        exact add_zero (-R)
      _ = 0 - R := by
        exact (zero_sub R).symm
      _ = ((t : ℂ).im) - (((R : ℂ) * Complex.I).im) := by
        exact
          Eq.subst
            (motive := fun u : ℝ => 0 - R = u - (((R : ℂ) * Complex.I).im))
            (Complex.ofReal_im t).symm
            (Eq.subst
              (motive := fun v : ℝ => 0 - R = 0 - v)
              (calc
                (((R : ℂ) * Complex.I).im) = (R : ℂ).re := by
                  exact Complex.mul_I_im (R : ℂ)
                _ = R := by
                  exact Complex.ofReal_re R)
              rfl)
      _ = (((t : ℂ) - (R : ℂ) * Complex.I).im) := by
        exact (Complex.sub_im (t : ℂ) ((R : ℂ) * Complex.I)).symm
  exact Complex.ext hre him

/-- The bottom side of the inverse-kernel square boundary, translated to the universal
centered bottom side. -/
theorem finiteRectangleSquareSubInvBottomIntegral_eq_centered
    (a : ℂ) (R : ℝ) :
    finiteRectangleSquareSubInvBottomIntegral a R =
      ∫ t : ℝ in (-R)..R, ((t : ℂ) - (R : ℂ) * Complex.I)⁻¹ := by
  let h : ℝ → ℂ :=
    fun x : ℝ => (((x : ℂ) + (a.im - R) * Complex.I) - a)⁻¹
  have hleft : a.re - R = -R + a.re := by
    calc
      a.re - R = a.re + -R := by
        exact sub_eq_add_neg a.re R
      _ = -R + a.re := by
        exact add_comm a.re (-R)
  have hright : a.re + R = R + a.re := by
    exact add_comm a.re R
  have htranslated :
      (∫ t : ℝ in (-R)..R, h (t + a.re)) =
        ∫ x : ℝ in (-R + a.re)..(R + a.re), h x :=
    intervalIntegral.integral_comp_add_right h a.re
  have hendpoints :
      (∫ x : ℝ in (a.re - R)..(a.re + R), h x) =
        ∫ x : ℝ in (-R + a.re)..(R + a.re), h x :=
    Eq.subst
      (motive := fun left : ℝ =>
        (∫ x : ℝ in left..(a.re + R), h x) =
          ∫ x : ℝ in (-R + a.re)..(R + a.re), h x)
      hleft
      (Eq.subst
        (motive := fun right : ℝ =>
          (∫ x : ℝ in (-R + a.re)..right, h x) =
            ∫ x : ℝ in (-R + a.re)..(R + a.re), h x)
        hright
        rfl)
  have hpoint :
      (∫ t : ℝ in (-R)..R, h (t + a.re)) =
        ∫ t : ℝ in (-R)..R, ((t : ℂ) - (R : ℂ) * Complex.I)⁻¹ := by
    exact
      intervalIntegral.integral_congr
        (fun t _ =>
          congrArg Inv.inv
            (finiteRectangleSquareSubInvBottom_denominator_centered a R t))
  calc
    finiteRectangleSquareSubInvBottomIntegral a R =
        ∫ x : ℝ in (a.re - R)..(a.re + R), h x := by
      rfl
    _ = ∫ x : ℝ in (-R + a.re)..(R + a.re), h x := by
      exact hendpoints
    _ = ∫ t : ℝ in (-R)..R, h (t + a.re) := by
      exact htranslated.symm
    _ = ∫ t : ℝ in (-R)..R, ((t : ℂ) - (R : ℂ) * Complex.I)⁻¹ := by
      exact hpoint

/-- The arctangent antiderivative span that appears in each square-side residue
calculation after scaling the interval to `[-1, 1]`. -/
theorem finiteRectangleSquareSubInv_arctanKernel_neg_one_one_eq_pi_quarters :
    (∫ u : ℝ in (-1)..1, (1 + u ^ 2)⁻¹) =
      Real.pi / 4 + Real.pi / 4 := by
  have hbase :
      (∫ u : ℝ in (-1)..1, (1 + u ^ 2)⁻¹) =
        Real.arctan 1 - Real.arctan (-1) :=
    Real.integral_inv_one_add_sq
  have hone : Real.arctan 1 = Real.pi / 4 :=
    Real.arctan_one
  have hneg_one : Real.arctan (-1) = -(Real.pi / 4) := by
    calc
      Real.arctan (-1) = -Real.arctan 1 := by
        exact Real.arctan_neg 1
      _ = -(Real.pi / 4) := by
        exact congrArg Neg.neg hone
  calc
    (∫ u : ℝ in (-1)..1, (1 + u ^ 2)⁻¹) =
        Real.arctan 1 - Real.arctan (-1) := by
      exact hbase
    _ = Real.pi / 4 - Real.arctan (-1) := by
      exact congrArg (fun z : ℝ => z - Real.arctan (-1)) hone
    _ = Real.pi / 4 - (-(Real.pi / 4)) := by
      exact congrArg (fun z : ℝ => Real.pi / 4 - z) hneg_one
    _ = Real.pi / 4 + Real.pi / 4 := by
      exact sub_neg_eq_add (Real.pi / 4) (Real.pi / 4)

/-- The two arctangent endpoint contributions fold to `π / 2`. -/
theorem finiteRectangleSquareSubInv_pi_quarters_add_eq_half :
    Real.pi / 4 + Real.pi / 4 = Real.pi / 2 := by
  calc
    Real.pi / 4 + Real.pi / 4 =
        (Real.pi / 2) / 2 + (Real.pi / 2) / 2 := by
      exact congrArg₂ HAdd.hAdd
        (div_div Real.pi 2 2).symm
        (div_div Real.pi 2 2).symm
    _ = Real.pi / 2 := by
      exact add_halves (Real.pi / 2)

/-- Complex-coerced form of the arctangent endpoint fold. -/
theorem finiteRectangleSquareSubInv_pi_quarters_add_eq_half_complex :
    ((Real.pi / 4 + Real.pi / 4 : ℝ) : ℂ) =
      (Real.pi / 2 : ℂ) := by
  exact congrArg (fun x : ℝ => (x : ℂ))
    finiteRectangleSquareSubInv_pi_quarters_add_eq_half

/-- Positive-radius coordinate change from the bottom-side arctangent kernel on
`[-R, R]` to the unit interval.  This is the scaling step used by the bottom side-value
proof after the centered inverse kernel has been split into real and imaginary parts. -/
theorem finiteRectangleSquareSubInv_arctanKernel_scaled_comp_div
    {R : ℝ} (hR : 0 < R) :
    (∫ t : ℝ in (-R)..R, (1 + (t / R) ^ 2)⁻¹) =
      R • (∫ u : ℝ in (-1)..1, (1 + u ^ 2)⁻¹) := by
  have hR_ne : R ≠ 0 :=
    ne_of_gt hR
  have hcomp :
      (∫ t : ℝ in (-R)..R, (fun u : ℝ => (1 + u ^ 2)⁻¹) (t / R)) =
        R • (∫ u : ℝ in (-R / R)..(R / R), (1 + u ^ 2)⁻¹) :=
    intervalIntegral.integral_comp_div
      (fun u : ℝ => (1 + u ^ 2)⁻¹) hR_ne
  have hleft : -R / R = -1 := by
    calc
      -R / R = (-R) * R⁻¹ := by
        exact div_eq_mul_inv (-R) R
      _ = -(R * R⁻¹) := by
        exact neg_mul R R⁻¹
      _ = -1 := by
        exact congrArg Neg.neg (mul_inv_cancel₀ hR_ne)
  have hright : R / R = 1 := by
    exact div_self hR_ne
  have hendpoints :
      (∫ u : ℝ in (-R / R)..(R / R), (1 + u ^ 2)⁻¹) =
        ∫ u : ℝ in (-1)..1, (1 + u ^ 2)⁻¹ :=
    Eq.subst
      (motive := fun left : ℝ =>
        (∫ u : ℝ in left..(R / R), (1 + u ^ 2)⁻¹) =
          ∫ u : ℝ in (-1)..1, (1 + u ^ 2)⁻¹)
      hleft
      (Eq.subst
        (motive := fun right : ℝ =>
          (∫ u : ℝ in (-1)..right, (1 + u ^ 2)⁻¹) =
            ∫ u : ℝ in (-1)..1, (1 + u ^ 2)⁻¹)
        hright
        rfl)
  calc
    (∫ t : ℝ in (-R)..R, (1 + (t / R) ^ 2)⁻¹) =
        (∫ t : ℝ in (-R)..R, (fun u : ℝ => (1 + u ^ 2)⁻¹) (t / R)) := by
      rfl
    _ = R • (∫ u : ℝ in (-R / R)..(R / R), (1 + u ^ 2)⁻¹) := by
      exact hcomp
    _ = R • (∫ u : ℝ in (-1)..1, (1 + u ^ 2)⁻¹) := by
      exact congrArg (fun z : ℝ => R • z) hendpoints

/-- Evaluated positive-radius coordinate-change form of the arctangent kernel. -/
theorem finiteRectangleSquareSubInv_arctanKernel_scaled_comp_div_eq
    {R : ℝ} (hR : 0 < R) :
    (∫ t : ℝ in (-R)..R, (1 + (t / R) ^ 2)⁻¹) =
      R • (Real.pi / 2) := by
  have hscale :
      (∫ t : ℝ in (-R)..R, (1 + (t / R) ^ 2)⁻¹) =
        R • (∫ u : ℝ in (-1)..1, (1 + u ^ 2)⁻¹) :=
    finiteRectangleSquareSubInv_arctanKernel_scaled_comp_div hR
  have hunit :
      (∫ u : ℝ in (-1)..1, (1 + u ^ 2)⁻¹) =
        Real.pi / 2 := by
    calc
      (∫ u : ℝ in (-1)..1, (1 + u ^ 2)⁻¹) =
          Real.pi / 4 + Real.pi / 4 := by
        exact finiteRectangleSquareSubInv_arctanKernel_neg_one_one_eq_pi_quarters
      _ = Real.pi / 2 := by
        exact finiteRectangleSquareSubInv_pi_quarters_add_eq_half
  calc
    (∫ t : ℝ in (-R)..R, (1 + (t / R) ^ 2)⁻¹) =
        R • (∫ u : ℝ in (-1)..1, (1 + u ^ 2)⁻¹) := by
      exact hscale
    _ = R • (Real.pi / 2) := by
      exact congrArg (fun z : ℝ => R • z) hunit

/-- The universal arctangent kernel integral over `[-1, 1]` is `π / 2`. -/
theorem finiteRectangleSquareSubInv_arctanKernel_neg_one_one_eq_half :
    (∫ u : ℝ in (-1)..1, (1 + u ^ 2)⁻¹) = Real.pi / 2 := by
  calc
    (∫ u : ℝ in (-1)..1, (1 + u ^ 2)⁻¹) =
        Real.pi / 4 + Real.pi / 4 := by
      exact finiteRectangleSquareSubInv_arctanKernel_neg_one_one_eq_pi_quarters
    _ = Real.pi / 2 := by
      exact finiteRectangleSquareSubInv_pi_quarters_add_eq_half

/-- Complex-coerced form of the universal arctangent kernel integral. -/
theorem finiteRectangleSquareSubInv_arctanKernel_neg_one_one_eq_half_complex :
    ((∫ u : ℝ in (-1)..1, (1 + u ^ 2)⁻¹) : ℂ) =
      (Real.pi / 2 : ℂ) := by
  exact congrArg (fun x : ℝ => (x : ℂ))
    finiteRectangleSquareSubInv_arctanKernel_neg_one_one_eq_half

/-- Cauchy-Goursat for one rectangular subdivision cell.

This is the local analytic input for the finite-hole construction: every subdivision cell
whose closed rectangle lies in the regular region, and whose open rectangle is
differentiable away from a countable exceptional set, contributes zero boundary. -/
theorem finiteRectangleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiable_on_off_countable
    (g : ℂ → ℂ) (z w : ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn g ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd :
      ∀ x : ℂ,
        x ∈
            Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
              Set.Ioo (min z.im w.im) (max z.im w.im) \ s →
          DifferentiableAt ℂ g x) :
    finiteRectangleSubdivisionCellBoundaryIntegral g z w = 0 := by
  exact
    Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
      g z w s hs Hc Hd

/-- Cauchy-Goursat for one subdivision cell with no exceptional set. -/
theorem finiteRectangleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiableOn
    (g : ℂ → ℂ) (z w : ℂ)
    (Hc : ContinuousOn g ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd :
      DifferentiableOn ℂ g
        (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
          Set.Ioo (min z.im w.im) (max z.im w.im))) :
    finiteRectangleSubdivisionCellBoundaryIntegral g z w = 0 := by
  exact
    Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      g z w Hc Hd

/-- A finite subdivision boundary sum is zero once every cell boundary is zero. -/
theorem finiteRectangleSubdivisionBoundarySum_eq_zero_of_cellBoundaries
    {ι : Type*} (cells : Finset ι) (cellBoundary : ι → ℂ)
    (hcell : ∀ c : ι, c ∈ cells → cellBoundary c = 0) :
    (∑ c in cells, cellBoundary c) = 0 := by
  apply Finset.induction_on cells
  · rfl
  · intro a cells ha ih hcell_insert
    have ha_zero : cellBoundary a = 0 :=
      hcell_insert a (Finset.mem_insert_self a cells)
    have hcells_zero :
        (∑ c in cells, cellBoundary c) = 0 :=
      ih
        (fun c hc =>
          hcell_insert c (Finset.mem_insert_of_mem hc))
    calc
      (∑ c in insert a cells, cellBoundary c) =
          cellBoundary a + ∑ c in cells, cellBoundary c := by
        exact Finset.sum_insert ha
      _ = 0 + ∑ c in cells, cellBoundary c := by
        exact congrArg
          (fun x : ℂ => x + ∑ c in cells, cellBoundary c)
          ha_zero
      _ = 0 + 0 := by
        exact congrArg (fun x : ℂ => 0 + x) hcells_zero
      _ = 0 := by
        exact zero_add 0

/-- Two adjacent horizontal cell-edge contributions cancel the shared horizontal edge. -/
theorem finiteRectangleSubdivisionSharedHorizontalEdges_cancel
    (bottom shared top : ℂ) :
    (bottom - shared) + (shared - top) = bottom - top :=
  sub_add_sub_cancel bottom shared top

/-- Two adjacent vertical cell-edge contributions cancel the shared vertical edge with
the tangent factor `I`. -/
theorem finiteRectangleSubdivisionSharedVerticalEdges_cancel
    (left shared right : ℂ) :
    (Complex.I • shared - Complex.I • left) +
        (Complex.I • right - Complex.I • shared) =
      Complex.I • right - Complex.I • left := by
  calc
    (Complex.I • shared - Complex.I • left) +
        (Complex.I • right - Complex.I • shared) =
        (Complex.I • right - Complex.I • shared) +
          (Complex.I • shared - Complex.I • left) := by
      exact add_comm
        (Complex.I • shared - Complex.I • left)
        (Complex.I • right - Complex.I • shared)
    _ = Complex.I • right - Complex.I • left :=
      sub_add_sub_cancel (Complex.I • right) (Complex.I • shared) (Complex.I • left)

/-- Reassociation of four additive terms into paired outer and inner edge groups. -/
theorem finiteRectangleSubdivision_add_two_add_two_group_pairs
    (A B C D : ℂ) :
    (A + C) + (B + D) = (A + B) + (C + D) := by
  calc
    (A + C) + (B + D) = A + (C + (B + D)) := by
      exact add_assoc A C (B + D)
    _ = A + (B + (C + D)) := by
      exact congrArg
        (fun z : ℂ => A + z)
        (calc
          C + (B + D) = C + B + D := by
            exact (add_assoc C B D).symm
          _ = B + C + D := by
            exact congrArg (fun z : ℂ => z + D) (add_comm C B)
          _ = B + (C + D) := by
            exact add_assoc B C D)
    _ = (A + B) + (C + D) := by
      exact (add_assoc A B (C + D)).symm

/-- Reassociation of six additive terms in the order needed for two-cell boundary
cancellation. -/
theorem finiteRectangleSubdivision_add_three_add_three_group_pairs
    (A B C D E F : ℂ) :
    (A + C + E) + (B + D + F) =
      ((A + B) + (C + D)) + (E + F) := by
  calc
    (A + C + E) + (B + D + F) =
        ((A + C) + E) + ((B + D) + F) := rfl
    _ = (A + C) + (E + ((B + D) + F)) := by
      exact add_assoc (A + C) E ((B + D) + F)
    _ = (A + C) + ((B + D) + (E + F)) := by
      exact congrArg
        (fun z : ℂ => (A + C) + z)
        (calc
          E + ((B + D) + F) =
              (B + D) + (E + F) := by
            calc
              E + ((B + D) + F) =
                  E + (B + D) + F := by
                exact (add_assoc E (B + D) F).symm
              _ = (B + D) + E + F := by
                exact congrArg (fun z : ℂ => z + F) (add_comm E (B + D))
              _ = (B + D) + (E + F) := by
                exact add_assoc (B + D) E F)
    _ = ((A + C) + (B + D)) + (E + F) := by
      exact (add_assoc (A + C) (B + D) (E + F)).symm
    _ = (A + (C + (B + D))) + (E + F) := by
      exact congrArg
        (fun z : ℂ => z + (E + F))
        (add_assoc A C (B + D))
    _ = (A + (B + (C + D))) + (E + F) := by
      exact congrArg
        (fun z : ℂ => (A + z) + (E + F))
        (calc
          C + (B + D) = B + (C + D) := by
            calc
              C + (B + D) = C + B + D := by
                exact (add_assoc C B D).symm
              _ = B + C + D := by
                exact congrArg (fun z : ℂ => z + D) (add_comm C B)
              _ = B + (C + D) := by
                exact add_assoc B C D)
    _ = ((A + B) + (C + D)) + (E + F) := by
      exact congrArg
        (fun z : ℂ => z + (E + F))
        (add_assoc A B (C + D)).symm

/-- Algebraic cancellation for two vertically adjacent rectangular cells.

The shared horizontal edge appears once as the top edge of the lower cell and
once as the bottom edge of the upper cell, with opposite signs.  The remaining
vertical side contributions are grouped by side for the later interval-splitting
step. -/
theorem finiteRectangleSubdivisionTwoVerticalCells_boundaryAlgebra
    (bottom shared top right₀ right₁ left₀ left₁ : ℂ) :
    (bottom - shared + right₀ - left₀) +
        (shared - top + right₁ - left₁) =
      bottom - top + (right₀ + right₁) - (left₀ + left₁) := by
  calc
    (bottom - shared + right₀ - left₀) +
        (shared - top + right₁ - left₁) =
        ((bottom - shared) + right₀ + -left₀) +
          ((shared - top) + right₁ + -left₁) := by
      exact congrArg₂ Add.add
        (congrArg
          (fun z : ℂ => z + -left₀)
          (sub_eq_add_neg (bottom - shared + right₀) left₀))
        (congrArg
          (fun z : ℂ => z + -left₁)
          (sub_eq_add_neg (shared - top + right₁) left₁))
    _ =
        (((bottom - shared) + (shared - top)) +
          (right₀ + right₁)) + (-left₀ + -left₁) := by
      exact
        finiteRectangleSubdivision_add_three_add_three_group_pairs
          (bottom - shared) (shared - top) right₀ right₁ (-left₀) (-left₁)
    _ =
        ((bottom - top) + (right₀ + right₁)) + (-left₀ + -left₁) := by
      exact congrArg
        (fun z : ℂ => (z + (right₀ + right₁)) + (-left₀ + -left₁))
        (finiteRectangleSubdivisionSharedHorizontalEdges_cancel bottom shared top)
    _ =
        bottom - top + (right₀ + right₁) - (left₀ + left₁) := by
      calc
        ((bottom - top) + (right₀ + right₁)) + (-left₀ + -left₁) =
            ((bottom - top) + (right₀ + right₁)) + -(left₀ + left₁) := by
          exact congrArg
            (fun z : ℂ => ((bottom - top) + (right₀ + right₁)) + z)
            (neg_add left₀ left₁).symm
        _ = ((bottom - top) + (right₀ + right₁)) - (left₀ + left₁) := by
          exact
            (sub_eq_add_neg
              ((bottom - top) + (right₀ + right₁))
              (left₀ + left₁)).symm
        _ = bottom - top + (right₀ + right₁) - (left₀ + left₁) := rfl

/-- Algebraic cancellation for two horizontally adjacent rectangular cells.

The shared vertical edge appears once as the right edge of the left cell and
once as the left edge of the right cell, with opposite tangent orientations.
The remaining horizontal side contributions are grouped by side for the later
interval-splitting step. -/
theorem finiteRectangleSubdivisionTwoHorizontalCells_boundaryAlgebra
    (bottom₀ bottom₁ top₀ top₁ left shared right : ℂ) :
    (bottom₀ - top₀ + (Complex.I • shared) - (Complex.I • left)) +
        (bottom₁ - top₁ + (Complex.I • right) - (Complex.I • shared)) =
      (bottom₀ + bottom₁) - (top₀ + top₁) +
        (Complex.I • right) - (Complex.I • left) := by
  calc
    (bottom₀ - top₀ + (Complex.I • shared) - (Complex.I • left)) +
        (bottom₁ - top₁ + (Complex.I • right) - (Complex.I • shared)) =
        ((bottom₀ - top₀) + (Complex.I • shared) + -(Complex.I • left)) +
          ((bottom₁ - top₁) + (Complex.I • right) + -(Complex.I • shared)) := by
      exact congrArg₂ Add.add
        (congrArg
          (fun z : ℂ => z + -(Complex.I • left))
          (sub_eq_add_neg
            (bottom₀ - top₀ + (Complex.I • shared))
            (Complex.I • left)))
        (congrArg
          (fun z : ℂ => z + -(Complex.I • shared))
          (sub_eq_add_neg
            (bottom₁ - top₁ + (Complex.I • right))
            (Complex.I • shared)))
    _ =
        ((bottom₀ + bottom₁) + (-(top₀ + top₁))) +
          ((Complex.I • shared - Complex.I • left) +
            (Complex.I • right - Complex.I • shared)) := by
      have hgroup :
          ((bottom₀ - top₀) + (Complex.I • shared) + -(Complex.I • left)) +
              ((bottom₁ - top₁) + (Complex.I • right) + -(Complex.I • shared)) =
            (((bottom₀ - top₀) + (bottom₁ - top₁)) +
              ((Complex.I • shared) + (Complex.I • right))) +
                (-(Complex.I • left) + -(Complex.I • shared)) :=
        finiteRectangleSubdivision_add_three_add_three_group_pairs
          (bottom₀ - top₀) (bottom₁ - top₁)
          (Complex.I • shared) (Complex.I • right)
          (-(Complex.I • left)) (-(Complex.I • shared))
      have hhorizontal :
          (bottom₀ - top₀) + (bottom₁ - top₁) =
            (bottom₀ + bottom₁) + (-(top₀ + top₁)) := by
        calc
          (bottom₀ - top₀) + (bottom₁ - top₁) =
              (bottom₀ + -top₀) + (bottom₁ + -top₁) := by
            exact congrArg₂ Add.add
              (sub_eq_add_neg bottom₀ top₀)
              (sub_eq_add_neg bottom₁ top₁)
          _ = ((bottom₀ + bottom₁) + (-top₀ + -top₁)) := by
            exact
              finiteRectangleSubdivision_add_two_add_two_group_pairs
                bottom₀ bottom₁ (-top₀) (-top₁)
          _ = (bottom₀ + bottom₁) + (-(top₀ + top₁)) := by
            exact congrArg
              (fun z : ℂ => (bottom₀ + bottom₁) + z)
              (neg_add top₀ top₁).symm
      have hvertical :
          ((Complex.I • shared) + (Complex.I • right)) +
              (-(Complex.I • left) + -(Complex.I • shared)) =
            (Complex.I • shared - Complex.I • left) +
              (Complex.I • right - Complex.I • shared) := by
        calc
          ((Complex.I • shared) + (Complex.I • right)) +
              (-(Complex.I • left) + -(Complex.I • shared)) =
              (((Complex.I • shared) + (-(Complex.I • left))) +
                ((Complex.I • right) + (-(Complex.I • shared)))) := by
            exact
              (finiteRectangleSubdivision_add_two_add_two_group_pairs
                (Complex.I • shared) (Complex.I • right)
                (-(Complex.I • left)) (-(Complex.I • shared))).symm
          _ =
              (Complex.I • shared - Complex.I • left) +
                (Complex.I • right - Complex.I • shared) := by
            exact congrArg₂ Add.add
              (sub_eq_add_neg (Complex.I • shared) (Complex.I • left)).symm
              (sub_eq_add_neg (Complex.I • right) (Complex.I • shared)).symm
      exact Eq.trans hgroup
        (calc
          (((bottom₀ - top₀) + (bottom₁ - top₁)) +
              ((Complex.I • shared) + (Complex.I • right))) +
                (-(Complex.I • left) + -(Complex.I • shared)) =
              (((bottom₀ + bottom₁) + (-(top₀ + top₁))) +
                ((Complex.I • shared) + (Complex.I • right))) +
                  (-(Complex.I • left) + -(Complex.I • shared)) := by
            exact congrArg
              (fun z : ℂ =>
                (z + ((Complex.I • shared) + (Complex.I • right))) +
                  (-(Complex.I • left) + -(Complex.I • shared)))
              hhorizontal
          _ =
              ((bottom₀ + bottom₁) + (-(top₀ + top₁))) +
                (((Complex.I • shared) + (Complex.I • right)) +
                  (-(Complex.I • left) + -(Complex.I • shared))) := by
            exact add_assoc
              ((bottom₀ + bottom₁) + (-(top₀ + top₁)))
              ((Complex.I • shared) + (Complex.I • right))
              (-(Complex.I • left) + -(Complex.I • shared))
          _ =
              ((bottom₀ + bottom₁) + (-(top₀ + top₁))) +
                ((Complex.I • shared - Complex.I • left) +
                  (Complex.I • right - Complex.I • shared)) := by
            exact congrArg
              (fun z : ℂ => ((bottom₀ + bottom₁) + (-(top₀ + top₁))) + z)
              hvertical)
    _ =
        ((bottom₀ + bottom₁) + (-(top₀ + top₁))) +
          (Complex.I • right - Complex.I • left) := by
      exact congrArg
        (fun z : ℂ => ((bottom₀ + bottom₁) + (-(top₀ + top₁))) + z)
        (finiteRectangleSubdivisionSharedVerticalEdges_cancel left shared right)
    _ =
      (bottom₀ + bottom₁) - (top₀ + top₁) +
        (Complex.I • right) - (Complex.I • left) := by
      calc
        ((bottom₀ + bottom₁) + (-(top₀ + top₁))) +
            (Complex.I • right - Complex.I • left) =
            ((bottom₀ + bottom₁) - (top₀ + top₁)) +
              (Complex.I • right - Complex.I • left) := by
          exact congrArg
            (fun z : ℂ => z + (Complex.I • right - Complex.I • left))
            (sub_eq_add_neg (bottom₀ + bottom₁) (top₀ + top₁)).symm
        _ =
            (bottom₀ + bottom₁) - (top₀ + top₁) +
              (Complex.I • right) - (Complex.I • left) := by
          exact
            (sub_eq_add_neg
              ((bottom₀ + bottom₁) - (top₀ + top₁) + (Complex.I • right))
              (Complex.I • left)).symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
