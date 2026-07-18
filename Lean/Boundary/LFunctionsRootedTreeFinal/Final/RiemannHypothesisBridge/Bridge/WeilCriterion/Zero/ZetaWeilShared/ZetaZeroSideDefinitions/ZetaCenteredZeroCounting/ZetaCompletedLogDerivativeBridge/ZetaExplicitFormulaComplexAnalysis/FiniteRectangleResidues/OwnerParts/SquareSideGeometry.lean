import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.SquareSideIntegrability

/-!
# Finite-height singular geometry

Every completed contour singularity in the raw vertical strip belongs to the finite raw
singular carrier. Square-side coordinate avoidance therefore gives global line regularity.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Every completed contour singularity of raw imaginary height below `T` belongs to the
finite raw singular-coordinate carrier. -/
theorem explicitFormulaRectangleRawSingularCoordinates_mem_of_singular_abs_im_lt
    (T : ℝ) {z : ℂ}
    (hz : z ∈ completedZetaContourIntegrandSingularSet)
    (him : |z.im| < T) :
    z ∈ explicitFormulaRectangleRawSingularCoordinates T := by
  match hz with
  | Or.inl hzero =>
      exact Eq.subst
        (motive := fun value : ℂ =>
          value ∈ explicitFormulaRectangleRawSingularCoordinates T)
        hzero.symm
        (explicitFormulaRectangleRawSingularCoordinates_zero_mem T)
  | Or.inr (Or.inl hone) =>
      exact Eq.subst
        (motive := fun value : ℂ =>
          value ∈ explicitFormulaRectangleRawSingularCoordinates T)
        hone.symm
        (explicitFormulaRectangleRawSingularCoordinates_one_mem T)
  | Or.inr (Or.inr hzeroData) =>
      let rho : {rho : ℂ // ZetaCompletedZero rho} :=
        explicitFormulaCompletedZeroOfContourZero
          z hzeroData.1 hzeroData.2.1 hzeroData.2.2
      have hcoordinate : completedZeroResidueCoordinate rho = z :=
        explicitFormulaCompletedZeroOfContourZero_residueCoordinate
          z hzeroData.1 hzeroData.2.1 hzeroData.2.2
      have hrhoHeight :
          |(completedZeroResidueCoordinate rho).im| < T :=
        Eq.subst
          (motive := fun value : ℂ => |value.im| < T)
          hcoordinate.symm
          him
      have hrho : rho ∈ explicitFormulaCompletedZeroContourHeightWindow T :=
        (mem_explicitFormulaCompletedZeroContourHeightWindow_iff T rho).mpr
          hrhoHeight
      have hraw :
          completedZeroResidueCoordinate rho ∈
            explicitFormulaRectangleRawSingularCoordinates T :=
        explicitFormulaRectangleRawSingularCoordinates_completedZero_mem T hrho
      exact Eq.subst
        (motive := fun value : ℂ =>
          value ∈ explicitFormulaRectangleRawSingularCoordinates T)
        hcoordinate
        hraw

/-- A horizontal affine line in the raw vertical strip avoids every completed singularity
when its height differs from every raw singular height. -/
theorem explicitFormulaRectangle_horizontalLine_avoidsSingularSet
    (T y : ℝ) (hy : |y| < T)
    (hlevel :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T → y ≠ b.im) :
    ∀ x : ℝ,
      (x : ℂ) + (y : ℂ) * Complex.I ∉
        completedZetaContourIntegrandSingularSet := by
  intro x hsingular
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have him : z.im = y :=
    ofReal_add_mul_I_im x y
  have hzHeight : |z.im| < T :=
    Eq.subst
      (motive := fun value : ℝ => |value| < T)
      him.symm
      hy
  have hzRaw : z ∈ explicitFormulaRectangleRawSingularCoordinates T :=
    explicitFormulaRectangleRawSingularCoordinates_mem_of_singular_abs_im_lt
      T hsingular hzHeight
  exact (hlevel z hzRaw) him.symm

/-- A vertical affine line avoids every completed singularity when its real coordinate
differs from every raw singular real coordinate. -/
theorem explicitFormulaRectangle_verticalLine_avoidsSingularSet
    (T x : ℝ)
    (hlevel :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T → x ≠ b.re) :
    ∀ y : ℝ,
      |y| < T →
        (x : ℂ) + (y : ℂ) * Complex.I ∉
          completedZetaContourIntegrandSingularSet := by
  intro y hy hsingular
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hre : z.re = x :=
    ofReal_add_mul_I_re x y
  have him : z.im = y :=
    ofReal_add_mul_I_im x y
  have hzHeight : |z.im| < T :=
    Eq.subst
      (motive := fun value : ℝ => |value| < T)
      him.symm
      hy
  have hzRaw : z ∈ explicitFormulaRectangleRawSingularCoordinates T :=
    explicitFormulaRectangleRawSingularCoordinates_mem_of_singular_abs_im_lt
      T hsingular hzHeight
  exact (hlevel z hzRaw) hre.symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
