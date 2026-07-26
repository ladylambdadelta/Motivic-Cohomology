import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.NormalizedContourProjection

/-!
# Explicit-formula finite rectangle residues

This owner layer contains finite-rectangle residue equalities, scheduled avoidance, and residue-window error transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Scheduled finite-rectangle residue equality for an explicit-formula
contour family.  This is the generic finite-residue owner surface; downstream
files specialize it to their chosen probe and height schedule. -/
def zetaCompletedScheduledFiniteResidueEquality
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) : Prop :=
  ∃ N : ℕ,
    ∀ u : ℝ,
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroContourHeightWindowResidueSum f
          (h.height_schedule.height u)

/-- Pointwise equality at every scheduled height gives the packaged scheduled
finite-residue equality.  The witness `0` carries no analytic content; all
residue-theoretic content is the supplied pointwise equality. -/
theorem zetaCompletedScheduledFiniteResidueEquality_of_heightWindowResidueEquality
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    zetaCompletedScheduledFiniteResidueEquality f F h :=
  Exists.intro 0 hfinite

/-- The scheduled residue sum is the completed-zero height-window residue sum
at the scheduled height. -/
theorem explicitFormulaScheduledRectangleResidueSum_eq_heightWindowResidueSum
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (u : ℝ) :
    explicitFormulaScheduledRectangleResidueSum f F h u =
      explicitFormulaCompletedZeroContourHeightWindowResidueSum f
        (h.height_schedule.height u) :=
  Eq.refl _

/-- Vanishing of the scheduled residue-equality error gives the pointwise
height-window residue equality. -/
theorem zetaCompletedScheduledHeightWindowResidueEquality_of_residueEqualityError_eq_zero
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (u : ℝ)
    (hzero :
      explicitFormulaScheduledRectangleResidueEqualityError f F h u = 0) :
    zetaCompletedExplicitFormulaContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      explicitFormulaCompletedZeroContourHeightWindowResidueSum f
        (h.height_schedule.height u) :=
  Eq.trans
    (sub_eq_zero.mp hzero)
    (explicitFormulaScheduledRectangleResidueSum_eq_heightWindowResidueSum
      f F h u)

/-- Pointwise vanishing of the scheduled residue-equality error gives
height-window residue equality at every scheduled height. -/
theorem zetaCompletedScheduledHeightWindowResidueEquality_of_residueEqualityError_eq_zero_all
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hzero :
      ∀ u : ℝ,
        explicitFormulaScheduledRectangleResidueEqualityError f F h u = 0) :
    ∀ u : ℝ,
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroContourHeightWindowResidueSum f
          (h.height_schedule.height u) :=
  fun u =>
    zetaCompletedScheduledHeightWindowResidueEquality_of_residueEqualityError_eq_zero
      f F h u (hzero u)

/-- Pointwise vanishing of the scheduled residue-equality error gives the
packaged scheduled finite-residue equality. -/
theorem zetaCompletedScheduledFiniteResidueEquality_of_residueEqualityError_eq_zero
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hzero :
      ∀ u : ℝ,
        explicitFormulaScheduledRectangleResidueEqualityError f F h u = 0) :
    zetaCompletedScheduledFiniteResidueEquality f F h :=
  zetaCompletedScheduledFiniteResidueEquality_of_heightWindowResidueEquality
    f
    F
    h
    (zetaCompletedScheduledHeightWindowResidueEquality_of_residueEqualityError_eq_zero_all
      f F h hzero)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
