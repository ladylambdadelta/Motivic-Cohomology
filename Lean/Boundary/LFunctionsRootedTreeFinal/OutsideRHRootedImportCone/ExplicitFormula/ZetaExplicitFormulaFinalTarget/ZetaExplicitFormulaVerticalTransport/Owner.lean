import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.Owner

/-!
# Boundary explicit-formula vertical transport

This file owns the vertical-channel contour transport theorem used by the
final explicit-formula assembly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The vertical side difference along a contour family. -/
noncomputable def explicitFormulaFamilyVerticalDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)

/-- The vertical-channel transport remainder along a contour family. -/
noncomputable def explicitFormulaFamilyVerticalTransportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  explicitFormulaFamilyVerticalDifference f F T -
    zetaCompletedExplicitFormulaBoundarySumAnalytic f

/-- The vertical family is its analytic boundary value plus the vertical-transport
remainder. -/
theorem explicitFormulaFamilyVerticalDifference_eq_boundary_add_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyVerticalDifference f F T =
      zetaCompletedExplicitFormulaBoundarySumAnalytic f +
        explicitFormulaFamilyVerticalTransportRemainder f F T := by
  let V : ℂ := explicitFormulaFamilyVerticalDifference f F T
  let B : ℂ := zetaCompletedExplicitFormulaBoundarySumAnalytic f
  change V = B + (V - B)
  calc
    V = V + 0 := by
      exact (add_zero V).symm
    _ = V + (-B + B) := by
      exact congrArg (fun x : ℂ => V + x) (neg_add_cancel B).symm
    _ = (V + -B) + B := by
      exact (add_assoc V (-B) B).symm
    _ = B + (V + -B) := by
      exact add_comm (V + -B) B
    _ = B + (V - B) := by
      exact congrArg (fun x : ℂ => B + x) (sub_eq_add_neg V B).symm

/-- If the vertical side difference converges to the analytic boundary scalar, then
the vertical-transport remainder tends to zero. -/
theorem explicitFormulaFamilyVerticalTransportRemainder_tendsto_zero_of_boundaryLimit
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hvertical :
      Tendsto
        (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f))) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyVerticalTransportRemainder f F T)
      atTop
      (𝓝 0) := by
  have hconst :
      Tendsto
        (fun _T : ℝ => zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun T : ℝ =>
          explicitFormulaFamilyVerticalDifference f F T -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaBoundarySumAnalytic f -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    hvertical.sub hconst
  have htarget :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f -
          zetaCompletedExplicitFormulaBoundarySumAnalytic f =
        0 := by
    exact sub_self _
  have hpointwise :
      (fun T : ℝ => explicitFormulaFamilyVerticalTransportRemainder f F T) =
        (fun T : ℝ =>
          explicitFormulaFamilyVerticalDifference f F T -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
    funext T
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            explicitFormulaFamilyVerticalDifference f F T -
              zetaCompletedExplicitFormulaBoundarySumAnalytic f)
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- Owner vertical-limit theorem: along a scheduled vertically regular contour realization,
the vertical side difference converges to the analytic prime/archimedean/correction boundary
scalar. -/
theorem explicitFormulaFamilyVerticalDifference_tendsto_boundarySum_core_ownerVerticalTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalDifference f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  dsimp
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaRightLineIntegral f
              (F.toContourFamily.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
              (F.toContourFamily.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_ownerVerticalDecomposition
      f F hSchedule
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalDifference f F.toContourFamily
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaRightLineIntegral f
              (F.toContourFamily.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
              (F.toContourFamily.rectangle (h.height_schedule.height u))) := by
    funext u
    rfl
  exact Eq.subst
    (motive := fun u : ℝ → ℂ =>
      Tendsto u atTop (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
    hpointwise.symm
    hvertical

/-- Owner vertical-transport theorem: along a scheduled vertically regular contour
realization, the named vertical-transport remainder tends to zero. -/
theorem explicitFormulaFamilyVerticalTransportRemainder_tendsto_zero_ownerVerticalTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalTransportRemainder f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  dsimp
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hboundary :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalDifference f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    explicitFormulaFamilyVerticalDifference_tendsto_boundarySum_core_ownerVerticalTransport
      f F hSchedule
  have hconst :
      Tendsto
        (fun _u : ℝ => zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalDifference f F.toContourFamily
              (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaBoundarySumAnalytic f -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    hboundary.sub hconst
  have htarget :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f -
          zetaCompletedExplicitFormulaBoundarySumAnalytic f =
        0 := by
    exact sub_self _
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalTransportRemainder f F.toContourFamily
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalDifference f F.toContourFamily
              (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
    funext u
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaFamilyVerticalDifference f F.toContourFamily
                (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaBoundarySumAnalytic f)
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- If the unscheduled vertical side difference has a boundary limit, its unscheduled
transport remainder tends to zero. -/
theorem explicitFormulaFamilyVerticalTransportRemainder_tendsto_zero_of_boundaryLimit_unscheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hvertical :
      Tendsto
        (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f))) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyVerticalTransportRemainder f F T)
      atTop
      (𝓝 0) := by
  exact explicitFormulaFamilyVerticalTransportRemainder_tendsto_zero_of_boundaryLimit
    f F hvertical

/-- If the vertical-transport remainder tends to zero, then the vertical side difference
converges to the analytic boundary scalar. -/
theorem explicitFormulaFamilyVerticalDifference_tendsto_boundarySum_of_remainderLimit
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hremainder :
      Tendsto
        (fun T : ℝ => explicitFormulaFamilyVerticalTransportRemainder f F T)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  have hconst :
      Tendsto
        (fun _T : ℝ => zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaBoundarySumAnalytic f +
            explicitFormulaFamilyVerticalTransportRemainder f F T)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f + 0)) :=
    hconst.add hremainder
  have htarget :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f + 0 =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
    add_zero _
  have hpointwise :
      (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T) =
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaBoundarySumAnalytic f +
            explicitFormulaFamilyVerticalTransportRemainder f F T) := by
    funext T
    exact explicitFormulaFamilyVerticalDifference_eq_boundary_add_transportRemainder f F T
  exact Eq.subst
    (motive := fun u : ℝ → ℂ =>
      Tendsto u atTop (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            zetaCompletedExplicitFormulaBoundarySumAnalytic f +
              explicitFormulaFamilyVerticalTransportRemainder f F T)
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Owner vertical-transport theorem: along a scheduled vertically regular contour
realization, the vertical side difference converges to the analytic
prime/archimedean/correction boundary scalar. -/
theorem explicitFormulaFamilyVerticalDifference_tendsto_boundarySum_ownerVerticalTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalDifference f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  dsimp
  exact explicitFormulaFamilyVerticalDifference_tendsto_boundarySum_core_ownerVerticalTransport
    f F hSchedule

/-- The vertical-channel transport remainder vanishes along the scheduled contour
realization. -/
theorem explicitFormulaFamilyVerticalTransportRemainder_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalTransportRemainder f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  dsimp
  exact explicitFormulaFamilyVerticalTransportRemainder_tendsto_zero_ownerVerticalTransport
    f F hSchedule

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
