import Boundary.LFunctionsRootedTreeFinal.OutsideRHRootedImportCone.ExplicitFormula.ZetaCompletedExplicitFormulaAssembly.ZetaExplicitFormulaBoundaryTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.Owner

/-!
# Boundary explicit-formula residue scalar

This file owns the residue-shaped scalar name used by the contour-shift
assembly. The comparison with the analytic boundary scalar is proved in the
final contour-shift target by uniqueness of the residue-side and vertical-side
limits.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The completed residue boundary sum attached to an admissible probe. -/
noncomputable def zetaCompletedResidueBoundarySum (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedZeroKreinGram f

/-- The complex completed residue boundary sum attached to an admissible probe. -/
noncomputable def zetaCompletedResidueBoundarySumComplex
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedZeroSideComplex f

/-- The zero-side Krein form is the completed residue boundary sum. -/
theorem zetaCompletedZeroKreinGram_eq_residueBoundarySum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      zetaCompletedResidueBoundarySum f := by
  rfl

/-- The real completed residue boundary scalar is the real part of the complex residue
boundary sum. -/
theorem zetaCompletedResidueBoundarySum_eq_complex_re
    (f : ZetaAdmissibleFunction) :
    zetaCompletedResidueBoundarySum f =
      Complex.re (zetaCompletedResidueBoundarySumComplex f) := by
  rfl

/-- The contour integral along a contour family. -/
noncomputable def explicitFormulaFamilyContourIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T)

/-- The residue-side contour remainder along a contour family. -/
noncomputable def explicitFormulaFamilyResidueRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  explicitFormulaFamilyContourIntegral f F T -
    zetaCompletedResidueBoundarySumComplex f

/-- The contour family is its residue boundary value plus the residue-side remainder. -/
theorem explicitFormulaFamilyContourIntegral_eq_residue_add_remainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyContourIntegral f F T =
      zetaCompletedResidueBoundarySumComplex f +
        explicitFormulaFamilyResidueRemainder f F T := by
  let C : ℂ := explicitFormulaFamilyContourIntegral f F T
  let R : ℂ := zetaCompletedResidueBoundarySumComplex f
  unfold explicitFormulaFamilyResidueRemainder
  change C = R + (C - R)
  calc
    C = C + 0 := by
      exact (add_zero C).symm
    _ = C + (-R + R) := by
      exact congrArg (fun x : ℂ => C + x) (neg_add_cancel R).symm
    _ = (C + -R) + R := by
      exact (add_assoc C (-R) R).symm
    _ = R + (C + -R) := by
      exact add_comm (C + -R) R
    _ = R + (C - R) := by
      exact congrArg (fun x : ℂ => R + x) (sub_eq_add_neg C R).symm

/-- If the contour integral converges to the completed residue boundary scalar, then
the residue-side contour remainder tends to zero. -/
theorem explicitFormulaFamilyResidueRemainder_tendsto_zero_of_contourLimit
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hcontour :
      Tendsto
        (fun T : ℝ => explicitFormulaFamilyContourIntegral f F T)
        atTop
        (𝓝 (zetaCompletedResidueBoundarySumComplex f))) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyResidueRemainder f F T)
      atTop
      (𝓝 0) := by
  have hconst :
      Tendsto
        (fun _T : ℝ => zetaCompletedResidueBoundarySumComplex f)
        atTop
        (𝓝 (zetaCompletedResidueBoundarySumComplex f)) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun T : ℝ =>
          explicitFormulaFamilyContourIntegral f F T -
            zetaCompletedResidueBoundarySumComplex f)
        atTop
        (𝓝
          (zetaCompletedResidueBoundarySumComplex f -
            zetaCompletedResidueBoundarySumComplex f)) :=
    hcontour.sub hconst
  have htarget :
      zetaCompletedResidueBoundarySumComplex f -
          zetaCompletedResidueBoundarySumComplex f =
        0 := by
    exact sub_self _
  have hpointwise :
      (fun T : ℝ => explicitFormulaFamilyResidueRemainder f F T) =
        (fun T : ℝ =>
          explicitFormulaFamilyContourIntegral f F T -
            zetaCompletedResidueBoundarySumComplex f) := by
    funext T
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            explicitFormulaFamilyContourIntegral f F T -
              zetaCompletedResidueBoundarySumComplex f)
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- Owner residue theorem for the completed explicit-formula contour family.

This is the residue-side limit theorem: finite rectangle residue calculus, with zeros
counted by analytic multiplicity, converges to the completed residue boundary scalar. -/
theorem explicitFormulaFamilyContourIntegral_tendsto_residueBoundarySum_core_ownerResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyContourIntegral f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedResidueBoundarySumComplex f)) := by
  have hzero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)) :=
    zetaCompletedExplicitFormulaContourIntegral_tendsto_zeroSideComplex_core_ownerContourResidueTheorem
      f F h
  have htarget :
      zetaCompletedZeroSideComplex f =
        zetaCompletedResidueBoundarySumComplex f := by
    rfl
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyContourIntegral f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u))) := by
    funext u
    rfl
  exact Eq.subst
    (motive := fun u : ℝ → ℂ =>
      Tendsto u atTop (𝓝 (zetaCompletedResidueBoundarySumComplex f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaContourIntegral f
              (F.rectangle (h.height_schedule.height u)))
          atTop
          (𝓝 z))
      htarget
      hzero)

/-- Owner residue theorem for the completed explicit-formula contour family.

This is the residue-side remainder theorem derived from the direct residue-limit theorem. -/
theorem explicitFormulaFamilyResidueRemainder_tendsto_zero_ownerResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyResidueRemainder f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  dsimp
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hcontour :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyContourIntegral f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedResidueBoundarySumComplex f)) :=
    explicitFormulaFamilyContourIntegral_tendsto_residueBoundarySum_core_ownerResidueTheorem
      f F.toContourFamily h
  have hconst :
      Tendsto
        (fun _u : ℝ => zetaCompletedResidueBoundarySumComplex f)
        atTop
        (𝓝 (zetaCompletedResidueBoundarySumComplex f)) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyContourIntegral f F.toContourFamily
              (h.height_schedule.height u) -
            zetaCompletedResidueBoundarySumComplex f)
        atTop
        (𝓝 (zetaCompletedResidueBoundarySumComplex f -
          zetaCompletedResidueBoundarySumComplex f)) :=
    hcontour.sub hconst
  have htarget :
      zetaCompletedResidueBoundarySumComplex f -
          zetaCompletedResidueBoundarySumComplex f =
        0 := by
    exact sub_self _
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyResidueRemainder f F.toContourFamily
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyContourIntegral f F.toContourFamily
              (h.height_schedule.height u) -
            zetaCompletedResidueBoundarySumComplex f) := by
    funext u
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaFamilyContourIntegral f F.toContourFamily
                (h.height_schedule.height u) -
              zetaCompletedResidueBoundarySumComplex f)
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- If the residue-side contour remainder tends to zero, then the contour integral
converges to the completed residue boundary scalar. -/
theorem explicitFormulaFamilyContourIntegral_tendsto_residueBoundarySum_of_remainderLimit
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hremainder :
      Tendsto
        (fun T : ℝ => explicitFormulaFamilyResidueRemainder f F T)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyContourIntegral f F T)
      atTop
      (𝓝 (zetaCompletedResidueBoundarySumComplex f)) := by
  have hconst :
      Tendsto
        (fun _T : ℝ => zetaCompletedResidueBoundarySumComplex f)
        atTop
        (𝓝 (zetaCompletedResidueBoundarySumComplex f)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedResidueBoundarySumComplex f +
            explicitFormulaFamilyResidueRemainder f F T)
        atTop
        (𝓝 (zetaCompletedResidueBoundarySumComplex f + 0)) :=
    hconst.add hremainder
  have htarget :
      zetaCompletedResidueBoundarySumComplex f + 0 =
        zetaCompletedResidueBoundarySumComplex f :=
    add_zero _
  have hfun :
      (fun T : ℝ => explicitFormulaFamilyContourIntegral f F T) =
        fun T : ℝ =>
          zetaCompletedResidueBoundarySumComplex f +
            explicitFormulaFamilyResidueRemainder f F T := by
    funext T
    exact explicitFormulaFamilyContourIntegral_eq_residue_add_remainder f F T
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedResidueBoundarySumComplex f)))
    hfun.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            zetaCompletedResidueBoundarySumComplex f +
              explicitFormulaFamilyResidueRemainder f F T)
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Owner residue theorem for the completed explicit-formula contour family.

This is the residue-side limit theorem: the finite rectangle residue calculus, with zeros
counted by analytic multiplicity, converges to the completed residue boundary scalar. -/
theorem explicitFormulaFamilyContourIntegral_tendsto_residueBoundarySum_ownerResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyContourIntegral f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedResidueBoundarySumComplex f)) := by
  dsimp
  exact explicitFormulaFamilyContourIntegral_tendsto_residueBoundarySum_core_ownerResidueTheorem
    f F.toContourFamily
    (explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule)

/-- The residue-side contour remainder vanishes along the contour family. -/
theorem explicitFormulaFamilyResidueRemainder_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyResidueRemainder f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  dsimp
  exact explicitFormulaFamilyResidueRemainder_tendsto_zero_ownerResidueTheorem f F hSchedule

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
