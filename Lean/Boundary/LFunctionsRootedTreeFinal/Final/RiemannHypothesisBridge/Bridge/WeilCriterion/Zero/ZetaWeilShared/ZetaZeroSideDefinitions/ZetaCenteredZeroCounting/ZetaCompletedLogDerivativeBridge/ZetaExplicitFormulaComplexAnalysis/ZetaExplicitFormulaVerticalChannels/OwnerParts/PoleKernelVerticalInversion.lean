import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleSides

/-!
# Pole-kernel vertical inversion targets

This file names the vertical-line inversion objects for the isolated pole
kernels.  The finite-rectangle residue theorems in `CorrectionPoleResidues`
control small punctured contours around the poles; these definitions own the
separate far-vertical-line limits needed by the vertical-channel transport
proofs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The right path of a contour family is the affine vertical line
`F.c + i t`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPole_verticalInversion_rightPath_eq
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) t =
      (F.c : ℂ) + t * Complex.I :=
  rfl

/-- The shifted right path used by the test transform is the affine vertical
line `(F.c - 1/2) + i t`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPole_verticalInversion_shiftedRightPath_eq
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - (1 / 2 : ℂ) =
      ((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I := by
  calc
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - (1 / 2 : ℂ) =
        ((F.c : ℂ) + t * Complex.I) - (1 / 2 : ℂ) := by
      exact congrArg
        (fun z : ℂ => z - (1 / 2 : ℂ))
        (zetaCompletedExplicitFormulaCorrectionRightZeroPole_verticalInversion_rightPath_eq
          F T t)
    _ = ((F.c : ℂ) + t * Complex.I) + -(1 / 2 : ℂ) := by
      exact sub_eq_add_neg ((F.c : ℂ) + t * Complex.I) (1 / 2 : ℂ)
    _ = (F.c : ℂ) + (t * Complex.I + -(1 / 2 : ℂ)) := by
      exact add_assoc (F.c : ℂ) (t * Complex.I) (-(1 / 2 : ℂ))
    _ = (F.c : ℂ) + (-(1 / 2 : ℂ) + t * Complex.I) := by
      exact congrArg
        (fun z : ℂ => (F.c : ℂ) + z)
        (add_comm (t * Complex.I) (-(1 / 2 : ℂ)))
    _ = ((F.c : ℂ) + -(1 / 2 : ℂ)) + t * Complex.I := by
      exact (add_assoc (F.c : ℂ) (-(1 / 2 : ℂ)) (t * Complex.I)).symm
    _ = ((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I := by
      exact congrArg
        (fun z : ℂ => z + t * Complex.I)
        (sub_eq_add_neg (F.c : ℂ) (1 / 2 : ℂ)).symm

/-- The right-face integrand for vertical inversion of the isolated `s = 0`
pole kernel. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) : ℂ :=
  (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)

/-- The right zero-pole vertical-inversion integrand in affine-line normal form. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand_eq_affineLine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand f F T t =
      (-1 / ((F.c : ℂ) + t * Complex.I)) *
        zetaCompletedExplicitFormulaPhi f
          (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
  have hpath :
      zetaCompletedExplicitFormulaRightPath (F.rectangle T) t =
        (F.c : ℂ) + t * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPole_verticalInversion_rightPath_eq
      F T t
  have hshift :
      zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - (1 / 2 : ℂ) =
        ((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPole_verticalInversion_shiftedRightPath_eq
      F T t
  calc
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand f F T t =
        (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) := by
      rfl
    _ =
        (-1 / ((F.c : ℂ) + t * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) := by
      exact congrArg
        (fun z : ℂ =>
          (-1 / z) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        hpath
    _ =
        (-1 / ((F.c : ℂ) + t * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
      exact congrArg
        (fun z : ℂ =>
          (-1 / ((F.c : ℂ) + t * Complex.I)) *
            zetaCompletedExplicitFormulaPhi f z)
        hshift

/-- The scheduled right-face vertical inversion integral for the isolated
`s = 0` pole kernel. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  ∫ t in
      Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand
        f F (h.height_schedule.height u) t

/-- The named scheduled vertical inversion integral is exactly the previously
defined right zero-pole vertical integral at the scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_eq_verticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
        f F h u =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) :=
  rfl

/-- The contour-side value predicted by vertical inversion of the isolated
`s = 0` right pole kernel.

The kernel is `(-1 / s) * Phi_f (s - 1/2)`, so the local contour value samples
`Phi_f (-1/2)`, not `Phi_f 0`.  Any later comparison with the centered
completed correction contribution must be a separate normalization theorem. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue
    (f : ZetaAdmissibleFunction) : ℂ :=
  -(((2 * (Real.pi : ℂ) * Complex.I) *
    (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I)

/-- The raw tangent-contour local residue value at the isolated `s = 0` pole.

The correction kernel is evaluated with the contour shift `s ↦ s - 1 / 2`,
so the finite local Cauchy residue samples `Φ_f (-1/2)`.  This is deliberately
kept separate from the centered completed correction contribution, which is
normalized at `Φ_f 0`. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
    (f : ZetaAdmissibleFunction) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I) *
    (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))

/-- The non-tangent right-vertical value corresponding to the raw tangent
local residue at `s = 0`.

Since the genuine contour boundary carries the vertical tangent factor `I`,
the corresponding real-parameter vertical integral value is multiplication
by `-I`. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue
    (f : ZetaAdmissibleFunction) : ℂ :=
  -(zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f * Complex.I)

/-- The right zero-pole vertical-inversion value unfolds to the shifted local
contour residue transported from tangent to real vertical parameter. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f =
      -(((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I) :=
  rfl

/-- The raw tangent local residue value unfolds to the finite Cauchy residue
normalization at the shifted pole. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) :=
  rfl

/-- The local non-tangent vertical residue value is the raw tangent residue
multiplied by `-I`. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue f =
      -(zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f * Complex.I) :=
  rfl

/-- The local right vertical zero-pole value cancels the raw tangent residue
after multiplication by the vertical tangent factor `I`. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidue_add_tangent_mul_I
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue f +
        zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f *
          Complex.I =
      0 := by
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue f +
        zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f *
          Complex.I =
        -(zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f *
            Complex.I) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f *
            Complex.I := by
      exact congrArg
        (fun z : ℂ =>
          z +
            zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f *
              Complex.I)
        (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue_eq f)
    _ = 0 := by
      exact neg_add_cancel
        (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f *
          Complex.I)

/-- The named right vertical inversion value is the local vertical residue
normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue_eq_localVerticalResidue
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f =
      zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue f := by
  calc
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f =
        -(((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I) := by
      exact zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue_eq f
    _ =
        -(zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f *
          Complex.I) := by
      exact congrArg
        (fun z : ℂ => -(z * Complex.I))
        (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue_eq f).symm
    _ = zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue f := by
      exact (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue_eq f).symm

/-- The named right vertical inversion value cancels the local tangent residue
after multiplication by the vertical tangent factor `I`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue_add_tangentResidue_mul_I
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f +
        zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f *
          Complex.I =
      0 := by
  exact Eq.trans
    (congrArg
      (fun z : ℂ =>
        z +
          zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f *
            Complex.I)
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue_eq_localVerticalResidue
        f))
    (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidue_add_tangent_mul_I
      f)

/-- Transport a proved scheduled vertical-inversion limit back to the existing
right zero-pole vertical integral name. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_of_scheduledVerticalInversion_value
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (value : ℂ)
    (hinversion :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
            f F h u)
        atTop
        (𝓝 value)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 value) := by
  have hfun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
          f F h u) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)) := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_eq_verticalIntegral
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 value))
    hfun
    hinversion

/-- Transport a proved scheduled vertical-inversion limit back to the existing
right zero-pole vertical integral name in the residue-valued normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_of_scheduledVerticalInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hinversion :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
            f F h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_of_scheduledVerticalInversion_value
      f F h
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)
      hinversion

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
