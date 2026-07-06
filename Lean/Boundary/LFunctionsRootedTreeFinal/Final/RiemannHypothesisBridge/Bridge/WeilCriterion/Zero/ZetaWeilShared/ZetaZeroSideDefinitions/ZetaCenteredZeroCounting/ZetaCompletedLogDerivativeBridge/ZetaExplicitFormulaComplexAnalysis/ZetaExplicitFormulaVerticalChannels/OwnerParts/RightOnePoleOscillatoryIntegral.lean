import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleResidues

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

/-- Time-side right one-pole Cauchy/Laplace projection value for the completed
zeta admissible test transform. -/
noncomputable def zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
    (f : ZetaAdmissibleFunction) (c : ℝ) : ℂ :=
  Boundary.zetaLaplaceTransform_rightOnePoleCauchyProjectionValue
    f.toZetaTestFunction' c

/-- Generic residue-free Cauchy/Laplace projection estimate for the right
one-pole kernel on a fixed line.

This is the analytic Fourier/Laplace core: after expanding `Φ_f` as the
Laplace transform of the compactly supported time kernel, the multiplier
`(c - 1 + it)⁻¹` is the boundary value of a one-sided exponential kernel, and
the scheduled symmetric-window integral has inverse-quadratic decay on the
residue-free side. -/
theorem zetaCompletedExplicitFormula_rightOnePoleCauchyLaplaceProjection_eventual_inverseQuadratic_to_value
    (f : ZetaAdmissibleFunction) (c : ℝ) (hc : 1 < c)
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖(∫ t in Set.Icc (-(height u)) (height u),
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                Boundary.zetaLaplaceTransform f.toZetaTestFunction'
                  (((c : ℂ) + t * Complex.I) - 1 / 2)) -
            zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f c‖
            ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  exact
    Boundary.zetaLaplaceTransform_rightOnePoleCauchyProjection_eventual_inverseQuadratic_to_value
      f c hc height hcofinal

/-- The scheduled right-face off-pole `s = 1` correction integral, isolated as
the object controlled by the contour-cancellation argument. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  ∫ t in
      Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      (-1 /
          (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2)

/-- Definition transport from the explicit right-face off-pole correction
integral to its scheduled owner name. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledOscillatoryIntegral_eq_named
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (∫ t in
        Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        (-1 /
            (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
        f F h u :=
  rfl

/-- Raw fixed-line residue-free inverse-quadratic estimate for the `s = 1`
right correction kernel.

This is the scalar analytic sink beneath the scheduled right one-pole
oscillatory estimate.  It is independent of the left residue branch: the line
has real part `c > 1`, hence it stays a fixed positive distance from the pole
at `1`, and the estimate is the residue-free Cauchy/Laplace oscillatory tail
bound on expanding symmetric windows. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_rawFixedLineInterval_eventual_inverseQuadratic_to_value
    (f : ZetaAdmissibleFunction) (c : ℝ) (hc : 1 < c)
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖(∫ t in Set.Icc (-(height u)) (height u),
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                zetaCompletedExplicitFormulaPhi f
                  (((c : ℂ) + t * Complex.I) - 1 / 2)) -
            zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f c‖
            ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  match
    zetaCompletedExplicitFormula_rightOnePoleCauchyLaplaceProjection_eventual_inverseQuadratic_to_value
      f c hc height hcofinal with
  | ⟨MR, hMRpos, hMR⟩ =>
      refine ⟨MR, hMRpos, ?_⟩
      exact hMR.mono
        (fun u hu =>
          let T : ℝ := height u
          have hphi :
              (fun t : ℝ =>
                (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                  zetaCompletedExplicitFormulaPhi f
                    (((c : ℂ) + t * Complex.I) - 1 / 2)) =
              (fun t : ℝ =>
                (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                  Boundary.zetaLaplaceTransform f.toZetaTestFunction'
                    (((c : ℂ) + t * Complex.I) - 1 / 2)) := by
            funext t
            exact congrArg
              (fun z : ℂ =>
                (-1 / (((c : ℂ) + t * Complex.I) - 1)) * z)
              (congrFun (zetaCompletedExplicitFormulaPhi_eq_laplace f)
                (((c : ℂ) + t * Complex.I) - 1 / 2))
          have hintegral :
              (∫ t in Set.Icc (-T) T,
                (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                  zetaCompletedExplicitFormulaPhi f
                    (((c : ℂ) + t * Complex.I) - 1 / 2)) =
              (∫ t in Set.Icc (-T) T,
                (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                  Boundary.zetaLaplaceTransform f.toZetaTestFunction'
                    (((c : ℂ) + t * Complex.I) - 1 / 2)) := by
            exact congrArg
              (fun φ : ℝ → ℂ => ∫ t in Set.Icc (-T) T, φ t)
              hphi
          by
            exact
              Eq.subst
                (motive := fun z : ℂ =>
                  ‖z - zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f c‖
                    ≤ MR * (1 + ‖T‖) ^ (-(2 : ℤ)))
                hintegral.symm
                hu)

/-- Transport the raw fixed-line right one-pole estimate to the scheduled
right-path integral. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_eventual_inverseQuadratic_to_value_of_rawFixedLine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
              f F h u -
            zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c‖
            ≤ MR *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match
    zetaCompletedExplicitFormulaCorrectionRightOnePole_rawFixedLineInterval_eventual_inverseQuadratic_to_value
      f F.c F.c_gt_one
      (fun u : ℝ => (F.rectangle (h.height_schedule.height u)).T)
      (by
        exact h.height_schedule.cofinal) with
  | ⟨MR, hMRpos, hMR⟩ =>
      refine ⟨MR, hMRpos, ?_⟩
      exact hMR.mono
        (fun u hu =>
          let T : ℝ := (F.rectangle (h.height_schedule.height u)).T
          have hline :
              (fun t : ℝ =>
                (-1 /
                    (zetaCompletedExplicitFormulaRightPath
                        (F.rectangle (h.height_schedule.height u)) t - 1)) *
                  zetaCompletedExplicitFormulaPhi f
                    (zetaCompletedExplicitFormulaRightPath
                        (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
              (fun t : ℝ =>
                (-1 / (((F.c : ℂ) + t * Complex.I) - 1)) *
                  zetaCompletedExplicitFormulaPhi f
                    (((F.c : ℂ) + t * Complex.I) - 1 / 2)) := by
            funext t
            have hpath :
                zetaCompletedExplicitFormulaRightPath
                    (F.rectangle (h.height_schedule.height u)) t =
                  (F.c : ℂ) + t * Complex.I := by
              rfl
            calc
              (-1 /
                    (zetaCompletedExplicitFormulaRightPath
                        (F.rectangle (h.height_schedule.height u)) t - 1)) *
                  zetaCompletedExplicitFormulaPhi f
                    (zetaCompletedExplicitFormulaRightPath
                        (F.rectangle (h.height_schedule.height u)) t - 1 / 2) =
                  (-1 / (((F.c : ℂ) + t * Complex.I) - 1)) *
                    zetaCompletedExplicitFormulaPhi f
                      (zetaCompletedExplicitFormulaRightPath
                        (F.rectangle (h.height_schedule.height u)) t - 1 / 2) := by
                exact congrArg
                  (fun z : ℂ =>
                    (-1 / (z - 1)) *
                      zetaCompletedExplicitFormulaPhi f
                        (zetaCompletedExplicitFormulaRightPath
                          (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
                  hpath
              _ =
                  (-1 / (((F.c : ℂ) + t * Complex.I) - 1)) *
                    zetaCompletedExplicitFormulaPhi f
                      (((F.c : ℂ) + t * Complex.I) - 1 / 2) := by
                exact congrArg
                  (fun z : ℂ =>
                    (-1 / (((F.c : ℂ) + t * Complex.I) - 1)) *
                      zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
                  hpath
          have hintegral :
              zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
                  f F h u =
                ∫ t in Set.Icc (-T) T,
                  (-1 / (((F.c : ℂ) + t * Complex.I) - 1)) *
                    zetaCompletedExplicitFormulaPhi f
                      (((F.c : ℂ) + t * Complex.I) - 1 / 2) := by
            calc
              zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
                  f F h u =
                  ∫ t in Set.Icc (-T) T,
                    (-1 /
                        (zetaCompletedExplicitFormulaRightPath
                            (F.rectangle (h.height_schedule.height u)) t - 1)) *
                      zetaCompletedExplicitFormulaPhi f
                        (zetaCompletedExplicitFormulaRightPath
                            (F.rectangle (h.height_schedule.height u)) t - 1 / 2) := by
                rfl
              _ =
                  ∫ t in Set.Icc (-T) T,
                    (-1 / (((F.c : ℂ) + t * Complex.I) - 1)) *
                      zetaCompletedExplicitFormulaPhi f
                        (((F.c : ℂ) + t * Complex.I) - 1 / 2) := by
                exact congrArg
                  (fun φ : ℝ → ℂ => ∫ t in Set.Icc (-T) T, φ t)
                  hline
          by
            exact
              Eq.subst
                (motive := fun z : ℂ =>
                  ‖z - zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c‖
                    ≤ MR * (1 + ‖T‖) ^ (-(2 : ℤ)))
                hintegral.symm
                hu)

/-- Direct Cauchy/Laplace projection estimate for the scheduled right `s = 1`
correction face.

This theorem belongs with the scheduled oscillatory integral itself.  Its proof
is the residue-free right-contour estimate, using the fixed off-pole
displacement from `s = 1`, the finite horizontal-edge decay, and the
scheduled height normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_eventual_inverseQuadratic_to_value_ownerOscillatory
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
              f F h u -
            zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c‖
            ≤ MR *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_eventual_inverseQuadratic_to_value_of_rawFixedLine
      f F h

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
