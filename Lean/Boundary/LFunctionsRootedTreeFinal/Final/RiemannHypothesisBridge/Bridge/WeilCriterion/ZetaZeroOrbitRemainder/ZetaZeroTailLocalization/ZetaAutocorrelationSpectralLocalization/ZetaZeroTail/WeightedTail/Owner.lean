import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.TailSummability.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralLinearity
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Completed-zero weighted tail mass

This file connects analytic zero-side summability to the finite-mass carrier of
the completed-zero coordinate map.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
open scoped ENNReal

/-- The completed-zero side-coordinate family belongs to discrete `ℓ¹` under the
analytic zero-side summability hypotheses. -/
theorem memℓp_zetaCompletedZeroSideCoordinate_one
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction) :
    Memℓp (zetaCompletedZeroSideCoordinateLinearMap f) (1 : ℝ≥0∞) := by
  have hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f) :=
    summable_zetaZeroSideContribution
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      hfinite
      hpartialLeft
      hcompactBoundary
      f
  have hnorm :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          ‖zetaZeroSideContribution (ρ : ℂ) f‖) :=
    hsum.norm
  have hpower :
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        ‖zetaCompletedZeroSideCoordinateLinearMap f ρ‖ ^
          (1 : ℝ≥0∞).toReal) =
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          ‖zetaZeroSideContribution (ρ : ℂ) f‖) := by
    funext ρ
    calc
      ‖zetaCompletedZeroSideCoordinateLinearMap f ρ‖ ^
          (1 : ℝ≥0∞).toReal =
          ‖zetaZeroSideContribution (ρ : ℂ) f‖ ^
            (1 : ℝ≥0∞).toReal := by
              exact congrArg
                (fun x : ℝ => x ^ (1 : ℝ≥0∞).toReal)
                (congrArg norm
                  (zetaCompletedZeroSideCoordinateLinearMap_apply f ρ))
      _ = ‖zetaZeroSideContribution (ρ : ℂ) f‖ ^ (1 : ℝ) := by
            exact congrArg
              (fun x : ℝ => ‖zetaZeroSideContribution (ρ : ℂ) f‖ ^ x)
              ENNReal.one_toReal
      _ = ‖zetaZeroSideContribution (ρ : ℂ) f‖ := by
            exact Real.rpow_one (‖zetaZeroSideContribution (ρ : ℂ) f‖)
  have hpowerSummable :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          ‖zetaCompletedZeroSideCoordinateLinearMap f ρ‖ ^
            (1 : ℝ≥0∞).toReal) :=
    Eq.mpr (congrArg Summable hpower) hnorm
  exact memℓp_gen hpowerSummable

/-- Every two-variable convolution-pair coordinate family belongs to discrete
`ℓ¹` under the same analytic summability hypotheses. -/
theorem memℓp_zetaCompletedZeroConvolutionPairSideCoordinate_one
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f h : ZetaAdmissibleFunction) :
    Memℓp
      (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
        zetaCompletedZeroConvolutionPairSideCoordinate f h rho)
      (1 : ℝ≥0∞) := by
  have hpair :
      Memℓp
        (zetaCompletedZeroSideCoordinateLinearMap (convolutionPair f h))
        (1 : ℝ≥0∞) :=
    memℓp_zetaCompletedZeroSideCoordinate_one
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      hfinite
      hpartialLeft
      hcompactBoundary
      (convolutionPair f h)
  have hcoordinate :
      (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
        zetaCompletedZeroConvolutionPairSideCoordinate f h rho) =
        zetaCompletedZeroSideCoordinateLinearMap (convolutionPair f h) := by
    funext rho
    exact
      Eq.trans
        (zetaCompletedZeroConvolutionPairSideCoordinate_eq f h rho)
        (zetaCompletedZeroSideCoordinateLinearMap_apply
          (convolutionPair f h) rho).symm
  exact
    Eq.mpr
      (congrArg
        (fun coordinate : {rho : ℂ // ZetaCompletedZero rho} → ℂ =>
          Memℓp coordinate (1 : ℝ≥0∞))
      hcoordinate)
      hpair

/-- The diagonal autocorrelation coordinate family is the diagonal case of the
summable convolution-pair coordinate family. -/
theorem memℓp_zetaCompletedZeroAutocorrelationSideCoordinate_one
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction) :
    Memℓp
      (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
        zetaCompletedZeroAutocorrelationSideCoordinate f rho)
      (1 : ℝ≥0∞) := by
  have hpair :
      Memℓp
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaCompletedZeroConvolutionPairSideCoordinate f f rho)
        (1 : ℝ≥0∞) :=
    memℓp_zetaCompletedZeroConvolutionPairSideCoordinate_one
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      hfinite
      hpartialLeft
      hcompactBoundary
      f f
  have hcoordinate :
      (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
        zetaCompletedZeroConvolutionPairSideCoordinate f f rho) =
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaCompletedZeroAutocorrelationSideCoordinate f rho) := by
    funext rho
    exact zetaCompletedZeroConvolutionPairSideCoordinate_self f rho
  exact
    Eq.mp
      (congrArg
        (fun coordinate : {rho : ℂ // ZetaCompletedZero rho} → ℂ =>
          Memℓp coordinate (1 : ℝ≥0∞))
        hcoordinate)
      hpair

/-- The analytic completed-zero side-coordinate map with values in discrete `ℓ¹`. -/
noncomputable def zetaCompletedZeroSideCoordinateL1LinearMap
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ZetaAdmissibleFunction →ₗ[ℂ]
      lp (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ) (1 : ℝ≥0∞) where
  toFun := fun f =>
    ⟨zetaCompletedZeroSideCoordinateLinearMap f,
      memℓp_zetaCompletedZeroSideCoordinate_one
        hbranch
        hpartialOneTwo
        hcompactOneTwo
        hfinite
        hpartialLeft
        hcompactBoundary
        f⟩
  map_add' := fun f g => by
    apply lp.ext
    funext ρ
    exact zetaZeroSideContribution_add (ρ : ℂ) f g
  map_smul' := fun c f => by
    apply lp.ext
    funext ρ
    exact zetaZeroSideContribution_smul (ρ : ℂ) c f

/-- The `ℓ¹` coordinate map evaluates to the completed-zero side contribution. -/
theorem zetaCompletedZeroSideCoordinateL1LinearMap_apply
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch
        hpartialOneTwo
        hcompactOneTwo
        hfinite
        hpartialLeft
        hcompactBoundary
        f
        ρ =
      zetaZeroSideContribution (ρ : ℂ) f := by
  exact zetaCompletedZeroSideCoordinateLinearMap_apply f ρ

/-- Evaluation at a completed-zero coordinate is continuous on discrete `ℓ¹`. -/
theorem continuous_zetaCompletedZeroSideCoordinateL1_eval
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    Continuous
      (fun x : lp (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ) (1 : ℝ≥0∞) =>
        x ρ) := by
  exact
    (continuous_apply ρ).comp
      (lp.uniformContinuous_coe.continuous)

/-- Evaluation on a finite completed-zero coordinate window is continuous on discrete `ℓ¹`. -/
theorem continuous_zetaCompletedZeroSideCoordinateL1_finiteEvaluation
    (S : Finset {ρ : ℂ // ZetaCompletedZero ρ}) :
    Continuous
      (fun x : lp (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ) (1 : ℝ≥0∞) =>
        fun ρ : S => x (ρ : {ρ : ℂ // ZetaCompletedZero ρ})) := by
  exact
    continuous_pi
      (fun ρ => continuous_zetaCompletedZeroSideCoordinateL1_eval
        (ρ : {ρ : ℂ // ZetaCompletedZero ρ}))

/-- The typed `ℓ¹` singleton at one completed-zero coordinate. -/
noncomputable def zetaCompletedZeroSideCoordinateL1Single
    (coordinate : {ρ : ℂ // ZetaCompletedZero ρ})
    (value : ℂ) :
    lp
      (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ)
      (1 : ℝ≥0∞) :=
  lp.single (1 : ℝ≥0∞) coordinate value

/-- The typed completed-zero singleton evaluates to its value at its own
coordinate. -/
theorem zetaCompletedZeroSideCoordinateL1Single_apply_self
    (coordinate : {ρ : ℂ // ZetaCompletedZero ρ})
    (value : ℂ) :
    zetaCompletedZeroSideCoordinateL1Single coordinate value coordinate =
      value := by
  change
    (lp.single (1 : ℝ≥0∞) coordinate value :
      lp
        (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ)
        (1 : ℝ≥0∞)) coordinate = value
  exact lp.single_apply_self
    (E := fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ)
    (1 : ℝ≥0∞) coordinate value

/-- The typed completed-zero singleton vanishes away from its coordinate. -/
theorem zetaCompletedZeroSideCoordinateL1Single_apply_ne
    (source target : {ρ : ℂ // ZetaCompletedZero ρ})
    (value : ℂ)
    (htargetSource : target ≠ source) :
    zetaCompletedZeroSideCoordinateL1Single source value target = 0 := by
  change
    (lp.single (1 : ℝ≥0∞) source value :
      lp
        (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ)
        (1 : ℝ≥0∞)) target = 0
  exact lp.single_apply_ne
    (E := fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ)
    (1 : ℝ≥0∞) source value htargetSource

/-- Evaluation at a completed-zero coordinate as a complex-linear map on the
typed `ℓ¹` target. -/
noncomputable def zetaCompletedZeroSideCoordinateL1Evaluation
    (coordinate : {ρ : ℂ // ZetaCompletedZero ρ}) :
    lp
        (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ)
        (1 : ℝ≥0∞) →ₗ[ℂ]
      ℂ where
  toFun := fun vector => vector coordinate
  map_add' := fun left right => Eq.refl (left coordinate + right coordinate)
  map_smul' := fun scalar vector => Eq.refl (scalar * vector coordinate)

/-- The canonical finite-support `ℓ¹` right inverse for a completed-zero window. -/
noncomputable def zetaCompletedZeroSideCoordinateL1FiniteRightInverse
    (S : Finset {ρ : ℂ // ZetaCompletedZero ρ})
    (a : S → ℂ) :
    lp (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ) (1 : ℝ≥0∞) :=
  ∑ ρ : S,
    zetaCompletedZeroSideCoordinateL1Single
      (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) (a ρ)

/-- The finite-support right inverse realizes its prescribed completed-zero coordinates. -/
theorem zetaCompletedZeroSideCoordinateL1FiniteRightInverse_apply
    (S : Finset {ρ : ℂ // ZetaCompletedZero ρ})
    (a : S → ℂ)
    (ρ : S) :
    zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a
      (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) = a ρ := by
  unfold zetaCompletedZeroSideCoordinateL1FiniteRightInverse
  have hsumApply :
      (∑ η : S,
          zetaCompletedZeroSideCoordinateL1Single
            (η : {ρ : ℂ // ZetaCompletedZero ρ}) (a η))
          (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) =
        ∑ η : S,
          zetaCompletedZeroSideCoordinateL1Single
            (η : {ρ : ℂ // ZetaCompletedZero ρ}) (a η)
            (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :=
    _root_.map_sum
      (zetaCompletedZeroSideCoordinateL1Evaluation
        (ρ : {ρ : ℂ // ZetaCompletedZero ρ}))
      (fun η : S =>
        zetaCompletedZeroSideCoordinateL1Single
          (η : {ρ : ℂ // ZetaCompletedZero ρ}) (a η))
      Finset.univ
  have hsumSingle :
      (∑ η : S,
          zetaCompletedZeroSideCoordinateL1Single
            (η : {ρ : ℂ // ZetaCompletedZero ρ}) (a η)
            (ρ : {ρ : ℂ // ZetaCompletedZero ρ})) =
        zetaCompletedZeroSideCoordinateL1Single
          (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) (a ρ)
          (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :=
    Finset.sum_eq_single
      ρ
      (fun η _hη hηρ =>
        have hcoordinate :
            (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) ≠
              (η : {ρ : ℂ // ZetaCompletedZero ρ}) := by
          intro hρeqη
          exact hηρ (Subtype.ext hρeqη.symm)
        zetaCompletedZeroSideCoordinateL1Single_apply_ne
          (η : {ρ : ℂ // ZetaCompletedZero ρ})
          (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
          (a η)
          hcoordinate)
      (fun hρ => False.elim (hρ (Finset.mem_univ ρ)))
  have hsingleSelf :
      zetaCompletedZeroSideCoordinateL1Single
          (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) (a ρ)
          (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) =
        a ρ :=
    zetaCompletedZeroSideCoordinateL1Single_apply_self
      (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) (a ρ)
  exact Eq.trans hsumApply (Eq.trans hsumSingle hsingleSelf)

/-- The completed-zero `ℓ¹` coordinate image of admissible probes. -/
def zetaCompletedZeroSideCoordinateL1Image
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    Set (lp (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ) (1 : ℝ≥0∞)) :=
  Set.range
    (zetaCompletedZeroSideCoordinateL1LinearMap
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      hfinite
      hpartialLeft
      hcompactBoundary)

/-- The complex-linear completed-zero coordinate subspace generated by
admissible probes. -/
noncomputable def zetaCompletedZeroSideCoordinateL1Submodule
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    Submodule ℂ (lp (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ) (1 : ℝ≥0∞)) :=
  LinearMap.range
    (zetaCompletedZeroSideCoordinateL1LinearMap
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      hfinite
      hpartialLeft
      hcompactBoundary)

/-- The coordinate-image set is the carrier of its canonical complex-linear
submodule. -/
theorem zetaCompletedZeroSideCoordinateL1Image_eq_submodule
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    zetaCompletedZeroSideCoordinateL1Image
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =
      (zetaCompletedZeroSideCoordinateL1Submodule
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary :
          Set (lp (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ) (1 : ℝ≥0∞))) := by
  rfl

/-- The closed complex-linear completed-zero coordinate subspace. -/
noncomputable def zetaCompletedZeroSideCoordinateL1ClosureSubmodule
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    Submodule ℂ (lp (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ) (1 : ℝ≥0∞)) :=
  (zetaCompletedZeroSideCoordinateL1Submodule
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary).topologicalClosure

/-- The completed-zero `ℓ¹` closure generated by admissible probe coordinates. -/
def zetaCompletedZeroSideCoordinateL1Closure
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    Set (lp (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ) (1 : ℝ≥0∞)) :=
  closure
    (zetaCompletedZeroSideCoordinateL1Image
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      hfinite
      hpartialLeft
      hcompactBoundary)

/-- The set-valued completed-zero closure is the carrier of the canonical
closed complex-linear coordinate subspace. -/
theorem zetaCompletedZeroSideCoordinateL1Closure_eq_closureSubmodule
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    zetaCompletedZeroSideCoordinateL1Closure
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =
      (zetaCompletedZeroSideCoordinateL1ClosureSubmodule
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary :
          Set (lp (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ) (1 : ℝ≥0∞))) := by
  unfold zetaCompletedZeroSideCoordinateL1Closure
  unfold zetaCompletedZeroSideCoordinateL1ClosureSubmodule
  exact
    Eq.trans
      (congrArg closure
        (zetaCompletedZeroSideCoordinateL1Image_eq_submodule
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary))
      (Submodule.topologicalClosure_coe
        (zetaCompletedZeroSideCoordinateL1Submodule
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)).symm

/-- The completed-zero coordinate closure submodule is closed. -/
theorem isClosed_zetaCompletedZeroSideCoordinateL1ClosureSubmodule
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    IsClosed
      (zetaCompletedZeroSideCoordinateL1ClosureSubmodule
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary :
          Set (lp (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ) (1 : ℝ≥0∞))) := by
  exact
    Submodule.isClosed_topologicalClosure
      (zetaCompletedZeroSideCoordinateL1Submodule
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)

/-- Every admissible coordinate vector belongs to the closed completed-zero
coordinate submodule. -/
theorem mem_zetaCompletedZeroSideCoordinateL1ClosureSubmodule
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ∈
      zetaCompletedZeroSideCoordinateL1ClosureSubmodule
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary := by
  exact
    Submodule.le_topologicalClosure
      (zetaCompletedZeroSideCoordinateL1Submodule
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)
      ⟨f, Eq.refl
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f)⟩

/-- Every admissible probe coordinate belongs to its completed-zero `ℓ¹` closure. -/
theorem mem_zetaCompletedZeroSideCoordinateL1Closure
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch
        hpartialOneTwo
        hcompactOneTwo
        hfinite
        hpartialLeft
        hcompactBoundary
        f ∈
      zetaCompletedZeroSideCoordinateL1Closure
        hbranch
        hpartialOneTwo
        hcompactOneTwo
        hfinite
        hpartialLeft
        hcompactBoundary := by
  exact
    subset_closure
      ⟨f, Eq.refl
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary
          f)⟩

/-- The finite completed-zero coordinate kernel in the completed-zero `ℓ¹` target. -/
def zetaCompletedZeroSideCoordinateL1FiniteWindowKernel
    (S : Finset {ρ : ℂ // ZetaCompletedZero ρ}) :
    Set (lp (fun _ : {ρ : ℂ // ZetaCompletedZero ρ} => ℂ) (1 : ℝ≥0∞)) :=
  fun x => ∀ ρ : S, x (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) = 0

/-- A finite-support right inverse lies in the finite-window kernel exactly when its target
coordinate vector is zero. -/
theorem zetaCompletedZeroSideCoordinateL1FiniteRightInverse_mem_kernel_of_zero
    (S : Finset {ρ : ℂ // ZetaCompletedZero ρ})
    (a : S → ℂ)
    (ha : ∀ ρ : S, a ρ = 0) :
    zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a ∈
      zetaCompletedZeroSideCoordinateL1FiniteWindowKernel S := by
  intro ρ
  calc
    zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a
        (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) = a ρ :=
          zetaCompletedZeroSideCoordinateL1FiniteRightInverse_apply S a ρ
    _ = 0 := ha ρ

/-- The analytic completed-zero summability theorem places every admissible probe in
the constant-weight finite-mass carrier. -/
theorem mem_zetaCompletedZeroSideWeightedTailFinite_one
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction) :
    f ∈ ZetaCompletedZeroSideWeightedTailFinite (fun _ => 1) := by
  have hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f) :=
    summable_zetaZeroSideContribution
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      hfinite
      hpartialLeft
      hcompactBoundary
      f
  have hnorm :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          ‖zetaZeroSideContribution (ρ : ℂ) f‖) :=
    hsum.norm
  have hnnorm :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          ‖zetaZeroSideContribution (ρ : ℂ) f‖₊) :=
    have hcoeFunction :
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          (‖zetaZeroSideContribution (ρ : ℂ) f‖₊ : ℝ)) =
          (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
            ‖zetaZeroSideContribution (ρ : ℂ) f‖) := by
      funext ρ
      exact coe_nnnorm (zetaZeroSideContribution (ρ : ℂ) f)
    have hcoeSummable :
        Summable
          (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
            (‖zetaZeroSideContribution (ρ : ℂ) f‖₊ : ℝ)) :=
      Eq.mpr (congrArg Summable hcoeFunction) hnorm
    NNReal.summable_coe.mp hcoeSummable
  have hfiniteMass :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        (‖zetaZeroSideContribution (ρ : ℂ) f‖₊ : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr hnnorm
  have hmass :
      zetaCompletedZeroSideWeightedTailMass (fun _ => 1) f =
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          (‖zetaZeroSideContribution (ρ : ℂ) f‖₊ : ℝ≥0∞) := by
    unfold zetaCompletedZeroSideWeightedTailMass
    exact
      tsum_congr
        (fun ρ =>
          calc
            (1 : ℝ≥0∞) * ‖zetaCompletedZeroSideCoordinateLinearMap f ρ‖₊ =
                (1 : ℝ≥0∞) * ‖zetaZeroSideContribution (ρ : ℂ) f‖₊ :=
                  zetaCompletedZeroSideWeightedTailMass_summand
                    (fun _ => 1)
                    f
                    ρ
            _ = (‖zetaZeroSideContribution (ρ : ℂ) f‖₊ : ℝ≥0∞) :=
                  one_mul (‖zetaZeroSideContribution (ρ : ℂ) f‖₊ : ℝ≥0∞))
  intro htop
  exact hfiniteMass (hmass.symm.trans htop)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
