import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.Owner

/-!
# Dense-coordinate completed-zero detection

This file owns the separation step that turns density of completed-zero
coordinates into an admissible probe detecting a nonzero bounded coefficient.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace FiniteWindow

open scoped ENNReal

theorem zetaCompletedZeroSideAnnihilator_forall_eq_zero_of_no_detecting_probe
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hnoProbe :
      ¬ ∃ f : ZetaAdmissibleFunction,
        zetaCompletedZeroSideAnnihilator
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ≠ 0) :
    ∀ f : ZetaAdmissibleFunction,
      zetaCompletedZeroSideAnnihilator
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f = 0 :=
  fun f =>
    not_ne_iff.mp
      (fun hvalueNonzero =>
        hnoProbe ⟨f, hvalueNonzero⟩)

theorem zetaCompletedZeroSideCoefficient_eq_zero_of_no_detecting_probe_of_coordinateDensity
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hnoProbe :
      ¬ ∃ f : ZetaAdmissibleFunction,
        zetaCompletedZeroSideAnnihilator
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ≠ 0)
    (hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =
        Set.univ) :
    b rho = 0 :=
  let hallProbeValuesZero :
      ∀ f : ZetaAdmissibleFunction,
        zetaCompletedZeroSideAnnihilator
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f = 0 :=
    zetaCompletedZeroSideAnnihilator_forall_eq_zero_of_no_detecting_probe
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      b hnoProbe
  let hbZero : b = 0 :=
    zetaCompletedZeroSideL1DualCoefficient_eq_zero_of_coordinateClosure_eq_univ
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      hallProbeValuesZero hdense
  congrArg (fun coefficient => coefficient rho) hbZero

theorem zetaCompletedZeroSideL1DualContinuousLinearMap_single_one_apply
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate) :
    zetaCompletedZeroSideL1DualContinuousLinearMap b
        (lp.single (1 : ENNReal) rho (1 : ℂ) :
          lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) =
      b rho :=
  Eq.trans
    (zetaCompletedZeroSideL1DualContinuousLinearMap_apply
      b
      (lp.single (1 : ENNReal) rho (1 : ℂ) :
        lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)))
    (Eq.trans
      (zetaCompletedZeroSideL1DualPairing_single b rho (1 : ℂ))
      (mul_one (b rho)))

theorem zetaCompletedZeroSideL1DualContinuousLinearMap_single_one_ne_zero
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0) :
    zetaCompletedZeroSideL1DualContinuousLinearMap b
        (lp.single (1 : ENNReal) rho (1 : ℂ) :
          lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) ≠ 0 :=
  fun htargetZero =>
    hrho
      (Eq.trans
        (zetaCompletedZeroSideL1DualContinuousLinearMap_single_one_apply b rho).symm
        htargetZero)

theorem zetaCompletedZeroSideL1DualContinuousLinearMap_nonzero_set_open
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal)) :
    IsOpen
      (zetaCompletedZeroSideL1DualContinuousLinearMap b ⁻¹'
        ({0}ᶜ : Set ℂ)) :=
  let L :
      lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ] ℂ :=
    zetaCompletedZeroSideL1DualContinuousLinearMap b
  show IsOpen (L ⁻¹' ({0}ᶜ : Set ℂ)) from
    isClosed_singleton.isOpen_compl.preimage L.continuous

theorem zetaCompletedZeroSideCoordinateL1Single_mem_closure_of_coordinateDensity
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (rho : ZetaCompletedZeroCoordinate)
    (hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =
        Set.univ) :
    (lp.single (1 : ENNReal) rho (1 : ℂ) :
      lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) ∈
      closure
        (Set.range
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)) :=
  Eq.mp
    (congrArg
      (fun carrier :
          Set (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) =>
        (lp.single (1 : ENNReal) rho (1 : ℂ) :
          lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) ∈ carrier)
      hdense.symm)
    (Set.mem_univ
      (lp.single (1 : ENNReal) rho (1 : ℂ) :
        lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)))

theorem exists_coordinateMap_mem_open_of_target_mem_closure
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (target : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (openCarrier :
      Set (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)))
    (htargetMemClosure :
      target ∈
        closure
          (Set.range
            (zetaCompletedZeroSideCoordinateL1LinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)))
    (hopenCarrier : IsOpen openCarrier)
    (htargetMemOpenCarrier : target ∈ openCarrier) :
    ∃ coordinate :
        lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal),
      coordinate ∈
        Set.range
            (zetaCompletedZeroSideCoordinateL1LinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary) ∧
        coordinate ∈ openCarrier :=
  let coordinateImage :
      Set (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :=
    Set.range
      (zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)
  let hclosureInterOpen :
      (closure coordinateImage ∩ openCarrier).Nonempty :=
    ⟨target, htargetMemClosure, htargetMemOpenCarrier⟩
  let himageInterOpen :
      (coordinateImage ∩ openCarrier).Nonempty :=
    (closure_inter_open_nonempty_iff hopenCarrier).mp hclosureInterOpen
  match himageInterOpen with
  | ⟨coordinate, hcoordinateImage, hcoordinateOpen⟩ =>
      ⟨coordinate, hcoordinateImage, hcoordinateOpen⟩

theorem zetaCompletedZeroSideAnnihilator_eq_dual_on_coordinateMap
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideL1DualContinuousLinearMap b
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) =
      zetaCompletedZeroSideAnnihilator
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f :=
  zetaCompletedZeroSideL1DualContinuousLinearMap_apply
    b
    (zetaCompletedZeroSideCoordinateL1LinearMap
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f)

theorem exists_probe_detecting_of_coordinateMap_mem_nonzero_dual
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (coordinate :
      lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (hcoordinateRange :
      coordinate ∈
        Set.range
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary))
    (hcoordinateNonzero :
      zetaCompletedZeroSideL1DualContinuousLinearMap b coordinate ≠ 0) :
    ∃ f : ZetaAdmissibleFunction,
      zetaCompletedZeroSideAnnihilator
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ≠ 0 :=
  let coordinateMap :
      ZetaAdmissibleFunction →
        lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) :=
    zetaCompletedZeroSideCoordinateL1LinearMap
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  let L :
      lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ] ℂ :=
    zetaCompletedZeroSideL1DualContinuousLinearMap b
  match hcoordinateRange with
  | ⟨f, hf⟩ =>
      let hmapAnnihilator :
          L (coordinateMap f) =
            zetaCompletedZeroSideAnnihilator
              b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f :=
        zetaCompletedZeroSideAnnihilator_eq_dual_on_coordinateMap
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f
      let hcoordinateAnnihilator :
          L coordinate =
            zetaCompletedZeroSideAnnihilator
              b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f :=
        Eq.trans (congrArg L hf.symm) hmapAnnihilator
      ⟨f,
        fun hannihilatorZero =>
          hcoordinateNonzero
            (Eq.trans hcoordinateAnnihilator hannihilatorZero)⟩

theorem exists_probe_detecting_nonzero_completedZeroCoefficient_of_coordinateDensity
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0)
    (hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =
        Set.univ) :
    ∃ f : ZetaAdmissibleFunction,
      zetaCompletedZeroSideAnnihilator
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ≠ 0 :=
  let target : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) :=
    lp.single (1 : ENNReal) rho (1 : ℂ)
  let L :
      lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ] ℂ :=
    zetaCompletedZeroSideL1DualContinuousLinearMap b
  have htargetNonzero : L target ≠ 0 :=
    zetaCompletedZeroSideL1DualContinuousLinearMap_single_one_ne_zero b rho hrho
  let nonzeroSet :
      Set (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :=
    L ⁻¹' ({0}ᶜ : Set ℂ)
  have hnonzeroSetOpen : IsOpen nonzeroSet :=
    zetaCompletedZeroSideL1DualContinuousLinearMap_nonzero_set_open b
  have htargetMemNonzeroSet : target ∈ nonzeroSet :=
    htargetNonzero
  have htargetMemClosure :
      target ∈
        closure
          (Set.range
            (zetaCompletedZeroSideCoordinateL1LinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)) :=
    zetaCompletedZeroSideCoordinateL1Single_mem_closure_of_coordinateDensity
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary rho hdense
  match
    exists_coordinateMap_mem_open_of_target_mem_closure
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      target nonzeroSet htargetMemClosure hnonzeroSetOpen htargetMemNonzeroSet with
  | ⟨coordinate, hcoordinateRange, hcoordinateNonzero⟩ =>
      exists_probe_detecting_of_coordinateMap_mem_nonzero_dual
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
        b coordinate hcoordinateRange hcoordinateNonzero

end FiniteWindow
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
