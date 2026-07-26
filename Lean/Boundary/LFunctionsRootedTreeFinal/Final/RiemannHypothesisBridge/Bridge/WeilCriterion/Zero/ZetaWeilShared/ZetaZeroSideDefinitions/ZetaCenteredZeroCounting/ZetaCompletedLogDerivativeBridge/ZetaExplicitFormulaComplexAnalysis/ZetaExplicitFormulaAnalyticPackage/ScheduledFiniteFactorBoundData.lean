import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledConcreteLogDerivControl
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.SingularSeparation

/-!
# Scheduled finite factor-bound carriers

This file owns the finite list assembly step for scheduled horizontal carriers
that already carry completed-log-derivative factor bounds.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_singletonFactorBoundedCarrier_of_lower_bounds
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (δ : ℝ)
    (δ_pos : 0 < δ)
    (δ_zero :
      δ ≤
        ‖zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x‖)
    (δ_one :
      δ ≤
        ‖zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x - 1‖)
    (δ_completedZero :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤
          ‖zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x -
              ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δ_gammaPole :
      ∀ n : ℕ,
        δ ≤
          ‖zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x - (-(2 * (n : ℂ)))‖) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  let z : ℂ :=
    zetaCompletedExplicitFormulaTopPath
      (F.rectangle (h.height_schedule.height u)) x
  let pointwise := h.scheduled_topPath_zeroExcisedPointwise u x hx
  let hstrip := pointwise.1
  let hz0 := pointwise.2.1
  let hz1 := pointwise.2.2.1
  let hzeta := pointwise.2.2.2.1
  let hgamma := pointwise.2.2.2.2.1
  let boundedCarrier :
      CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
        (min F.c (1 - F.c)) (max F.c (1 - F.c)) :=
    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_lower_bounds
      z hstrip hz0 hz1 hzeta hgamma
      δ δ_pos δ_zero δ_one δ_completedZero δ_gammaPole
  Exists.intro boundedCarrier
    (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_lower_bounds_mem
      z hstrip hz0 hz1 hzeta hgamma
      δ δ_pos δ_zero δ_one δ_completedZero δ_gammaPole)

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_singletonFactorBoundedCarrier_of_lower_bounds
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (δ : ℝ)
    (δ_pos : 0 < δ)
    (δ_zero :
      δ ≤
        ‖zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x‖)
    (δ_one :
      δ ≤
        ‖zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x - 1‖)
    (δ_completedZero :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x -
              ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δ_gammaPole :
      ∀ n : ℕ,
        δ ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x - (-(2 * (n : ℂ)))‖) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  let z : ℂ :=
    zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (h.height_schedule.height u)) x
  let pointwise := h.scheduled_bottomPath_zeroExcisedPointwise u x hx
  let hstrip := pointwise.1
  let hz0 := pointwise.2.1
  let hz1 := pointwise.2.2.1
  let hzeta := pointwise.2.2.2.1
  let hgamma := pointwise.2.2.2.2.1
  let boundedCarrier :
      CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
        (min F.c (1 - F.c)) (max F.c (1 - F.c)) :=
    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_lower_bounds
      z hstrip hz0 hz1 hzeta hgamma
      δ δ_pos δ_zero δ_one δ_completedZero δ_gammaPole
  Exists.intro boundedCarrier
    (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_lower_bounds_mem
      z hstrip hz0 hz1 hzeta hgamma
      δ δ_pos δ_zero δ_one δ_completedZero δ_gammaPole)

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_singletonFactorBoundedCarrier_of_component_lower_bounds
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (δZero δOne δCompleted δGamma : ℝ)
    (δZeroPos : 0 < δZero)
    (δOnePos : 0 < δOne)
    (δCompletedPos : 0 < δCompleted)
    (δGammaPos : 0 < δGamma)
    (δZeroBound :
      δZero ≤
        ‖zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x‖)
    (δOneBound :
      δOne ≤
        ‖zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x - 1‖)
    (δCompletedBound :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δCompleted ≤
          ‖zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x -
              ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δGammaBound :
      ∀ n : ℕ,
        δGamma ≤
          ‖zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x - (-(2 * (n : ℂ)))‖) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  let z : ℂ :=
    zetaCompletedExplicitFormulaTopPath
      (F.rectangle (h.height_schedule.height u)) x
  let pointwise := h.scheduled_topPath_zeroExcisedPointwise u x hx
  let hstrip := pointwise.1
  let hz0 := pointwise.2.1
  let hz1 := pointwise.2.2.1
  let hzeta := pointwise.2.2.2.1
  let hgamma := pointwise.2.2.2.2.1
  let boundedCarrier :
      CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
        (min F.c (1 - F.c)) (max F.c (1 - F.c)) :=
    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_component_lower_bounds
      z hstrip hz0 hz1 hzeta hgamma
      δZero δOne δCompleted δGamma
      δZeroPos δOnePos δCompletedPos δGammaPos
      δZeroBound δOneBound δCompletedBound δGammaBound
  Exists.intro boundedCarrier
    (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_component_lower_bounds_mem
      z hstrip hz0 hz1 hzeta hgamma
      δZero δOne δCompleted δGamma
      δZeroPos δOnePos δCompletedPos δGammaPos
      δZeroBound δOneBound δCompletedBound δGammaBound)

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_singletonFactorBoundedCarrier_of_component_lower_bounds
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (δZero δOne δCompleted δGamma : ℝ)
    (δZeroPos : 0 < δZero)
    (δOnePos : 0 < δOne)
    (δCompletedPos : 0 < δCompleted)
    (δGammaPos : 0 < δGamma)
    (δZeroBound :
      δZero ≤
        ‖zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x‖)
    (δOneBound :
      δOne ≤
        ‖zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x - 1‖)
    (δCompletedBound :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δCompleted ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x -
              ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δGammaBound :
      ∀ n : ℕ,
        δGamma ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x - (-(2 * (n : ℂ)))‖) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  let z : ℂ :=
    zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (h.height_schedule.height u)) x
  let pointwise := h.scheduled_bottomPath_zeroExcisedPointwise u x hx
  let hstrip := pointwise.1
  let hz0 := pointwise.2.1
  let hz1 := pointwise.2.2.1
  let hzeta := pointwise.2.2.2.1
  let hgamma := pointwise.2.2.2.2.1
  let boundedCarrier :
      CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
        (min F.c (1 - F.c)) (max F.c (1 - F.c)) :=
    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_component_lower_bounds
      z hstrip hz0 hz1 hzeta hgamma
      δZero δOne δCompleted δGamma
      δZeroPos δOnePos δCompletedPos δGammaPos
      δZeroBound δOneBound δCompletedBound δGammaBound
  Exists.intro boundedCarrier
    (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_component_lower_bounds_mem
      z hstrip hz0 hz1 hzeta hgamma
      δZero δOne δCompleted δGamma
      δZeroPos δOnePos δCompletedPos δGammaPos
      δZeroBound δOneBound δCompletedBound δGammaBound)

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_singletonFactorBoundedCarrier_of_singular_component_lower_bounds
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (δCompleted δGamma : ℝ)
    (δCompletedPos : 0 < δCompleted)
    (δGammaPos : 0 < δGamma)
    (δCompletedBound :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δCompleted ≤
          ‖zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x -
              ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δGammaBound :
      ∀ n : ℕ,
        δGamma ≤
          ‖zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x - (-(2 * (n : ℂ)))‖) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  let z : ℂ :=
    zetaCompletedExplicitFormulaTopPath
      (F.rectangle (h.height_schedule.height u)) x
  let pointwise := h.scheduled_topPath_zeroExcisedPointwise u x hx
  let hstrip := pointwise.1
  let hz0 := pointwise.2.1
  let hz1 := pointwise.2.2.1
  let hzeta := pointwise.2.2.2.1
  let hgamma := pointwise.2.2.2.2.1
  let boundedCarrier :
      CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
        (min F.c (1 - F.c)) (max F.c (1 - F.c)) :=
    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_singular_component_lower_bounds
      z hstrip hz0 hz1 hzeta hgamma
      δCompleted δGamma δCompletedPos δGammaPos
      δCompletedBound δGammaBound
  Exists.intro boundedCarrier
    (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_singular_component_lower_bounds_mem
      z hstrip hz0 hz1 hzeta hgamma
      δCompleted δGamma δCompletedPos δGammaPos
      δCompletedBound δGammaBound)

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_singletonFactorBoundedCarrier_of_singular_component_lower_bounds
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (δCompleted δGamma : ℝ)
    (δCompletedPos : 0 < δCompleted)
    (δGammaPos : 0 < δGamma)
    (δCompletedBound :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δCompleted ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x -
              ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δGammaBound :
      ∀ n : ℕ,
        δGamma ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x - (-(2 * (n : ℂ)))‖) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  let z : ℂ :=
    zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (h.height_schedule.height u)) x
  let pointwise := h.scheduled_bottomPath_zeroExcisedPointwise u x hx
  let hstrip := pointwise.1
  let hz0 := pointwise.2.1
  let hz1 := pointwise.2.2.1
  let hzeta := pointwise.2.2.2.1
  let hgamma := pointwise.2.2.2.2.1
  let boundedCarrier :
      CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
        (min F.c (1 - F.c)) (max F.c (1 - F.c)) :=
    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_singular_component_lower_bounds
      z hstrip hz0 hz1 hzeta hgamma
      δCompleted δGamma δCompletedPos δGammaPos
      δCompletedBound δGammaBound
  Exists.intro boundedCarrier
    (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_singular_component_lower_bounds_mem
      z hstrip hz0 hz1 hzeta hgamma
      δCompleted δGamma δCompletedPos δGammaPos
      δCompletedBound δGammaBound)

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalPairFactorBoundedCarrier_of_top_bottom
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (topCarrier :
      ∃ boundedCarrier :
          CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
            (min F.c (1 - F.c)) (max F.c (1 - F.c)),
        zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x ∈
          boundedCarrier.carrier.carrier)
    (bottomCarrier :
      ∃ boundedCarrier :
          CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
            (min F.c (1 - F.c)) (max F.c (1 - F.c)),
        zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x ∈
          boundedCarrier.carrier.carrier) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier ∧
      zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  Exists.elim topCarrier
    (fun topBounded topMem =>
      Exists.elim bottomCarrier
        (fun bottomBounded bottomMem =>
          let combinedCarrier :=
            CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.union
              topBounded bottomBounded
          Exists.intro combinedCarrier
            (And.intro
              (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_left
                topBounded bottomBounded topMem)
              (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_right
                topBounded bottomBounded bottomMem))))

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalPairFactorBoundedCarrier_of_lower_bounds
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (δTop δBottom : ℝ)
    (δTopPos : 0 < δTop)
    (δBottomPos : 0 < δBottom)
    (δTopZero :
      δTop ≤
        ‖zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x‖)
    (δTopOne :
      δTop ≤
        ‖zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x - 1‖)
    (δTopCompletedZero :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δTop ≤
          ‖zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x -
              ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δTopGammaPole :
      ∀ n : ℕ,
        δTop ≤
          ‖zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x - (-(2 * (n : ℂ)))‖)
    (δBottomZero :
      δBottom ≤
        ‖zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x‖)
    (δBottomOne :
      δBottom ≤
        ‖zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x - 1‖)
    (δBottomCompletedZero :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δBottom ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x -
              ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δBottomGammaPole :
      ∀ n : ℕ,
        δBottom ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x - (-(2 * (n : ℂ)))‖) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier ∧
      zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalPairFactorBoundedCarrier_of_top_bottom
    h u x
    (ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_singletonFactorBoundedCarrier_of_lower_bounds
      h u x hx δTop δTopPos δTopZero δTopOne
      δTopCompletedZero δTopGammaPole)
    (ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_singletonFactorBoundedCarrier_of_lower_bounds
      h u x hx δBottom δBottomPos δBottomZero δBottomOne
      δBottomCompletedZero δBottomGammaPole)

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFiniteWindowFactorBoundedCarrier
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (xs : List ℝ)
    (pairCarrier :
      ∀ x : ℝ, x ∈ xs →
        ∃ boundedCarrier :
            CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
              (min F.c (1 - F.c)) (max F.c (1 - F.c)),
          zetaCompletedExplicitFormulaTopPath
              (F.rectangle (h.height_schedule.height u)) x ∈
            boundedCarrier.carrier.carrier ∧
          zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (h.height_schedule.height u)) x ∈
            boundedCarrier.carrier.carrier) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      (∀ x : ℝ, x ∈ xs →
        zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x ∈
          boundedCarrier.carrier.carrier) ∧
      (∀ x : ℝ, x ∈ xs →
        zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x ∈
          boundedCarrier.carrier.carrier) :=
  List.rec
    (motive := fun ys =>
      (∀ x : ℝ, x ∈ ys →
        ∃ boundedCarrier :
            CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
              (min F.c (1 - F.c)) (max F.c (1 - F.c)),
          zetaCompletedExplicitFormulaTopPath
              (F.rectangle (h.height_schedule.height u)) x ∈
            boundedCarrier.carrier.carrier ∧
          zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (h.height_schedule.height u)) x ∈
            boundedCarrier.carrier.carrier) →
      ∃ boundedCarrier :
          CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
            (min F.c (1 - F.c)) (max F.c (1 - F.c)),
        (∀ x : ℝ, x ∈ ys →
          zetaCompletedExplicitFormulaTopPath
              (F.rectangle (h.height_schedule.height u)) x ∈
            boundedCarrier.carrier.carrier) ∧
        (∀ x : ℝ, x ∈ ys →
          zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (h.height_schedule.height u)) x ∈
            boundedCarrier.carrier.carrier))
    (fun emptyPairCarrier =>
      Exists.intro
        (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.empty
          (min F.c (1 - F.c)) (max F.c (1 - F.c)))
        (And.intro
          (fun x hx =>
            Exists.elim (emptyPairCarrier x hx)
              (fun boundedCarrier hmem =>
                False.elim ((fun membership => List.not_mem_nil x hx) hmem)))
          (fun x hx =>
            Exists.elim (emptyPairCarrier x hx)
              (fun boundedCarrier hmem =>
                False.elim ((fun membership => List.not_mem_nil x hx) hmem)))))
    (fun x ys ih consPairCarrier =>
      let tailPairCarrier :
          ∀ y : ℝ, y ∈ ys →
            ∃ boundedCarrier :
                CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
                  (min F.c (1 - F.c)) (max F.c (1 - F.c)),
              zetaCompletedExplicitFormulaTopPath
                  (F.rectangle (h.height_schedule.height u)) y ∈
                boundedCarrier.carrier.carrier ∧
              zetaCompletedExplicitFormulaBottomPath
                  (F.rectangle (h.height_schedule.height u)) y ∈
                boundedCarrier.carrier.carrier :=
        fun y hy => consPairCarrier y (List.mem_cons_of_mem x hy)
      match consPairCarrier x (List.mem_cons_self x ys), ih tailPairCarrier with
      | ⟨headCarrier, headTop, headBottom⟩,
        ⟨tailCarrier, tailTop, tailBottom⟩ =>
          let combinedCarrier :=
            CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.union
              headCarrier tailCarrier
          Exists.intro combinedCarrier
            (And.intro
              (fun y hy =>
                match List.mem_cons.mp hy with
                | Or.inl hyx =>
                    Eq.subst
                      (motive := fun w : ℝ =>
                        zetaCompletedExplicitFormulaTopPath
                            (F.rectangle (h.height_schedule.height u)) w ∈
                          combinedCarrier.carrier.carrier)
                      hyx.symm
                      (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_left
                        headCarrier tailCarrier headTop)
                | Or.inr hytail =>
                    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_right
                      headCarrier tailCarrier (tailTop y hytail))
              (fun y hy =>
                match List.mem_cons.mp hy with
                | Or.inl hyx =>
                    Eq.subst
                      (motive := fun w : ℝ =>
                        zetaCompletedExplicitFormulaBottomPath
                            (F.rectangle (h.height_schedule.height u)) w ∈
                          combinedCarrier.carrier.carrier)
                      hyx.symm
                      (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_left
                        headCarrier tailCarrier headBottom)
                | Or.inr hytail =>
                    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_right
                      headCarrier tailCarrier (tailBottom y hytail))))
    xs pairCarrier

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFiniteSampleFactorBoundedCarrier
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (samples : List (ℝ × ℝ))
    (pairCarrier :
      ∀ p : ℝ × ℝ, p ∈ samples →
        ∃ boundedCarrier :
            CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
              (min F.c (1 - F.c)) (max F.c (1 - F.c)),
          zetaCompletedExplicitFormulaTopPath
              (F.rectangle (h.height_schedule.height p.1)) p.2 ∈
            boundedCarrier.carrier.carrier ∧
          zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (h.height_schedule.height p.1)) p.2 ∈
            boundedCarrier.carrier.carrier) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      (∀ p : ℝ × ℝ, p ∈ samples →
        zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height p.1)) p.2 ∈
          boundedCarrier.carrier.carrier) ∧
      (∀ p : ℝ × ℝ, p ∈ samples →
        zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height p.1)) p.2 ∈
          boundedCarrier.carrier.carrier) :=
  List.rec
    (motive := fun sampleList =>
      (∀ p : ℝ × ℝ, p ∈ sampleList →
        ∃ boundedCarrier :
            CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
              (min F.c (1 - F.c)) (max F.c (1 - F.c)),
          zetaCompletedExplicitFormulaTopPath
              (F.rectangle (h.height_schedule.height p.1)) p.2 ∈
            boundedCarrier.carrier.carrier ∧
          zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (h.height_schedule.height p.1)) p.2 ∈
            boundedCarrier.carrier.carrier) →
      ∃ boundedCarrier :
          CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
            (min F.c (1 - F.c)) (max F.c (1 - F.c)),
        (∀ p : ℝ × ℝ, p ∈ sampleList →
          zetaCompletedExplicitFormulaTopPath
              (F.rectangle (h.height_schedule.height p.1)) p.2 ∈
            boundedCarrier.carrier.carrier) ∧
        (∀ p : ℝ × ℝ, p ∈ sampleList →
          zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (h.height_schedule.height p.1)) p.2 ∈
            boundedCarrier.carrier.carrier))
    (fun emptyPairCarrier =>
      Exists.intro
        (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.empty
          (min F.c (1 - F.c)) (max F.c (1 - F.c)))
        (And.intro
          (fun p hp =>
            Exists.elim (emptyPairCarrier p hp)
              (fun boundedCarrier hmem =>
                False.elim ((fun membership => List.not_mem_nil p hp) hmem)))
          (fun p hp =>
            Exists.elim (emptyPairCarrier p hp)
              (fun boundedCarrier hmem =>
                False.elim ((fun membership => List.not_mem_nil p hp) hmem)))))
    (fun p sampleList ih consPairCarrier =>
      let tailPairCarrier :
          ∀ q : ℝ × ℝ, q ∈ sampleList →
            ∃ boundedCarrier :
                CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
                  (min F.c (1 - F.c)) (max F.c (1 - F.c)),
              zetaCompletedExplicitFormulaTopPath
                  (F.rectangle (h.height_schedule.height q.1)) q.2 ∈
                boundedCarrier.carrier.carrier ∧
              zetaCompletedExplicitFormulaBottomPath
                  (F.rectangle (h.height_schedule.height q.1)) q.2 ∈
                boundedCarrier.carrier.carrier :=
        fun q hq => consPairCarrier q (List.mem_cons_of_mem p hq)
      match consPairCarrier p (List.mem_cons_self p sampleList), ih tailPairCarrier with
      | ⟨headCarrier, headTop, headBottom⟩,
        ⟨tailCarrier, tailTop, tailBottom⟩ =>
          let combinedCarrier :=
            CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.union
              headCarrier tailCarrier
          Exists.intro combinedCarrier
            (And.intro
              (fun q hq =>
                match List.mem_cons.mp hq with
                | Or.inl hqp =>
                    Eq.subst
                      (motive := fun r : ℝ × ℝ =>
                        zetaCompletedExplicitFormulaTopPath
                            (F.rectangle (h.height_schedule.height r.1)) r.2 ∈
                          combinedCarrier.carrier.carrier)
                      hqp.symm
                      (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_left
                        headCarrier tailCarrier headTop)
                | Or.inr hqtail =>
                    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_right
                      headCarrier tailCarrier (tailTop q hqtail))
              (fun q hq =>
                match List.mem_cons.mp hq with
                | Or.inl hqp =>
                    Eq.subst
                      (motive := fun r : ℝ × ℝ =>
                        zetaCompletedExplicitFormulaBottomPath
                            (F.rectangle (h.height_schedule.height r.1)) r.2 ∈
                          combinedCarrier.carrier.carrier)
                      hqp.symm
                      (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_left
                        headCarrier tailCarrier headBottom)
                | Or.inr hqtail =>
                    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_right
                      headCarrier tailCarrier (tailBottom q hqtail))))
    samples pairCarrier

/-- The finite sample carrier is obtained from the actual completed-zero and
Gamma-pole separation owners.  In particular, this constructor does not ask
for a uniform separation of the entire unbounded scheduled carrier. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFiniteSampleFactorBoundedCarrier_of_owner_separation
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (samples : List (ℝ × ℝ))
    (hx : ∀ p : ℝ × ℝ, p ∈ samples → p.2 ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      (∀ p : ℝ × ℝ, p ∈ samples →
        zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height p.1)) p.2 ∈
          boundedCarrier.carrier.carrier) ∧
      (∀ p : ℝ × ℝ, p ∈ samples →
        zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height p.1)) p.2 ∈
          boundedCarrier.carrier.carrier) :=
  ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFiniteSampleFactorBoundedCarrier
    h samples
    (fun p hpmem =>
      let hp := h.scheduled_topPath_zeroExcisedPointwise p.1 p.2 (hx p hpmem)
      let zTop := zetaCompletedExplicitFormulaTopPath
        (F.rectangle (h.height_schedule.height p.1)) p.2
      let hpTop := completedZeroResidueCoordinate_norm_separation_of_completedRiemannZeta_ne_zero
        zTop hp.2.1 hp.2.2.1 hp.2.2.2.1
      let hpGamma := gammaPole_norm_separation_of_Gammaℝ_ne_zero
        zTop hp.2.2.2.2.1
      let δTop : ℝ := min hpTop.choose (min hpGamma.choose
        (min ‖zTop‖ ‖zTop - 1‖))
      have hδTop : 0 < δTop := by
        exact lt_min hpTop.choose_spec.1
          (lt_min hpGamma.choose_spec.1
            (lt_min (norm_pos_iff.mpr hp.2.1) (norm_pos_iff.mpr (sub_ne_zero.mpr hp.2.2.1))))
      have hTopZero : δTop ≤ ‖zTop‖ := by
        exact (min_le_right hpTop.choose (min hpGamma.choose (min ‖zTop‖ ‖zTop - 1‖))).trans
          (min_le_right hpGamma.choose (min ‖zTop‖ ‖zTop - 1‖)).trans
            (min_le_left ‖zTop‖ ‖zTop - 1‖)
      have hTopOne : δTop ≤ ‖zTop - 1‖ := by
        exact (min_le_right hpTop.choose (min hpGamma.choose (min ‖zTop‖ ‖zTop - 1‖))).trans
          (min_le_right hpGamma.choose (min ‖zTop‖ ‖zTop - 1‖)).trans
            (min_le_right ‖zTop‖ ‖zTop - 1‖)
      have hTopCompleted : ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
          δTop ≤ ‖zTop - ((1 / 2 : ℂ) + (ρ : ℂ))‖ := by
        intro ρ
        exact (min_le_left hpTop.choose).trans (hpTop.choose_spec.2 ρ)
      have hTopGamma : ∀ n : ℕ,
          δTop ≤ ‖zTop - (-(2 * (n : ℂ)))‖ := by
        intro n
        exact (min_le_right hpTop.choose (min hpGamma.choose (min ‖zTop‖ ‖zTop - 1‖))).trans
          ((min_le_left hpGamma.choose).trans (hpGamma.choose_spec.2 n))
      let hTop := ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_singletonFactorBoundedCarrier_of_lower_bounds
        h p.1 p.2 (hx p hpmem) δTop hδTop
        hTopZero hTopOne hTopCompleted hTopGamma
      let hb := h.scheduled_bottomPath_zeroExcisedPointwise p.1 p.2 (hx p hpmem)
      let zBottom := zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (h.height_schedule.height p.1)) p.2
      let hbTop := completedZeroResidueCoordinate_norm_separation_of_completedRiemannZeta_ne_zero
        zBottom hb.2.1 hb.2.2.1 hb.2.2.2.1
      let hbGamma := gammaPole_norm_separation_of_Gammaℝ_ne_zero
        zBottom hb.2.2.2.2.1
      let δBottom : ℝ := min hbTop.choose (min hbGamma.choose
        (min ‖zBottom‖ ‖zBottom - 1‖))
      have hδBottom : 0 < δBottom := by
        exact lt_min hbTop.choose_spec.1
          (lt_min hbGamma.choose_spec.1
            (lt_min (norm_pos_iff.mpr hb.2.1) (norm_pos_iff.mpr (sub_ne_zero.mpr hb.2.2.1))))
      have hBottomZero : δBottom ≤ ‖zBottom‖ := by
        exact (min_le_right hbTop.choose (min hbGamma.choose (min ‖zBottom‖ ‖zBottom - 1‖))).trans
          (min_le_right hbGamma.choose (min ‖zBottom‖ ‖zBottom - 1‖)).trans
            (min_le_left ‖zBottom‖ ‖zBottom - 1‖)
      have hBottomOne : δBottom ≤ ‖zBottom - 1‖ := by
        exact (min_le_right hbTop.choose (min hbGamma.choose (min ‖zBottom‖ ‖zBottom - 1‖))).trans
          (min_le_right hbGamma.choose (min ‖zBottom‖ ‖zBottom - 1‖)).trans
            (min_le_right ‖zBottom‖ ‖zBottom - 1‖)
      have hBottomCompleted : ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
          δBottom ≤ ‖zBottom - ((1 / 2 : ℂ) + (ρ : ℂ))‖ := by
        intro ρ
        exact (min_le_left hbTop.choose).trans (hbTop.choose_spec.2 ρ)
      have hBottomGamma : ∀ n : ℕ,
          δBottom ≤ ‖zBottom - (-(2 * (n : ℂ)))‖ := by
        intro n
        exact (min_le_right hbTop.choose (min hbGamma.choose (min ‖zBottom‖ ‖zBottom - 1‖))).trans
          ((min_le_left hbGamma.choose).trans (hbGamma.choose_spec.2 n))
      let hBottom := ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_singletonFactorBoundedCarrier_of_lower_bounds
        h p.1 p.2 (hx p hpmem) δBottom hδBottom
        hBottomZero hBottomOne hBottomCompleted hBottomGamma
      exact ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalPairFactorBoundedCarrier_of_top_bottom
        h p.1 p.2 hTop hBottom)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
