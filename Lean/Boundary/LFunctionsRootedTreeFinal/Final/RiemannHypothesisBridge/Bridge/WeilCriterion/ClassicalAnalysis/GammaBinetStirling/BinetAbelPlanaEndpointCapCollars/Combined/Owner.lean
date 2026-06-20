import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.SetIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteHoleSubdivisionCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaEndpointCapCollars.Foundation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaEndpointCapCollars.Left.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaEndpointCapCollars.Right.Owner

/-!
# Combined balance and owner theorems for endpoint cap-collars

Integration of left and right endpoint cap-collar analysis with balance theorems
and owner-level Cauchy-Goursat statements combining both endpoints.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

notation:max "[[" a "," b "]]" => Set.Icc a b

theorem Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_orientedBoundary_pair_owner
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 ∧
      Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 :=
  let hρnonneg := le_of_lt hρ
  let hcont_left :=
    Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hcont
  let hdiff_left :=
    Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hdiff
  let hleft :=
    Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero_owner
      (N := N) T hT hρ hdeleted_geometry hcont_left hdiff_left
  let hright :=
    Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero_owner
      N T hT hρ hdeleted_geometry hcont hdiff
  ⟨hleft, hright⟩

/-- Endpoint half-collar Cauchy-Goursat in balance form.

This is the remaining planar topology input: the left endpoint right
half-collar and the right endpoint left half-collar have oriented boundary
zero, expressed as equality between their straight collar boundary and their
endpoint semicircular indentation.  The statement is deliberately local to the
two endpoint half-collars, not a full rectangle through an endpoint pole. -/
theorem Complex.finiteAbelPlana_log_endpointHalfCollarCauchyGoursat_balance_left_right
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) ∧
      (Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
            Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
          let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :=
  let hboundary :=
    Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_orientedBoundary_pair_owner
      N T hT hρ hdeleted_geometry hcont hdiff
  ⟨
    Complex.finiteAbelPlana_log_leftEndpointHalfCollar_balance_of_orientedBoundary_zero
      w T ρ hboundary.1,
    (sub_eq_zero.mp hboundary.2 : _)
  ⟩

/-- Algebraic conversion from the left endpoint half-collar balance to the
oriented-boundary vanishing statement. -/
theorem Complex.finiteAbelPlana_log_leftEndpointHalfCollar_orientedBoundary_eq_zero_of_balance
    (w : ℂ)
    (T ρ : ℝ)
    (hbalance :
      Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 :=
  sub_eq_zero.mpr hbalance

/-- Algebraic conversion from the right endpoint half-collar balance to the
unfolded oriented-boundary vanishing statement. -/
theorem Complex.finiteAbelPlana_log_rightEndpointHalfCollar_orientedBoundary_eq_zero_of_balance
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ)
    (hbalance :
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
        let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
        Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
      (let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 :=
  sub_eq_zero.mpr hbalance

/-- The two local endpoint half-collar Cauchy-Goursat identities.

This is the exact local topology input for the endpoint collars.  The left
identity is Cauchy-Goursat on the right half-rectangle based at `0`, with its
right semicircular deleted boundary.  The right identity is the translated
left half-rectangle based at `N + 1`, with its left semicircular deleted
boundary.  The displayed signs are the punctured-domain orientations:
lower collar, minus upper collar, adjacent safe vertical edge, minus
principal-value vertical edge, minus the endpoint semicircle. -/
theorem Complex.finiteAbelPlana_log_endpointHalfCollarCauchyGoursat_left_right
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 ∧
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 :=
  let hbalance :=
    Complex.finiteAbelPlana_log_endpointHalfCollarCauchyGoursat_balance_left_right
      N T hT hρ hdeleted_geometry hcont hdiff
  ⟨Complex.finiteAbelPlana_log_leftEndpointHalfCollar_orientedBoundary_eq_zero_of_balance
    w T ρ hbalance.1,
   Complex.finiteAbelPlana_log_rightEndpointHalfCollar_orientedBoundary_eq_zero_of_balance
    N w T ρ hbalance.2⟩

/-- Left endpoint half-collar Cauchy-Goursat identity, extracted from the
local endpoint half-collar pair. -/
theorem Complex.finiteAbelPlana_log_leftEndpointHalfCollarCauchyGoursat_orientedBoundary_eq_zero
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 :=
  let hρnonneg := le_of_lt hρ
  let hcont_left :=
    Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hcont
  let hdiff_left :=
    Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hdiff
  Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero_owner
    (N := N) T hT hρ hdeleted_geometry hcont_left hdiff_left

/-- Right endpoint half-collar Cauchy-Goursat identity, extracted from the
local endpoint half-collar pair. -/
theorem Complex.finiteAbelPlana_log_rightEndpointHalfCollarCauchyGoursat_orientedBoundary_eq_zero
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
        Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
      (let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 :=
  Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero_owner
    N T hT hρ hdeleted_geometry hcont hdiff

/-- Assembly of the endpoint semicollar pair from the two local half-collar
Cauchy-Goursat identities. -/
theorem Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_pair_of_halfCollars
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hleft :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0)
    (hright :
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 ∧
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 :=
  ⟨hleft, hright⟩

/-- Shared semicollar Cauchy-Goursat owner statement for the endpoint caps.

Each endpoint domain is a half-rectangle with the endpoint disk removed.
Its oriented boundary is
`lower collar - upper collar + safe vertical edge - PV vertical edge -
endpoint semicircle`, with the right endpoint obtained from the same local
semicollar geometry by translation and reflection.  The second conjunct is
written in unfolded form so the same owner theorem can serve the right wrapper
after the right endpoint boundary is named. -/
theorem Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_orientedBoundary_eq_zero_pair
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 ∧
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 :=
  let hleft :=
    Complex.finiteAbelPlana_log_leftEndpointHalfCollarCauchyGoursat_orientedBoundary_eq_zero
      N T hT hρ hdeleted_geometry hcont hdiff
  let hright :=
    Complex.finiteAbelPlana_log_rightEndpointHalfCollarCauchyGoursat_orientedBoundary_eq_zero
      N T hT hρ hdeleted_geometry hcont hdiff
  Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_pair_of_halfCollars
    N T hleft hright

/-- Cauchy-Goursat on the left endpoint cap/collar domain, with the boundary
orientation identified with the existing named side and indentation integrals.

This is the exact local classical proof obligation: apply Cauchy-Goursat to the
punctured cap/collar domain and match its oriented boundary to the lower collar,
upper collar, adjacent safe-strip vertical edge, principal-value left edge, and
right semicircular indentation at the left endpoint. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 :=
  (Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_orientedBoundary_eq_zero_pair
    N T hT hρ hdeleted_geometry hcont hdiff).1

/-- Algebraic extraction of the left endpoint semicircle from the oriented
cap/collar boundary equation. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollar_balance_of_orientedBoundary_eq_zero
    (w : ℂ)
    (T ρ : ℝ)
    (hboundary :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0) :
    Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
        Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
      ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
  sub_eq_zero.mp hboundary

/-- The left endpoint oriented boundary vanishes exactly when the straight
collar boundary equals the right semicircular indentation integral. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero_iff_balance
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 ↔
      Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
  ⟨
    fun hboundary =>
      Complex.finiteAbelPlana_log_leftEndpointCapCollar_balance_of_orientedBoundary_eq_zero
        w T ρ hboundary,
    fun hbalance => sub_eq_zero.mpr hbalance
  ⟩

/-- Unnormalized local Cauchy-Goursat balance for the left endpoint collar.

The contour is the left endpoint cap/collar subdomain: the lower horizontal
collar from `0` to `ρ`, the safe-strip vertical edge at `x = ρ`, the upper
horizontal collar with opposite orientation, the principal-value left vertical
edge with opposite orientation, and the right semicircular indentation around
the deleted endpoint pole.  Cauchy's theorem on that punctured collar says the
sum of these oriented pieces is zero; equivalently, the straight cap/collar
boundary equals the endpoint indentation integral with the displayed
orientation. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollar_unnormalizedCauchy_balance
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
        Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
      ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
  let hboundary :=
    Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero
      N T hT hρ hdeleted_geometry hcont hdiff
  Complex.finiteAbelPlana_log_leftEndpointCapCollar_balance_of_orientedBoundary_eq_zero
    w T ρ hboundary

/-- The left endpoint collar, together with the adjacent safe-strip boundary
pieces, contributes exactly the left endpoint deleted semicircle.

This is the one-piece Cauchy-Goursat statement for the left endpoint collar in
the finite Abel-Plana punctured rectangle.  Its proof is the classical local
rectangle argument: apply Cauchy-Goursat on the small endpoint collar
subdomain, then identify the one curved boundary component with the
principal-value left endpoint indentation. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollarCauchy_balance
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarBoundary w T ρ =
      Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ :=
  let hlocal :=
    Complex.finiteAbelPlana_log_leftEndpointCapCollar_unnormalizedCauchy_balance
      N T hT hρ hdeleted_geometry hcont hdiff
  congrArg
    (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
    hlocal

/-- Solving the right endpoint oriented-boundary Cauchy equation gives the
right endpoint half-collar balance. -/
theorem Complex.finiteAbelPlana_log_rightEndpointHalfCollar_balance_of_orientedBoundary_zero
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ)
    (hboundary :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0) :
    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
        let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
  sub_eq_zero.mp hboundary

/-- Cauchy-Goursat on the right endpoint cap/collar domain, with the boundary
orientation identified with the existing named side and indentation integrals.

This is the exact local classical proof obligation: apply Cauchy-Goursat to the
punctured cap/collar domain and match its oriented boundary to the lower collar,
upper collar, principal-value right edge, adjacent safe-strip vertical edge, and
left semicircular indentation at the right endpoint. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 :=
  Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero_owner
    N T hT hρ hdeleted_geometry hcont hdiff

/-- Algebraic extraction of the right endpoint semicircle from the oriented
cap/collar boundary equation. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollar_balance_of_orientedBoundary_eq_zero
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ)
    (hboundary :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0) :
    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
        Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
      let M : ℕ := N + 1
      ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
  sub_eq_zero.mp hboundary

/-- The right endpoint oriented boundary vanishes exactly when the straight
collar boundary equals the left semicircular indentation integral. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero_iff_balance
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 ↔
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
        let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
  ⟨
    fun hboundary =>
      Complex.finiteAbelPlana_log_rightEndpointCapCollar_balance_of_orientedBoundary_eq_zero
        N w T ρ hboundary,
    fun hbalance => sub_eq_zero.mpr hbalance
  ⟩

/-- Unnormalized local Cauchy-Goursat balance for the right endpoint collar.

The contour is the right endpoint cap/collar subdomain: the lower horizontal
collar from `N + 1 - ρ` to `N + 1`, the principal-value right vertical edge,
the upper horizontal collar with opposite orientation, the adjacent safe-strip
vertical edge with opposite orientation, and the left semicircular indentation
around the deleted endpoint pole.  Cauchy's theorem on that punctured collar
says the sum of these oriented pieces is zero; equivalently, the straight
cap/collar boundary equals the endpoint indentation integral with the displayed
orientation. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollar_unnormalizedCauchy_balance
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
        Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
      let M : ℕ := N + 1
      ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
  let hboundary :=
    Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero
      N T hT hρ hdeleted_geometry hcont hdiff
  Complex.finiteAbelPlana_log_rightEndpointCapCollar_balance_of_orientedBoundary_eq_zero
    N w T ρ hboundary

/-- The right endpoint collar, together with the adjacent safe-strip boundary
pieces, contributes exactly the right endpoint deleted semicircle.

This is the right endpoint version of the local collar Cauchy-Goursat
calculation.  The ordinary straight edges cancel against the adjacent strip
orientation; the surviving curved boundary is the right endpoint indentation. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollarCauchy_balance
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary N w T ρ =
      Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ :=
  let hlocal :=
    Complex.finiteAbelPlana_log_rightEndpointCapCollar_unnormalizedCauchy_balance
      N T hT hρ hdeleted_geometry hcont hdiff
  congrArg
    (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
    hlocal

end

end LFunctions
end Boundary
