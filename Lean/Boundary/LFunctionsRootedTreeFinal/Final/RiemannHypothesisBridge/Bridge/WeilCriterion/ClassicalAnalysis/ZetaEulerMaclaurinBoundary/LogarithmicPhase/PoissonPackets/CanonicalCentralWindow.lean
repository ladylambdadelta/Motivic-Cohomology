import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CanonicalWindows

/-!
# Canonical central stationary windows

This owner isolates the continuous central integral of a logarithmic Poisson
packet. Its endpoints are the mode-dependent `sqrt x_m` window endpoints,
and its norm is controlled directly by its geometric width.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhasePoissonCanonicalWindowLeft
    (t : ℝ) (m : ℤ) : ℝ :=
  Complex.logarithmicPhaseFourierStationaryPoint t m -
    Complex.logarithmicPhasePoissonCanonicalRadius t m

def Complex.logarithmicPhasePoissonCanonicalWindowRight
    (t : ℝ) (m : ℤ) : ℝ :=
  Complex.logarithmicPhaseFourierStationaryPoint t m +
    Complex.logarithmicPhasePoissonCanonicalRadius t m

def Complex.logarithmicPhasePoissonCanonicalWindowWidth
    (t : ℝ) (m : ℤ) : ℝ :=
  Complex.logarithmicPhasePoissonCanonicalWindowRight t m -
    Complex.logarithmicPhasePoissonCanonicalWindowLeft t m

def Complex.logarithmicPhasePoissonCanonicalCentralIntegral
    (t : ℝ) (a b m : ℤ) : ℂ :=
  ∫ x in Complex.logarithmicPhasePoissonCanonicalWindowLeft t m..
      Complex.logarithmicPhasePoissonCanonicalWindowRight t m,
    Complex.phaseCutoffFrequencyTwistIntegrand
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.integerBlockCutoff a b) m x

theorem Complex.logarithmicPhasePoissonCanonicalWindowLeft_eq
    (t : ℝ) (m : ℤ) :
    Complex.logarithmicPhasePoissonCanonicalWindowLeft t m =
      Complex.logarithmicPhaseFourierStationaryPoint t m -
        Complex.logarithmicPhasePoissonCanonicalRadius t m :=
  rfl

theorem Complex.logarithmicPhasePoissonCanonicalWindowRight_eq
    (t : ℝ) (m : ℤ) :
    Complex.logarithmicPhasePoissonCanonicalWindowRight t m =
      Complex.logarithmicPhaseFourierStationaryPoint t m +
        Complex.logarithmicPhasePoissonCanonicalRadius t m :=
  rfl

theorem Complex.logarithmicPhasePoissonCanonicalWindowLeft_le_center
    (t : ℝ) (m : ℤ) :
    Complex.logarithmicPhasePoissonCanonicalWindowLeft t m ≤
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  unfold Complex.logarithmicPhasePoissonCanonicalWindowLeft
  exact
    sub_le_self _
      (Complex.logarithmicPhasePoissonCanonicalRadius_nonneg t m)

theorem Complex.logarithmicPhasePoissonCanonicalWindowCenter_le_right
    (t : ℝ) (m : ℤ) :
    Complex.logarithmicPhaseFourierStationaryPoint t m ≤
      Complex.logarithmicPhasePoissonCanonicalWindowRight t m := by
  unfold Complex.logarithmicPhasePoissonCanonicalWindowRight
  exact
    le_add_of_nonneg_right
      (Complex.logarithmicPhasePoissonCanonicalRadius_nonneg t m)

theorem Complex.logarithmicPhasePoissonCanonicalWindowWidth_nonneg
    (t : ℝ) (m : ℤ) :
    0 ≤ Complex.logarithmicPhasePoissonCanonicalWindowWidth t m := by
  unfold Complex.logarithmicPhasePoissonCanonicalWindowWidth
  exact
    sub_nonneg.mpr
      (le_trans
        (Complex.logarithmicPhasePoissonCanonicalWindowLeft_le_center t m)
        (Complex.logarithmicPhasePoissonCanonicalWindowCenter_le_right t m))

theorem Complex.logarithmicPhasePoissonCanonicalWindow_bounds_of_mem
    (t : ℝ) (a b m : ℤ)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    (a : ℝ) ≤ Complex.logarithmicPhasePoissonCanonicalWindowLeft t m ∧
      Complex.logarithmicPhasePoissonCanonicalWindowRight t m ≤ (b : ℝ) := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
      t a b m).mp hm
  exact
    And.intro hmem.2.2.1 hmem.2.2.2

theorem Complex.norm_logarithmicPhasePoissonCanonicalCentralIntegral_le_width
    (t : ℝ) (a b m : ℤ)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    ‖Complex.logarithmicPhasePoissonCanonicalCentralIntegral t a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalWindowWidth t m := by
  have hbounds :=
    Complex.logarithmicPhasePoissonCanonicalWindow_bounds_of_mem
      t a b m hm
  have hradius_nonneg :
      0 ≤ Complex.logarithmicPhasePoissonCanonicalRadius t m :=
    Complex.logarithmicPhasePoissonCanonicalRadius_nonneg t m
  exact
    Complex.norm_intervalIntegral_logarithmicPhase_packet_centralWindow_le_two_radius
      t a b m
      (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhasePoissonCanonicalRadius t m)
      hbounds.1 hbounds.2 hradius_nonneg

end
end LFunctions
end Boundary
