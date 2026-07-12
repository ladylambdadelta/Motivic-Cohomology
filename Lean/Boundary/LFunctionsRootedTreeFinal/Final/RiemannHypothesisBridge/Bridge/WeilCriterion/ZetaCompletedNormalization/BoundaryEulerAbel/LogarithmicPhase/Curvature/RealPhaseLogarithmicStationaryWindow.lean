import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.CorrectedFrequencyStationary

namespace Boundary
namespace LFunctions

noncomputable section

/-!
# Continuous logarithmic stationary windows

This file names the continuous window geometry used by the Poisson packet
owner.  The stationary center is definitionally the center already owned by
`CorrectedFrequencyStationary`; the additional names here make the packet
proof graph explicit without introducing a second stationary-point
construction.
-/

def Complex.logarithmicPhasePacketCenter
    (t : ℝ) (m : ℤ) : ℝ :=
  ‖t‖ / (2 * Real.pi * (-(m : ℝ)))

theorem Complex.logarithmicPhasePacketCenter_eq_fourierStationaryPoint
    (t : ℝ) (m : ℤ) :
    Complex.logarithmicPhasePacketCenter t m =
      Complex.logarithmicPhaseFourierStationaryPoint t m :=
  rfl

theorem Complex.logarithmicPhasePacketCenter_pos
    (t : ℝ) (m : ℤ)
    (ht : 1 ≤ ‖t‖) (hm : m < 0) :
    0 < Complex.logarithmicPhasePacketCenter t m := by
  exact
    Complex.logarithmicPhaseFourierStationaryPoint_pos
      t ht hm

def Complex.logarithmicPhasePacketTwistedDerivative
    (t : ℝ) (m : ℤ) (x : ℝ) : ℝ :=
  Complex.logarithmicPhaseFourierTwistedDerivative t m x

theorem Complex.logarithmicPhasePacketTwistedDerivative_eq
    (t : ℝ) (m : ℤ) (x : ℝ) :
    Complex.logarithmicPhasePacketTwistedDerivative t m x =
      -‖t‖ / x - Real.integerAngularFrequency m :=
  rfl

/-- The continuous phase whose integer Fourier packet is indexed by `m`.
The normalization is inherited from the finite B-process: the integer mode
subtracts `2πm x` from the logarithmic real phase. -/
def Complex.logarithmicPhasePacketTwistedPhase
    (t : ℝ) (m : ℤ) : ℝ → ℝ :=
  Complex.realPhaseFrequencyTwist
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) m

theorem Complex.logarithmicPhasePacketTwistedPhase_eq
    (t : ℝ) (m : ℤ) (x : ℝ) :
    Complex.logarithmicPhasePacketTwistedPhase t m x =
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x -
        Real.integerAngularFrequency m * x :=
  rfl

/-- On the positive half-line the derivative of the packet phase is the
corrected Fourier derivative.  The nonnegative-frequency hypothesis is
essential: replacing `t` by `‖t‖` without it would be false. -/
theorem Complex.logarithmicPhasePacketTwistedPhase_deriv
    (t : ℝ) (ht_nonneg : 0 ≤ t) (m : ℤ) {x : ℝ} (hx : 0 < x) :
    deriv (Complex.logarithmicPhasePacketTwistedPhase t m) x =
      Complex.logarithmicPhasePacketTwistedDerivative t m x := by
  have hphase :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_hasDerivAt
      t hx
  have htwist :=
    Complex.hasDerivAt_realPhaseFrequencyTwist m hphase
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hderivative :
      -t / x - Real.integerAngularFrequency m =
        -‖t‖ / x - Real.integerAngularFrequency m :=
    congrArg
      (fun value : ℝ => -value / x - Real.integerAngularFrequency m)
      hnorm.symm
  have hderiv :
      deriv (Complex.logarithmicPhasePacketTwistedPhase t m) x =
        -t / x - Real.integerAngularFrequency m :=
    htwist.deriv
  exact
    hderiv.trans
      (Eq.trans hderivative
        (Complex.logarithmicPhasePacketTwistedDerivative_eq t m x).symm)

theorem Complex.logarithmicPhasePacketTwistedPhase_hasDerivAt_stationary
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) {m : ℤ} (hm : m < 0) :
    HasDerivAt (Complex.logarithmicPhasePacketTwistedPhase t m) 0
      (Complex.logarithmicPhasePacketCenter t m) := by
  exact
    Complex.logarithmicPhaseRealPhase_fourierStationaryPoint_is_stationary
      t ht ht_nonneg hm

theorem Complex.logarithmicPhasePacketTwistedPhase_deriv_stationary
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) {m : ℤ} (hm : m < 0) :
    deriv (Complex.logarithmicPhasePacketTwistedPhase t m)
      (Complex.logarithmicPhasePacketCenter t m) = 0 := by
  exact
    (Complex.logarithmicPhasePacketTwistedPhase_hasDerivAt_stationary
      t ht ht_nonneg hm).deriv

theorem Complex.logarithmicPhasePacketTwistedDerivative_hasDerivAt
    (t : ℝ) (ht_nonneg : 0 ≤ t) (m : ℤ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (Complex.logarithmicPhasePacketTwistedDerivative t m)
      (‖t‖ / x ^ 2) x := by
  exact
    Complex.logarithmicPhaseFourierTwistedDerivative_hasDerivAt
      t ht_nonneg m hx

theorem Complex.logarithmicPhasePacketTwistedDerivative_deriv
    (t : ℝ) (ht_nonneg : 0 ≤ t) (m : ℤ) {x : ℝ} (hx : 0 < x) :
    deriv (Complex.logarithmicPhasePacketTwistedDerivative t m) x =
      ‖t‖ / x ^ 2 := by
  exact
    (Complex.logarithmicPhasePacketTwistedDerivative_hasDerivAt
      t ht_nonneg m hx).deriv

def Complex.logarithmicPhaseStationaryWindow
    (t : ℝ) (m : ℤ) (a b : ℕ) : Set ℝ :=
  Set.Icc
    (max (a : ℝ)
      (Complex.logarithmicPhasePacketCenter t m -
        Real.sqrt (Complex.logarithmicPhasePacketCenter t m)))
    (min (b : ℝ)
      (Complex.logarithmicPhasePacketCenter t m +
        Real.sqrt (Complex.logarithmicPhasePacketCenter t m)))

theorem Complex.logarithmicPhaseStationaryWindow_mem_iff
    (t : ℝ) (m : ℤ) (a b : ℕ) (x : ℝ) :
    x ∈ Complex.logarithmicPhaseStationaryWindow t m a b ↔
      max (a : ℝ)
          (Complex.logarithmicPhasePacketCenter t m -
            Real.sqrt (Complex.logarithmicPhasePacketCenter t m)) ≤ x ∧
      x ≤ min (b : ℝ)
          (Complex.logarithmicPhasePacketCenter t m +
            Real.sqrt (Complex.logarithmicPhasePacketCenter t m)) :=
  Iff.rfl

theorem Complex.logarithmicPhaseStationaryWindow_subset_support
    (t : ℝ) (m : ℤ) (a b : ℕ) :
    Complex.logarithmicPhaseStationaryWindow t m a b ⊆
      Set.Icc (a : ℝ) (b : ℝ) := by
  intro x hx
  have hleft :
      (a : ℝ) ≤
        max (a : ℝ)
          (Complex.logarithmicPhasePacketCenter t m -
            Real.sqrt (Complex.logarithmicPhasePacketCenter t m)) :=
    le_max_left _ _
  have hright :
      min (b : ℝ)
          (Complex.logarithmicPhasePacketCenter t m +
            Real.sqrt (Complex.logarithmicPhasePacketCenter t m)) ≤
        (b : ℝ) :=
    min_le_left _ _
  exact
    And.intro
      (le_trans hleft hx.1)
      (le_trans hx.2 hright)

theorem Complex.logarithmicPhasePacketCenter_stationary
    (t : ℝ) (m : ℤ)
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) (hm : m < 0) :
    deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Complex.logarithmicPhasePacketCenter t m) =
      Real.integerAngularFrequency m := by
  exact
    Complex.logarithmicPhaseRealPhase_deriv_fourierStationaryPoint_eq
      t ht ht_nonneg hm

end
end LFunctions
end Boundary
