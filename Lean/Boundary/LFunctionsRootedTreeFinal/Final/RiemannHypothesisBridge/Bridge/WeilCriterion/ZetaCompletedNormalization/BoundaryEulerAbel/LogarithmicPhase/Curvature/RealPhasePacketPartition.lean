import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCore

/-!
# Real-phase logarithmic derivative-packet partition

This file owns the stationary/endpoint partition of active derivative packets
for the real logarithmic phase.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Stationary point for the logarithmic phase frequency equation
`φ'(x) = m`, in the negative-frequency branch. -/
def Complex.logarithmicPhaseRealPhase_stationaryPoint
    (t : ℝ)
    (m : ℤ) : ℝ :=
  ‖t‖ / (-(m : ℝ))

/-- Negative integer frequencies have positive denominator in the stationary
point formula. -/
theorem Int.neg_cast_pos_of_lt_zero
    {m : ℤ}
    (hm : m < 0) :
    0 < -(m : ℝ) := by
  have hcast_neg : (m : ℝ) < 0 :=
    Eq.subst
      (motive := fun r : ℝ => (m : ℝ) < r)
      Int.cast_zero
      (Int.cast_lt.mpr hm)
  exact neg_pos.mpr hcast_neg

/-- In the nonnegative-parameter branch, the logarithmic phase derivative is
the negative reciprocal profile with amplitude `‖t‖`. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {x : ℝ}
    (hx_pos : 0 < x) :
    deriv
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
      -‖t‖ / x := by
  have hderiv :
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
        -t / x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
      t hx_pos
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hright : -t / x = -‖t‖ / x := by
    exact congrArg (fun r : ℝ => -r / x) hnorm.symm
  exact Eq.trans hderiv hright

/-- For nonzero logarithmic frequency and negative packet index, the
stationary point is positive. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPoint_pos
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {m : ℤ}
    (hm : m < 0) :
    0 < Complex.logarithmicPhaseRealPhase_stationaryPoint t m := by
  have ht_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hden_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm
  show 0 < ‖t‖ / (-(m : ℝ))
  exact div_pos ht_pos hden_pos

/-- The stationary point solves the reciprocal derivative equation. -/
theorem Real.logarithmicPhase_stationaryPoint_reciprocal_identity
    {T μ : ℝ}
    (hT : 0 < T)
    (hμ : 0 < μ) :
    T / (T / μ) = μ := by
  have hT_ne : T ≠ 0 :=
    ne_of_gt hT
  have hμ_ne : μ ≠ 0 :=
    ne_of_gt hμ
  calc
    T / (T / μ) = T * (T / μ)⁻¹ :=
      div_eq_mul_inv T (T / μ)
    _ = T * (T * μ⁻¹)⁻¹ := by
      exact congrArg (fun r : ℝ => T * r⁻¹) (div_eq_mul_inv T μ)
    _ = T * ((μ⁻¹)⁻¹ * T⁻¹) := by
      exact congrArg (fun r : ℝ => T * r) (mul_inv_rev T μ⁻¹)
    _ = T * (μ * T⁻¹) := by
      exact congrArg
        (fun r : ℝ => T * (r * T⁻¹))
        (inv_inv μ)
    _ = μ * (T * T⁻¹) := by
      calc
        T * (μ * T⁻¹) = (T * μ) * T⁻¹ :=
          (mul_assoc T μ T⁻¹).symm
        _ = (μ * T) * T⁻¹ := by
          exact congrArg (fun r : ℝ => r * T⁻¹) (mul_comm T μ)
        _ = μ * (T * T⁻¹) :=
          mul_assoc μ T T⁻¹
    _ = μ * 1 := by
      exact congrArg (fun r : ℝ => μ * r) (mul_inv_cancel₀ hT_ne)
    _ = μ :=
      mul_one μ

/-- At a negative integer frequency, the logarithmic stationary point has
derivative exactly equal to that frequency. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_stationaryPoint_eq
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {m : ℤ}
    (hm : m < 0) :
    deriv
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Complex.logarithmicPhaseRealPhase_stationaryPoint t m) =
      (m : ℝ) := by
  let x : ℝ := Complex.logarithmicPhaseRealPhase_stationaryPoint t m
  have hx_pos : 0 < x :=
    Complex.logarithmicPhaseRealPhase_stationaryPoint_pos t ht hm
  have hderiv :
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
        -‖t‖ / x :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div
      t ht_nonneg hx_pos
  have hT_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hden_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm
  have hrecip :
      ‖t‖ / x = -(m : ℝ) := by
    show ‖t‖ / (‖t‖ / (-(m : ℝ))) = -(m : ℝ)
    exact
      Real.logarithmicPhase_stationaryPoint_reciprocal_identity
        hT_pos hden_pos
  have hneg :
      -(‖t‖ / x) = (m : ℝ) := by
    calc
      -(‖t‖ / x) = -(-(m : ℝ)) := by
        exact congrArg Neg.neg hrecip
      _ = (m : ℝ) :=
        neg_neg (m : ℝ)
  have hneg_div :
      -‖t‖ / x = -(‖t‖ / x) :=
    neg_div x ‖t‖
  exact Eq.trans hderiv (Eq.trans hneg_div hneg)

/-- Active logarithmic derivative-packet frequencies whose stationary point
lies in the ambient real interval. -/
def Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets
    (t : ℝ)
    (a b : ℕ) : Finset ℤ :=
  (Complex.realPhase_secondDerivative_vdc_activeDerivPackets
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
    a b).filter
    (fun m : ℤ =>
      (m < 0) ∧
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
          Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))

/-- Active logarithmic derivative-packet frequencies whose stationary point is
outside the ambient interval.  These are the endpoint tails in the B-process
decomposition. -/
def Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets
    (t : ℝ)
    (a b : ℕ) : Finset ℤ :=
  (Complex.realPhase_secondDerivative_vdc_activeDerivPackets
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
    a b).filter
    (fun m : ℤ =>
      ¬ ((m < 0) ∧
          Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
            Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))

/-- Endpoint packets with nonnegative packet index form the right endpoint
tail. -/
def Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets
    (t : ℝ)
    (a b : ℕ) : Finset ℤ :=
  (Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b).filter
    (fun m : ℤ => 0 ≤ m)

/-- Endpoint packets with negative packet index and stationary point left of
the block form the left endpoint tail. -/
def Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets
    (t : ℝ)
    (a b : ℕ) : Finset ℤ :=
  (Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b).filter
    (fun m : ℤ =>
      m < 0 ∧
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m < (a : ℝ))

/-- Endpoint packets with negative packet index and stationary point to the
right of the block form the far-right endpoint tail. -/
def Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets
    (t : ℝ)
    (a b : ℕ) : Finset ℤ :=
  (Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b).filter
    (fun m : ℤ =>
      m < 0 ∧
        ((b + 1 : ℕ) : ℝ) <
          Complex.logarithmicPhaseRealPhase_stationaryPoint t m)

/-- The stationary and endpoint packet sets partition the active logarithmic
derivative frequencies. -/
theorem Complex.logarithmicPhaseRealPhase_activeDerivPackets_eq_stationary_union_endpoint
    (t : ℝ)
    (a b : ℕ) :
    Complex.realPhase_secondDerivative_vdc_activeDerivPackets
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b =
      Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b ∪
        Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b := by
  exact Finset.ext
    (fun m =>
      Iff.intro
        (fun hm =>
          match Classical.em
              ((m < 0) ∧
                Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
                  Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) with
          | Or.inl hstat =>
              Finset.mem_union.mpr
                (Or.inl
                  (Finset.mem_filter.mpr
                    (And.intro hm hstat)))
          | Or.inr hnot =>
              Finset.mem_union.mpr
                (Or.inr
                  (Finset.mem_filter.mpr
                    (And.intro hm hnot))))
        (fun hm =>
          match Finset.mem_union.mp hm with
          | Or.inl hleft =>
              (Finset.mem_filter.mp hleft).1
          | Or.inr hright =>
              (Finset.mem_filter.mp hright).1))

/-- The stationary and endpoint packet sets are disjoint. -/
theorem Complex.logarithmicPhaseRealPhase_stationary_endpoint_disjoint
    (t : ℝ)
    (a b : ℕ) :
    Disjoint
      (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b)
      (Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b) := by
  exact Finset.disjoint_left.mpr
    (fun m hm_stat hm_end =>
      have hstat :
          (m < 0) ∧
            Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
              Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
        (Finset.mem_filter.mp hm_stat).2
      have hnot :
          ¬ ((m < 0) ∧
              Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
                Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :=
        (Finset.mem_filter.mp hm_end).2
      hnot hstat)

/-- A stationary filtered packet is active. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_mem_active
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b) :
    m ∈
      Complex.realPhase_secondDerivative_vdc_activeDerivPackets
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b :=
  (Finset.mem_filter.mp hm).1

/-- A stationary filtered packet has a negative derivative frequency. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_index_neg
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b) :
    m < 0 :=
  ((Finset.mem_filter.mp hm).2).1

/-- A stationary filtered packet has its explicit stationary point in the
ambient block interval. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_point_mem_Icc
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b) :
    Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
      Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
  ((Finset.mem_filter.mp hm).2).2

end

end LFunctions
end Boundary
