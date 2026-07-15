import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveFarDecomposition

/-!
# Sharp assembly of all finite inactive packets

The near classes consume the quantitative balanced-window packet budget.  The
far classes consume the exact crossing-plus-reciprocal decomposition.  This
file recombines those four disjoint classes and exports the single finite
inactive budget used by the final B-process owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.add_add_add_add_add_add_reassociate
    (a b c d e f : ℝ) :
    (a + (b + c)) + (d + (e + f)) =
      (a + d) + (b + e) + (c + f) := by
  have houter :
      (a + (b + c)) + (d + (e + f)) =
        (a + d) + ((b + c) + (e + f)) :=
    add_add_add_comm a (b + c) d (e + f)
  have hinner :
      (b + c) + (e + f) = (b + e) + (c + f) :=
    add_add_add_comm b c e f
  exact Eq.trans houter
    (Eq.trans
      (congrArg (fun value : ℝ => (a + d) + value) hinner)
      (add_assoc (a + d) (b + e) (c + f)).symm)

def Complex.logarithmicPhaseFiniteInactiveSharpBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteNearQuantitativeBudget t a b +
    Complex.logarithmicPhaseFiniteFarSeparatedBudget t a b

def Complex.logarithmicPhaseFiniteInactiveSharpCrossingBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteFarCrossingBudget t a b

def Complex.logarithmicPhaseFiniteInactiveSharpStationaryBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteNearQuantitativeBudget t a b

def Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteFarReciprocalBudget t a b

theorem Complex.logarithmicPhaseFiniteInactiveSharpBudget_eq_three_parts
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseFiniteInactiveSharpBudget t a b =
      Complex.logarithmicPhaseFiniteInactiveSharpStationaryBudget t a b +
        Complex.logarithmicPhaseFiniteInactiveSharpCrossingBudget t a b +
          Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget t a b := by
  unfold Complex.logarithmicPhaseFiniteInactiveSharpBudget
  unfold Complex.logarithmicPhaseFiniteInactiveSharpStationaryBudget
  unfold Complex.logarithmicPhaseFiniteInactiveSharpCrossingBudget
  unfold Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget
  unfold Complex.logarithmicPhaseFiniteFarSeparatedBudget
  exact
    (add_assoc
      (Complex.logarithmicPhaseFiniteNearQuantitativeBudget t a b)
      (Complex.logarithmicPhaseFiniteFarCrossingBudget t a b)
      (Complex.logarithmicPhaseFiniteFarReciprocalBudget t a b)).symm

theorem Complex.logarithmicPhaseFiniteLeftNearPacketNorm_le_quantitativeBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ) (m : ℤ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes
      t (a : ℤ) (b : ℤ)) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
        t (a : ℤ) (b : ℤ) m‖ ≤
      Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
        t (a : ℤ) (b : ℤ) m := by
  have haNat :=
    Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry
  have haInt : 1 ≤ (a : ℤ) :=
    Int.ofNat_le.mpr haNat
  have habInt : (a : ℤ) ≤ (b : ℤ) :=
    Int.ofNat_le.mpr
      (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  exact
    Complex.norm_logarithmicPhaseQuantitativeFiniteLeftNearPacket_le_sharpBudget
      t ht ht_nonneg (a : ℤ) (b : ℤ) m haInt habInt hm

theorem Complex.logarithmicPhaseFiniteRightNearPacketNorm_le_quantitativeBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ) (m : ℤ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes
      t (a : ℤ) (b : ℤ)) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
        t (a : ℤ) (b : ℤ) m‖ ≤
      Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
        t (a : ℤ) (b : ℤ) m := by
  have haNat :=
    Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry
  have haInt : 1 ≤ (a : ℤ) :=
    Int.ofNat_le.mpr haNat
  have habInt : (a : ℤ) ≤ (b : ℤ) :=
    Int.ofNat_le.mpr
      (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  exact
    Complex.norm_logarithmicPhaseQuantitativeFiniteRightNearPacket_le_sharpBudget
      t ht ht_nonneg (a : ℤ) (b : ℤ) m haInt habInt hm

theorem Complex.logarithmicPhaseFiniteLeftFarPacketNorm_le_separatedPacketBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ) (m : ℤ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes
      t (a : ℤ) (b : ℤ)) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
        t (a : ℤ) (b : ℤ) m‖ ≤
      (2 / 3 : ℝ) +
        (Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) +
          Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ)) := by
  have haInt : 1 ≤ (a : ℤ) :=
    Int.ofNat_le.mpr
      (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have habInt : (a : ℤ) ≤ (b : ℤ) :=
    Int.ofNat_le.mpr
      (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hpacket :=
    Complex.norm_logarithmicPhaseQuantitativeFiniteLeftFarPacket_le_endpointBudget
      t ht ht_nonneg (a : ℤ) (b : ℤ) m haInt habInt hm
  exact le_trans hpacket
    (le_of_eq
      (Complex.logarithmicPhaseFiniteLeftFarPacketBudget_eq_crossing_add_reciprocal
        t (a : ℤ) m))

theorem Complex.logarithmicPhaseFiniteRightFarPacketNorm_le_separatedPacketBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ) (m : ℤ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightFarModes
      t (a : ℤ) (b : ℤ)) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
        t (a : ℤ) (b : ℤ) m‖ ≤
      (2 / 3 : ℝ) +
        (Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) +
          Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ)) := by
  have haInt : 1 ≤ (a : ℤ) :=
    Int.ofNat_le.mpr
      (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have habInt : (a : ℤ) ≤ (b : ℤ) :=
    Int.ofNat_le.mpr
      (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hpacket :=
    Complex.norm_logarithmicPhaseQuantitativeFiniteRightFarPacket_le_endpointBudget
      t ht ht_nonneg (a : ℤ) (b : ℤ) m haInt habInt hm
  exact le_trans hpacket
    (le_of_eq
      (Complex.logarithmicPhaseFiniteRightFarPacketBudget_eq_crossing_add_reciprocal
        t (b : ℤ) m))

theorem Complex.logarithmicPhaseFiniteLeftNearNormSum_le_quantitativeBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (∑ m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes
        t (a : ℤ) (b : ℤ),
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
        t (a : ℤ) (b : ℤ) m‖) ≤
      Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
        t (a : ℤ) (b : ℤ) := by
  unfold Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
  exact Finset.sum_le_sum (fun m hm =>
    Complex.logarithmicPhaseFiniteLeftNearPacketNorm_le_quantitativeBudget
      t ht ht_nonneg a b m hgeometry hm)

theorem Complex.logarithmicPhaseFiniteRightNearNormSum_le_quantitativeBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (∑ m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes
        t (a : ℤ) (b : ℤ),
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
        t (a : ℤ) (b : ℤ) m‖) ≤
      Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
        t (a : ℤ) (b : ℤ) := by
  unfold Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
  exact Finset.sum_le_sum (fun m hm =>
    Complex.logarithmicPhaseFiniteRightNearPacketNorm_le_quantitativeBudget
      t ht ht_nonneg a b m hgeometry hm)

theorem Complex.logarithmicPhaseFiniteLeftFarNormSum_le_separatedBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (∑ m ∈ Complex.logarithmicPhaseFiniteLeftFarModes
        t (a : ℤ) (b : ℤ),
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
        t (a : ℤ) (b : ℤ) m‖) ≤
      Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
          t (a : ℤ) (b : ℤ) +
        Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
          t (a : ℤ) (b : ℤ) := by
  have hsum := Finset.sum_le_sum (fun m hm =>
    Complex.logarithmicPhaseFiniteLeftFarPacketNorm_le_separatedPacketBudget
      t ht ht_nonneg a b m hgeometry hm)
  have hsplit := Finset.sum_add_distrib
    (s := Complex.logarithmicPhaseFiniteLeftFarModes
      t (a : ℤ) (b : ℤ))
    (f := fun _m : ℤ => (2 / 3 : ℝ))
    (g := fun m : ℤ =>
      Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) +
        Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ))
  unfold Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
  unfold Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
  exact le_trans hsum (le_of_eq hsplit)

theorem Complex.logarithmicPhaseFiniteRightFarNormSum_le_separatedBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (∑ m ∈ Complex.logarithmicPhaseFiniteRightFarModes
        t (a : ℤ) (b : ℤ),
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
        t (a : ℤ) (b : ℤ) m‖) ≤
      Complex.logarithmicPhaseFiniteRightFarCrossingBudget
          t (a : ℤ) (b : ℤ) +
        Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
          t (a : ℤ) (b : ℤ) := by
  have hsum := Finset.sum_le_sum (fun m hm =>
    Complex.logarithmicPhaseFiniteRightFarPacketNorm_le_separatedPacketBudget
      t ht ht_nonneg a b m hgeometry hm)
  have hsplit := Finset.sum_add_distrib
    (s := Complex.logarithmicPhaseFiniteRightFarModes
      t (a : ℤ) (b : ℤ))
    (f := fun _m : ℤ => (2 / 3 : ℝ))
    (g := fun m : ℤ =>
      Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) +
        Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ))
  unfold Complex.logarithmicPhaseFiniteRightFarCrossingBudget
  unfold Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
  exact le_trans hsum (le_of_eq hsplit)

theorem Complex.logarithmicPhaseQuantitativeLeftInactiveNormSum_le_sharpParts
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
          t (a : ℤ) (b : ℤ) +
        (Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
            t (a : ℤ) (b : ℤ) +
          Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
            t (a : ℤ) (b : ℤ)) := by
  let near := Complex.logarithmicPhaseFiniteLeftNearEndpointModes
    t (a : ℤ) (b : ℤ)
  let far := Complex.logarithmicPhaseFiniteLeftFarModes
    t (a : ℤ) (b : ℤ)
  let packetNorm : ℤ → ℝ := fun m =>
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
      t (a : ℤ) (b : ℤ) m‖
  have hunion := Complex.logarithmicPhaseFiniteLeftNear_union_far
    t (a : ℤ) (b : ℤ)
  have hdisjoint : Disjoint near far := by
    exact Finset.disjoint_left.mpr (fun m hnear hfar =>
      have hn :=
        (Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
          t (a : ℤ) (b : ℤ) m).mp hnear
      have hf :=
        (Complex.mem_logarithmicPhaseFiniteLeftFarModes_iff
          t (a : ℤ) (b : ℤ) m).mp hfar
      (not_lt_of_ge hn.2) hf.2)
  have hsplit :
      (∑ m in near ∪ far, packetNorm m) =
        (∑ m in near, packetNorm m) + (∑ m in far, packetNorm m) :=
    Finset.sum_union hdisjoint
  have hnear :=
    Complex.logarithmicPhaseFiniteLeftNearNormSum_le_quantitativeBudget
      t ht ht_nonneg a b hgeometry
  have hfar :=
    Complex.logarithmicPhaseFiniteLeftFarNormSum_le_separatedBudget
      t ht ht_nonneg a b hgeometry
  have hunionBound :
      (∑ m in near ∪ far, packetNorm m) ≤
        Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
            t (a : ℤ) (b : ℤ) +
          (Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
              t (a : ℤ) (b : ℤ) +
            Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
              t (a : ℤ) (b : ℤ)) :=
    Eq.subst (motive := fun value : ℝ => value ≤ _)
      hsplit.symm (add_le_add hnear hfar)
  have hinactiveBound :
      (∑ m in Complex.logarithmicPhasePoissonLeftInactiveModes
          t (a : ℤ) (b : ℤ), packetNorm m) ≤
        Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
            t (a : ℤ) (b : ℤ) +
          (Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
              t (a : ℤ) (b : ℤ) +
            Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
              t (a : ℤ) (b : ℤ)) :=
    Eq.subst
      (motive := fun modes : Finset ℤ =>
        (∑ m in modes, packetNorm m) ≤ _)
      hunion hunionBound
  unfold Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
  exact hinactiveBound

theorem Complex.logarithmicPhaseQuantitativeRightInactiveNormSum_le_sharpParts
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
          t (a : ℤ) (b : ℤ) +
        (Complex.logarithmicPhaseFiniteRightFarCrossingBudget
            t (a : ℤ) (b : ℤ) +
          Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
            t (a : ℤ) (b : ℤ)) := by
  let near := Complex.logarithmicPhaseFiniteRightNearEndpointModes
    t (a : ℤ) (b : ℤ)
  let far := Complex.logarithmicPhaseFiniteRightFarModes
    t (a : ℤ) (b : ℤ)
  let packetNorm : ℤ → ℝ := fun m =>
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
      t (a : ℤ) (b : ℤ) m‖
  have hunion := Complex.logarithmicPhaseFiniteRightNear_union_far
    t (a : ℤ) (b : ℤ)
  have hdisjoint : Disjoint near far := by
    exact Finset.disjoint_left.mpr (fun m hnear hfar =>
      have hn :=
        (Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
          t (a : ℤ) (b : ℤ) m).mp hnear
      have hf :=
        (Complex.mem_logarithmicPhaseFiniteRightFarModes_iff
          t (a : ℤ) (b : ℤ) m).mp hfar
      (not_lt_of_ge hn.2) hf.2)
  have hsplit :
      (∑ m in near ∪ far, packetNorm m) =
        (∑ m in near, packetNorm m) + (∑ m in far, packetNorm m) :=
    Finset.sum_union hdisjoint
  have hnear :=
    Complex.logarithmicPhaseFiniteRightNearNormSum_le_quantitativeBudget
      t ht ht_nonneg a b hgeometry
  have hfar :=
    Complex.logarithmicPhaseFiniteRightFarNormSum_le_separatedBudget
      t ht ht_nonneg a b hgeometry
  have hunionBound :
      (∑ m in near ∪ far, packetNorm m) ≤
        Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
            t (a : ℤ) (b : ℤ) +
          (Complex.logarithmicPhaseFiniteRightFarCrossingBudget
              t (a : ℤ) (b : ℤ) +
            Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
              t (a : ℤ) (b : ℤ)) :=
    Eq.subst (motive := fun value : ℝ => value ≤ _)
      hsplit.symm (add_le_add hnear hfar)
  have hinactiveBound :
      (∑ m in Complex.logarithmicPhasePoissonRightInactiveModes
          t (a : ℤ) (b : ℤ), packetNorm m) ≤
        Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
            t (a : ℤ) (b : ℤ) +
          (Complex.logarithmicPhaseFiniteRightFarCrossingBudget
              t (a : ℤ) (b : ℤ) +
            Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
              t (a : ℤ) (b : ℤ)) :=
    Eq.subst
      (motive := fun modes : Finset ℤ =>
        (∑ m in modes, packetNorm m) ≤ _)
      hunion hunionBound
  unfold Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
  exact hinactiveBound

theorem Complex.logarithmicPhaseFiniteInactiveNormBudgets_le_sharpBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
          t (a : ℤ) (b : ℤ) +
        Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
          t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseFiniteInactiveSharpBudget
        t (a : ℤ) (b : ℤ) := by
  have hleft :=
    Complex.logarithmicPhaseQuantitativeLeftInactiveNormSum_le_sharpParts
      t ht ht_nonneg a b hgeometry
  have hright :=
    Complex.logarithmicPhaseQuantitativeRightInactiveNormSum_le_sharpParts
      t ht ht_nonneg a b hgeometry
  have hadd := add_le_add hleft hright
  unfold Complex.logarithmicPhaseFiniteInactiveSharpBudget
  unfold Complex.logarithmicPhaseFiniteNearQuantitativeBudget
  unfold Complex.logarithmicPhaseFiniteFarSeparatedBudget
  unfold Complex.logarithmicPhaseFiniteFarCrossingBudget
  unfold Complex.logarithmicPhaseFiniteFarReciprocalBudget
  exact le_trans hadd
    (le_of_eq
      (show
        (Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
              t (a : ℤ) (b : ℤ) +
            (Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
                t (a : ℤ) (b : ℤ) +
              Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
                t (a : ℤ) (b : ℤ))) +
          (Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
              t (a : ℤ) (b : ℤ) +
            (Complex.logarithmicPhaseFiniteRightFarCrossingBudget
                t (a : ℤ) (b : ℤ) +
              Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
                t (a : ℤ) (b : ℤ))) =
          (Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
              t (a : ℤ) (b : ℤ) +
            Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
              t (a : ℤ) (b : ℤ)) +
          ((Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
                t (a : ℤ) (b : ℤ) +
              Complex.logarithmicPhaseFiniteRightFarCrossingBudget
                t (a : ℤ) (b : ℤ)) +
            (Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
                t (a : ℤ) (b : ℤ) +
              Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
                t (a : ℤ) (b : ℤ))) from by
        have hreassociate :=
          Real.add_add_add_add_add_add_reassociate
            (Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
              t (a : ℤ) (b : ℤ))
            (Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
              t (a : ℤ) (b : ℤ))
            (Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
              t (a : ℤ) (b : ℤ))
            (Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
              t (a : ℤ) (b : ℤ))
            (Complex.logarithmicPhaseFiniteRightFarCrossingBudget
              t (a : ℤ) (b : ℤ))
            (Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
              t (a : ℤ) (b : ℤ))
        exact Eq.trans hreassociate
          (add_assoc
            (Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
                t (a : ℤ) (b : ℤ) +
              Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
                t (a : ℤ) (b : ℤ))
            (Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
                t (a : ℤ) (b : ℤ) +
              Complex.logarithmicPhaseFiniteRightFarCrossingBudget
                t (a : ℤ) (b : ℤ))
            (Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
                t (a : ℤ) (b : ℤ) +
              Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
                t (a : ℤ) (b : ℤ)))))

theorem Complex.logarithmicPhaseFiniteInactiveSharpBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    0 ≤ Complex.logarithmicPhaseFiniteInactiveSharpBudget
      t (a : ℤ) (b : ℤ) := by
  have hnearLeft :=
    Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget_le_thirteen_sixths_scale
      ht ht_nonneg hgeometry
  have hnearRight :=
    Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget_le_four_thirds_scale
      ht hgeometry
  have hnearLeftNonneg :
      0 ≤ Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
        t (a : ℤ) (b : ℤ) := by
    unfold Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
    exact Finset.sum_nonneg (fun m hm =>
      le_trans (norm_nonneg _)
        (Complex.logarithmicPhaseFiniteLeftNearPacketNorm_le_quantitativeBudget
          t ht ht_nonneg a b m hgeometry hm))
  have hnearRightNonneg :
      0 ≤ Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
        t (a : ℤ) (b : ℤ) := by
    unfold Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
    exact Finset.sum_nonneg (fun m hm =>
      le_trans (norm_nonneg _)
        (Complex.logarithmicPhaseFiniteRightNearPacketNorm_le_quantitativeBudget
          t ht ht_nonneg a b m hgeometry hm))
  have hfar :=
    Complex.logarithmicPhaseFiniteFarSeparatedBudget_nonneg
      t ht (a : ℤ) (b : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_order hgeometry))
  unfold Complex.logarithmicPhaseFiniteInactiveSharpBudget
  unfold Complex.logarithmicPhaseFiniteNearQuantitativeBudget
  exact add_nonneg (add_nonneg hnearLeftNonneg hnearRightNonneg) hfar

end

end LFunctions
end Boundary
