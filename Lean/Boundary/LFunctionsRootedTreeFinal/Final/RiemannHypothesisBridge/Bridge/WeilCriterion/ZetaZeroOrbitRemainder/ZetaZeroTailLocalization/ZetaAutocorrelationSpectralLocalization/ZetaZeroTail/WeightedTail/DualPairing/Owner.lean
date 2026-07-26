import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Coordinate

/-!
# Completed-zero `l1`--`linfinity` dual pairing

This owner gives the absolutely convergent pairing used by the completed-zero
annihilator argument.  Its convergence proof is the endpoint estimate: every
`linfinity` coordinate is bounded by its supremum norm, while the other
coordinate family has a summable norm series.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

open scoped ENNReal

/-- The endpoint product series of a bounded completed-zero family and an
absolutely summable completed-zero family is summable. -/
theorem summable_zetaCompletedZeroSideL1DualProduct
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (x : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :
    Summable (fun rho : ZetaCompletedZeroCoordinate => b rho * x rho) := by
  have hcoordinateBound :
      forall rho : ZetaCompletedZeroCoordinate, norm (b rho) <= norm b := by
    intro rho
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero b rho
  have honeToReal : (1 : ENNReal).toReal = 1 := ENNReal.one_toReal
  have hpositiveOne : 0 < (1 : ENNReal).toReal := by
    exact
      Eq.mpr
        (congrArg (fun exponent : ℝ => 0 < exponent) honeToReal)
        Real.zero_lt_one
  have hpowerSeries :
      Summable
        (fun rho : ZetaCompletedZeroCoordinate =>
          norm (x rho) ^ (1 : ENNReal).toReal) := by
    exact (lp.hasSum_norm hpositiveOne x).summable
  have hpowerEqNorm :
      (fun rho : ZetaCompletedZeroCoordinate =>
        norm (x rho) ^ (1 : ENNReal).toReal) =
        (fun rho : ZetaCompletedZeroCoordinate => norm (x rho)) := by
    funext rho
    calc
      norm (x rho) ^ (1 : ENNReal).toReal = norm (x rho) ^ (1 : ℝ) := by
        exact congrArg (fun exponent : ℝ => norm (x rho) ^ exponent) honeToReal
      _ = norm (x rho) := Real.rpow_one (norm (x rho))
  have hnormSeries :
      Summable (fun rho : ZetaCompletedZeroCoordinate => norm (x rho)) := by
    have hsummableTransport :
        Summable
            (fun rho : ZetaCompletedZeroCoordinate =>
              norm (x rho) ^ (1 : ENNReal).toReal) =
          Summable
            (fun rho : ZetaCompletedZeroCoordinate => norm (x rho)) :=
      congrArg
        (fun series : ZetaCompletedZeroCoordinate → ℝ => Summable series)
        hpowerEqNorm
    exact Eq.mp hsummableTransport hpowerSeries
  have hmajorant :
      Summable (fun rho : ZetaCompletedZeroCoordinate => norm b * norm (x rho)) :=
    hnormSeries.mul_left (norm b)
  exact
    Summable.of_norm_bounded
      (fun rho : ZetaCompletedZeroCoordinate => norm b * norm (x rho))
      hmajorant
      (fun rho =>
        calc
          norm (b rho * x rho) = norm (b rho) * norm (x rho) :=
            norm_mul (b rho) (x rho)
          _ <= norm b * norm (x rho) :=
            mul_le_mul_of_nonneg_right
              (hcoordinateBound rho)
              (norm_nonneg (x rho)))

/-- The canonical endpoint dual pairing for completed-zero coordinate families. -/
noncomputable def zetaCompletedZeroSideL1DualPairing
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (x : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) : ℂ :=
  tsum (fun rho : ZetaCompletedZeroCoordinate => b rho * x rho)

/-- The series defining the completed-zero endpoint pairing is absolutely convergent. -/
theorem zetaCompletedZeroSideL1DualPairing_summable
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (x : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :
    Summable (fun rho : ZetaCompletedZeroCoordinate => b rho * x rho) := by
  exact summable_zetaCompletedZeroSideL1DualProduct b x

/-- The completed-zero endpoint pairing satisfies the usual `linfinity`--`l1`
norm bound. -/
theorem norm_zetaCompletedZeroSideL1DualPairing_le
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (x : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :
    norm (zetaCompletedZeroSideL1DualPairing b x) <= norm b * norm x := by
  have hcoordinateBound :
      forall rho : ZetaCompletedZeroCoordinate, norm (b rho) <= norm b := by
    intro rho
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero b rho
  have honeToReal : (1 : ENNReal).toReal = 1 := ENNReal.one_toReal
  have hpositiveOne : 0 < (1 : ENNReal).toReal := by
    exact
      Eq.mpr
        (congrArg (fun exponent : ℝ => 0 < exponent) honeToReal)
        Real.zero_lt_one
  have hpowerHasSum :
      HasSum
        (fun rho : ZetaCompletedZeroCoordinate =>
          norm (x rho) ^ (1 : ENNReal).toReal)
        (norm x ^ (1 : ENNReal).toReal) := by
    exact lp.hasSum_norm hpositiveOne x
  have hpowerEqNorm :
      (fun rho : ZetaCompletedZeroCoordinate =>
        norm (x rho) ^ (1 : ENNReal).toReal) =
        (fun rho : ZetaCompletedZeroCoordinate => norm (x rho)) := by
    funext rho
    calc
      norm (x rho) ^ (1 : ENNReal).toReal = norm (x rho) ^ (1 : ℝ) := by
        exact congrArg (fun exponent : ℝ => norm (x rho) ^ exponent) honeToReal
      _ = norm (x rho) := Real.rpow_one (norm (x rho))
  have htargetEqNorm : norm x ^ (1 : ENNReal).toReal = norm x := by
    calc
      norm x ^ (1 : ENNReal).toReal = norm x ^ (1 : ℝ) := by
        exact congrArg (fun exponent : ℝ => norm x ^ exponent) honeToReal
      _ = norm x := Real.rpow_one (norm x)
  have hnormHasSum :
      HasSum
        (fun rho : ZetaCompletedZeroCoordinate => norm (x rho))
        (norm x) := by
    have htargetTransport :
        HasSum
          (fun rho : ZetaCompletedZeroCoordinate =>
            norm (x rho) ^ (1 : ENNReal).toReal)
          (norm x) := by
      have htargetProposition :
          HasSum
              (fun rho : ZetaCompletedZeroCoordinate =>
                norm (x rho) ^ (1 : ENNReal).toReal)
              (norm x ^ (1 : ENNReal).toReal) =
            HasSum
              (fun rho : ZetaCompletedZeroCoordinate =>
                norm (x rho) ^ (1 : ENNReal).toReal)
              (norm x) :=
        congrArg
          (fun total : ℝ =>
            HasSum
              (fun rho : ZetaCompletedZeroCoordinate =>
                norm (x rho) ^ (1 : ENNReal).toReal)
              total)
          htargetEqNorm
      exact Eq.mp htargetProposition hpowerHasSum
    have hseriesProposition :
        HasSum
            (fun rho : ZetaCompletedZeroCoordinate =>
              norm (x rho) ^ (1 : ENNReal).toReal)
            (norm x) =
          HasSum
            (fun rho : ZetaCompletedZeroCoordinate => norm (x rho))
            (norm x) :=
      congrArg
        (fun series : (ZetaCompletedZeroCoordinate → ℝ) =>
          HasSum series (norm x))
        hpowerEqNorm
    exact Eq.mp hseriesProposition htargetTransport
  have hmajorant :
      Summable (fun rho : ZetaCompletedZeroCoordinate => norm b * norm (x rho)) :=
    hnormHasSum.summable.mul_left (norm b)
  have htermBound :
      forall rho : ZetaCompletedZeroCoordinate,
        norm (b rho * x rho) <= norm b * norm (x rho) := by
    intro rho
    calc
      norm (b rho * x rho) = norm (b rho) * norm (x rho) :=
        norm_mul (b rho) (x rho)
      _ <= norm b * norm (x rho) :=
        mul_le_mul_of_nonneg_right
          (hcoordinateBound rho)
          (norm_nonneg (x rho))
  have htsumBound :
      norm (tsum (fun rho : ZetaCompletedZeroCoordinate => b rho * x rho)) <=
        tsum (fun rho : ZetaCompletedZeroCoordinate => norm b * norm (x rho)) := by
    exact tsum_of_norm_bounded hmajorant.hasSum htermBound
  have hmajorantTsum :
      tsum (fun rho : ZetaCompletedZeroCoordinate => norm b * norm (x rho)) =
        norm b * norm x := by
    exact Eq.trans (hnormHasSum.summable.tsum_mul_left (norm b))
      (congrArg (fun total : ℝ => norm b * total) hnormHasSum.tsum_eq)
  unfold zetaCompletedZeroSideL1DualPairing
  exact htsumBound.trans_eq hmajorantTsum

/-- The bounded completed-zero coefficient family acts linearly on the discrete
`l1` coordinate space. -/
noncomputable def zetaCompletedZeroSideL1DualLinearMap
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal)) :
    lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →ₗ[ℂ] ℂ where
  toFun := zetaCompletedZeroSideL1DualPairing b
  map_add' := by
    intro x y
    have hx :
        Summable (fun rho : ZetaCompletedZeroCoordinate => b rho * x rho) :=
      zetaCompletedZeroSideL1DualPairing_summable b x
    have hy :
        Summable (fun rho : ZetaCompletedZeroCoordinate => b rho * y rho) :=
      zetaCompletedZeroSideL1DualPairing_summable b y
    unfold zetaCompletedZeroSideL1DualPairing
    calc
      tsum (fun rho : ZetaCompletedZeroCoordinate => b rho * (x + y) rho) =
          tsum (fun rho : ZetaCompletedZeroCoordinate =>
            b rho * x rho + b rho * y rho) := by
              exact
                tsum_congr
                  (fun rho =>
                    mul_add (b rho) (x rho) (y rho))
      _ =
          tsum (fun rho : ZetaCompletedZeroCoordinate => b rho * x rho) +
            tsum (fun rho : ZetaCompletedZeroCoordinate => b rho * y rho) := by
              exact tsum_add hx hy
  map_smul' := by
    intro c x
    have hx :
        Summable (fun rho : ZetaCompletedZeroCoordinate => b rho * x rho) :=
      zetaCompletedZeroSideL1DualPairing_summable b x
    unfold zetaCompletedZeroSideL1DualPairing
    calc
      tsum (fun rho : ZetaCompletedZeroCoordinate => b rho * (c • x) rho) =
          tsum (fun rho : ZetaCompletedZeroCoordinate =>
            c * (b rho * x rho)) := by
              exact
                tsum_congr
                  (fun rho =>
                    calc
                      b rho * (c • x) rho = b rho * (c * x rho) := rfl
                      _ = (b rho * c) * x rho :=
                        (mul_assoc (b rho) c (x rho)).symm
                      _ = (c * b rho) * x rho := by
                        exact
                          congrArg
                            (fun coefficient : ℂ => coefficient * x rho)
                            (mul_comm (b rho) c)
                      _ = c * (b rho * x rho) :=
                        mul_assoc c (b rho) (x rho))
      _ = c * tsum (fun rho : ZetaCompletedZeroCoordinate => b rho * x rho) := by
            exact hx.tsum_mul_left c

/-- The bounded completed-zero coefficient family defines a continuous linear
functional on the discrete `l1` coordinate space. -/
noncomputable def zetaCompletedZeroSideL1DualContinuousLinearMap
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal)) :
    lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    (zetaCompletedZeroSideL1DualLinearMap b)
    (norm b)
    (fun x => norm_zetaCompletedZeroSideL1DualPairing_le b x)

/-- The continuous dual map is definitionally the completed-zero endpoint pairing. -/
theorem zetaCompletedZeroSideL1DualContinuousLinearMap_apply
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (x : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :
    zetaCompletedZeroSideL1DualContinuousLinearMap b x =
      zetaCompletedZeroSideL1DualPairing b x := by
  rfl

/-- Pairing with a one-coordinate `l1` vector extracts the corresponding bounded
completed-zero coefficient. -/
theorem zetaCompletedZeroSideL1DualPairing_single
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (a : ℂ) :
    zetaCompletedZeroSideL1DualPairing
        b
        (lp.single (1 : ENNReal) rho a) =
      b rho * a := by
  let singleCoordinate :
      lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) :=
    lp.single (1 : ENNReal) rho a
  have hsingleDefinition :
      singleCoordinate =
        (lp.single (1 : ENNReal) rho a :
          lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) := rfl
  have hsingleOffCoordinate :
      forall eta : ZetaCompletedZeroCoordinate, eta ≠ rho →
        singleCoordinate eta = 0 := by
    intro eta heta
    exact
      Eq.trans
        (congrArg (fun vector => vector eta) hsingleDefinition)
        (show
          (lp.single (1 : ENNReal) rho a :
              lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) eta = 0
          from
            lp.single_apply_ne
              (E := fun _ : ZetaCompletedZeroCoordinate => ℂ)
              (1 : ENNReal)
              rho
              a
              heta)
  have hsingleAtCoordinate : singleCoordinate rho = a := by
    exact
      Eq.trans
        (congrArg (fun vector => vector rho) hsingleDefinition)
        (show
          (lp.single (1 : ENNReal) rho a :
              lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) rho = a
          from
            lp.single_apply_self
              (E := fun _ : ZetaCompletedZeroCoordinate => ℂ)
              (1 : ENNReal)
              rho
              a)
  have hpairingDefinition :
      zetaCompletedZeroSideL1DualPairing
          b
          (lp.single (1 : ENNReal) rho a) =
        zetaCompletedZeroSideL1DualPairing b singleCoordinate := by
    exact
      congrArg
        (fun vector => zetaCompletedZeroSideL1DualPairing b vector)
        hsingleDefinition.symm
  have hsinglePairing :
      zetaCompletedZeroSideL1DualPairing b singleCoordinate = b rho * a := by
    unfold zetaCompletedZeroSideL1DualPairing
    calc
      tsum (fun eta : ZetaCompletedZeroCoordinate =>
          b eta * singleCoordinate eta) =
        b rho * singleCoordinate rho := by
          exact
            tsum_eq_single
              rho
              (fun eta heta =>
                calc
                  b eta * singleCoordinate eta = b eta * 0 := by
                    exact
                      congrArg
                        (fun z : ℂ => b eta * z)
                        (hsingleOffCoordinate eta heta)
                  _ = 0 := mul_zero (b eta))
      _ = b rho * a := by
        exact
          congrArg
            (fun z : ℂ => b rho * z)
            hsingleAtCoordinate
  exact hpairingDefinition.trans hsinglePairing

/-- A bounded completed-zero family that annihilates every discrete `l1` vector
is identically zero. -/
theorem zetaCompletedZeroSideL1DualPairing_eq_zero_of_forall_eq_zero
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hvanishing :
      forall x : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal),
        zetaCompletedZeroSideL1DualPairing b x = 0) :
    b = 0 := by
  apply lp.ext
  funext rho
  have hsingle :
      zetaCompletedZeroSideL1DualPairing
          b
          (lp.single (1 : ENNReal) rho (1 : ℂ)) = 0 :=
    hvanishing (lp.single (1 : ENNReal) rho (1 : ℂ))
  have hproduct : b rho * (1 : ℂ) = 0 :=
    (zetaCompletedZeroSideL1DualPairing_single b rho (1 : ℂ)).symm.trans hsingle
  calc
    b rho = b rho * (1 : ℂ) := (mul_one (b rho)).symm
    _ = 0 := hproduct

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
