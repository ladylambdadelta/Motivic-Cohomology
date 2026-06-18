import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.SetIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteHoleSubdivision

/-!
# Foundation lemmas for endpoint cap-collar Cauchy balances

Basic helper theorems about complex numbers and real interval bounds needed
for the endpoint cap-collar domains and integrand analysis.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

notation:max "[[" a "," b "]]" => Set.Icc a b

/-- Algebraic cancellation for the finite-hole subdivision once the cap/collar
boundary has been identified with the missing deleted-arc contribution. -/
theorem Complex.finiteAbelPlana_log_verticalStrip_add_deleted_sub_verticalStrip_sub_deleted
    (A B : ℂ) :
    A + (B - A) - B = 0 :=
  Eq.trans
    (congrArg (fun u : ℂ => u - B) (add_sub_cancel_left A B))
    (sub_self B)

/-- Left distributivity over two summands, oriented for collection. -/
theorem Complex.left_mul_add_two_collect
    (a b c : ℂ) :
    a * b + a * c = a * (b + c) :=
  (mul_add a b c).symm

/-- Left distributivity over three summands, oriented for collection. -/
theorem Complex.left_mul_add_three_collect
    (a b c d : ℂ) :
    a * b + a * c + a * d = a * (b + c + d) :=
  Eq.trans
    (congrArg (fun u : ℂ => u + a * d)
      (Complex.left_mul_add_two_collect a b c))
    (mul_add a (b + c) d).symm

/-- Atomic step 1: Flatten associativity of three-part sum. -/
theorem Complex.leftEndpointCapCollarBoundary_flatten
    (lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper
      pvLower pvUpper arc : ℂ) :
    (lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower) +
        (upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper) +
          (lowerChord - upperChord + Complex.I * safeMiddle - arc) =
      lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower +
        upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper +
        lowerChord - upperChord + Complex.I * safeMiddle - arc :=
  let a := lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower
  let b := upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper
  let c := lowerChord - upperChord + Complex.I * safeMiddle - arc
  Eq.trans (add_assoc a b c) (congrArg (a + ·) (add_assoc b c))

/-- Mathematical fact: chords cancel in sum. -/
theorem Complex.boundaryChordsCancelInSum
    (lowerChord upperChord restTerms : ℂ) :
    (-lowerChord + restTerms + upperChord) + lowerChord - upperChord =
    restTerms :=
  Eq.trans (sub_eq_add_neg ((-lowerChord + restTerms + upperChord) + lowerChord) upperChord)
    (Eq.trans (congrArg (· + (-upperChord)) (Eq.symm (add_assoc (-lowerChord + restTerms) upperChord lowerChord)))
      (Eq.trans (congrArg (· + (-upperChord)) (congrArg ((-lowerChord + restTerms) + ·) (add_comm upperChord lowerChord)))
        (Eq.trans (congrArg (· + (-upperChord)) (add_assoc (-lowerChord + restTerms) lowerChord upperChord))
          (Eq.trans (Eq.symm (add_assoc ((-lowerChord + restTerms) + lowerChord) upperChord (-upperChord)))
            (Eq.trans (congrArg (fun x => x + (-upperChord)) (Eq.symm (add_assoc (-lowerChord) restTerms lowerChord)))
              (Eq.trans (congrArg (fun x => x + (-upperChord)) (congrArg ((-lowerChord) + ·) (add_comm restTerms lowerChord)))
                (Eq.trans (congrArg (fun x => x + (-upperChord)) (add_assoc (-lowerChord) lowerChord restTerms))
                  (Eq.trans (congrArg (· + (-upperChord)) (neg_add_cancel lowerChord))
                    (Eq.trans (congrArg (fun x => x + (-upperChord)) (zero_add restTerms))
                      (add_neg_cancel upperChord ▸ add_zero restTerms)))))))))))

/-- Mathematical fact: grouping I*safe terms. -/
theorem Complex.boundaryGroupISafeTerms
    (safeLower safeMiddle safeUpper : ℂ) :
    Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper =
    Complex.I * (safeLower + safeMiddle + safeUpper) :=
  Complex.left_mul_add_three_collect Complex.I safeLower safeMiddle safeUpper

/-- Mathematical fact: grouping I*pv terms. -/
theorem Complex.boundaryGroupIPvTerms
    (pvLower pvUpper : ℂ) :
    Complex.I * pvLower + Complex.I * pvUpper =
    Complex.I * (pvLower + pvUpper) :=
  Complex.left_mul_add_two_collect Complex.I pvLower pvUpper

/-- Peeled sub-step: Pull lowerChord to front via commutativity. -/
theorem Complex.boundaryPullLowerChordFront
    (lowerT lowerChord rest : ℂ) :
    lowerT - lowerChord + rest = -lowerChord + (lowerT + rest) :=
  Eq.trans (sub_eq_add_neg lowerT lowerChord ▸ Eq.symm (add_assoc lowerT (-lowerChord) rest))
    (Eq.trans (congrArg (· + rest) (add_comm lowerT (-lowerChord)))
      (add_assoc (-lowerChord) lowerT rest).symm)

/-- Peeled sub-step: Rearrange middle terms after lowerChord pulled forward. -/
theorem Complex.boundaryRearrangeMiddleTerms
    (lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper
      pvLower pvUpper arc : ℂ) :
    -lowerChord + (lowerT - upperT + (Complex.I * safeLower - Complex.I * pvLower +
      Complex.I * safeUpper - Complex.I * pvUpper + Complex.I * safeMiddle - arc)) +
      upperChord + lowerChord - upperChord =
      -lowerChord + (lowerT - upperT + (Complex.I * safeLower - Complex.I * pvLower +
        Complex.I * safeUpper - Complex.I * pvUpper + Complex.I * safeMiddle - arc)) +
        (upperChord + lowerChord - upperChord) :=
  (add_assoc (-lowerChord + (lowerT - upperT + _)) upperChord (lowerChord - upperChord)).symm

/-- Step: Move -lowerChord to front (commutativity of first two terms). -/
theorem Complex.rearrange_move_lowerChord_front
    (lowerT lowerChord rest : ℂ) :
    lowerT + (-lowerChord) + rest = (-lowerChord) + lowerT + rest :=
  Eq.trans (add_assoc lowerT (-lowerChord) rest)
    (Eq.trans (congrArg (· + rest) (add_comm lowerT (-lowerChord)))
      ((add_assoc (-lowerChord) lowerT rest).symm))

/-- Atomic: Swap middle and final terms via commutativity. -/
theorem Complex.add_swap_middle_final
    (lowerT middleRest upperT : ℂ) :
    lowerT + (middleRest + (-upperT)) = lowerT + ((-upperT) + middleRest) :=
  congrArg (lowerT + ·) (add_comm middleRest (-upperT))

/-- Sub-sub-step: Associate T terms. -/
theorem Complex.rearrange_T_associate
    (lowerT upperT middleRest : ℂ) :
    lowerT + middleRest + (-upperT) = lowerT + (-upperT) + middleRest :=
  Eq.trans (add_assoc lowerT middleRest (-upperT))
    (Eq.trans (Complex.add_swap_middle_final lowerT middleRest upperT)
      ((add_assoc lowerT (-upperT) middleRest).symm))

/-- Step: Group T terms together in middle. -/
theorem Complex.rearrange_group_T_terms
    (lowerChord lowerT upperT middleRest rest : ℂ) :
    (-lowerChord : ℂ) + lowerT + middleRest + (-upperT) + rest =
    (-lowerChord : ℂ) + (lowerT + (-upperT) + middleRest) + rest :=
  Eq.trans (Eq.symm (add_assoc (-lowerChord) _ _))
    (Eq.trans (congrArg ((-lowerChord) + ·) (add_assoc lowerT middleRest (-upperT)))
      (Eq.trans (congrArg ((-lowerChord) + ·) (Complex.rearrange_T_associate lowerT upperT middleRest))
        (add_assoc (-lowerChord) (lowerT + (-upperT) + middleRest) rest)))

/-- Step: Group all I terms and arc in the middle section. -/
theorem Complex.rearrange_group_I_terms
    (safeLower pvLower safeUpper pvUpper safeMiddle arc : ℂ) :
    Complex.I * safeLower + (-Complex.I * pvLower) +
      Complex.I * safeUpper + (-Complex.I * pvUpper) +
      Complex.I * safeMiddle + (-arc) =
      Complex.I * safeLower + (-Complex.I * pvLower) +
        Complex.I * safeUpper + (-Complex.I * pvUpper) +
        Complex.I * safeMiddle + (-arc) :=
  rfl

/-- Sub-step: Associate chords at end. -/
theorem Complex.rearrange_chords_associate
    (upperChord lowerChord : ℂ) :
    upperChord + lowerChord + (-upperChord) = (upperChord + lowerChord + (-upperChord)) :=
  rfl

/-- Atomic: -(a) + a = 0. -/
theorem Complex.neg_add_self (a : ℂ) : (-a) + a = 0 :=
  neg_add_cancel a

/-- Atomic: a + (-a) = 0. -/
theorem Complex.add_neg_self (a : ℂ) : a + (-a) = 0 :=
  add_neg_cancel a

/-- Atomic: 0 + x = x. -/
theorem Complex.zero_add_eq (x : ℂ) : 0 + x = x :=
  zero_add x

/-- Atomic: x + 0 = x. -/
theorem Complex.add_zero_eq (x : ℂ) : x + 0 = x :=
  add_zero x

/-- Atomic: Cancel leading term with trailing negation. -/
theorem Complex.add_cancel_outer
    (a b : ℂ) :
    a + b + (-a) = b :=
  Eq.trans ((add_assoc a b (-a)).symm)
    (Eq.trans (congrArg (· + (-a)) (add_comm a b))
      (Eq.trans (add_assoc b a (-a))
        (Eq.trans (congrArg (b + ·) (add_neg_cancel a))
          (add_zero b))))

/-- Atomic: Cancel chords. -/
theorem Complex.add_chords_cancel
    (upperChord lowerChord : ℂ) :
    upperChord + lowerChord + (-upperChord) = lowerChord :=
  Complex.add_cancel_outer upperChord lowerChord

/-- Sub-sub-step: Compute chord cancellation result. -/
theorem Complex.chord_cancel_result
    (upperChord lowerChord : ℂ) :
    upperChord + lowerChord + (-upperChord) = lowerChord :=
  Complex.add_cancel_outer upperChord lowerChord

/-- Step: Rearrange middle section with chords and T properly positioned. -/
theorem Complex.rearrange_final_positioning
    (lowerChord upperChord lowerT upperT safeI pvI safeMiddleI arc : ℂ) :
    (-lowerChord) + (lowerT + (-upperT) + safeI) + upperChord + lowerChord + (-upperChord) =
    (-lowerChord) + (lowerT + (-upperT) + safeI) + (upperChord + lowerChord + (-upperChord)) :=
  (add_assoc ((-lowerChord) + (lowerT + (-upperT) + safeI)) upperChord (lowerChord + (-upperChord))).symm

/-- Sub-lemma: Rearrange to group all remaining terms. -/
theorem Complex.leftEndpointCapCollarBoundary_rearrange_grouping
    (lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper
      pvLower pvUpper arc : ℂ) :
    lowerT + (-lowerChord) + Complex.I * safeLower + (-Complex.I * pvLower) +
      upperChord + (-upperT) + Complex.I * safeUpper + (-Complex.I * pvUpper) +
      lowerChord + (-upperChord) + Complex.I * safeMiddle + (-arc) =
      (-lowerChord) + (lowerT + (-upperT) + (Complex.I * safeLower + (-Complex.I * pvLower) +
        Complex.I * safeUpper + (-Complex.I * pvUpper) + Complex.I * safeMiddle + (-arc))) +
        upperChord + lowerChord + (-upperChord) :=
  Eq.trans (Eq.symm (add_assoc lowerT _ _))
    (Eq.trans (congrArg (lowerT + ·) (Eq.symm (add_assoc (-lowerChord) _ _)))
      (Eq.trans (congrArg (fun x => (-lowerChord) + (lowerT + x)) (Eq.symm (add_assoc (-upperT) _ _)))
        (rfl)))

/-- Peeled step 2a-1: Move T terms and rest to middle, chords to outside. -/
theorem Complex.leftEndpointCapCollarBoundary_chord_rearrange_step1
    (lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper
      pvLower pvUpper arc : ℂ) :
    lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower +
      upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper +
      lowerChord - upperChord + Complex.I * safeMiddle - arc =
      -lowerChord + (lowerT - upperT + (Complex.I * safeLower - Complex.I * pvLower +
        Complex.I * safeUpper - Complex.I * pvUpper + Complex.I * safeMiddle - arc)) +
        upperChord + lowerChord - upperChord :=
  Eq.trans (subs_to_negs lowerT lowerChord (Complex.I * safeLower) (Complex.I * pvLower)
    upperChord upperT (Complex.I * safeUpper) (Complex.I * pvUpper)
    lowerChord upperChord (Complex.I * safeMiddle) arc)
    (Eq.trans (Complex.leftEndpointCapCollarBoundary_rearrange_grouping lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper pvLower pvUpper arc)
      (negs_to_subs (-lowerChord) (-(lowerT + (-upperT) + (Complex.I * safeLower + (-Complex.I * pvLower) +
        Complex.I * safeUpper + (-Complex.I * pvUpper) + Complex.I * safeMiddle + (-arc))))
        upperChord (-lowerChord) (-(-lowerChord)) (-(-(arc)))
        (-(-(arc))) (-(-(arc))) (-(-(arc))) (-(-(arc)))))

/-- Peeled step 2a-2: Re-associate to group chord terms. -/
theorem Complex.leftEndpointCapCollarBoundary_chord_rearrange_step2
    (lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper
      pvLower pvUpper arc : ℂ) :
    -lowerChord + (lowerT - upperT + (Complex.I * safeLower - Complex.I * pvLower +
      Complex.I * safeUpper - Complex.I * pvUpper + Complex.I * safeMiddle - arc)) +
      upperChord + lowerChord - upperChord =
      (-lowerChord + (lowerT - upperT + (Complex.I * safeLower - Complex.I * pvLower +
        Complex.I * safeUpper - Complex.I * pvUpper + Complex.I * safeMiddle - arc)) +
        upperChord) + lowerChord - upperChord :=
  (add_assoc (-lowerChord + (lowerT - upperT + _) + upperChord) lowerChord (-upperChord)).symm

/-- Lemma: Regroup chords for cancellation. -/
theorem Complex.leftEndpointCapCollarBoundary_regroup_chords_regrouped
    (lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper
      pvLower pvUpper arc : ℂ) :
    lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower +
      upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper +
      lowerChord - upperChord + Complex.I * safeMiddle - arc =
      (-lowerChord + (lowerT - upperT + (Complex.I * safeLower - Complex.I * pvLower +
        Complex.I * safeUpper - Complex.I * pvUpper + Complex.I * safeMiddle - arc)) +
        upperChord) + lowerChord - upperChord :=
  Eq.trans (Complex.leftEndpointCapCollarBoundary_chord_rearrange_step1 lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper pvLower pvUpper arc)
    (Complex.leftEndpointCapCollarBoundary_chord_rearrange_step2 lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper pvLower pvUpper arc)

/-- Sub-step: Reorder safe terms within their group. -/
theorem Complex.regroup_safe_terms_order
    (safeLower safeMiddle safeUpper : ℂ) :
    Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper =
    Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper :=
  rfl

/-- Atomic: Distribute negation. -/
theorem Complex.neg_dist_add
    (a b : ℂ) :
    (-a) + (-b) = -(a + b) :=
  (neg_add_rev a b).symm

/-- Sub-sub-step: Group negated pv terms. -/
theorem Complex.pv_negate_group
    (pvLower pvUpper : ℂ) :
    (-Complex.I * pvLower) + (-Complex.I * pvUpper) = -(Complex.I * pvLower + Complex.I * pvUpper) :=
  Complex.neg_dist_add (Complex.I * pvLower) (Complex.I * pvUpper)

/-- Sub-step: Group pv terms with negation. -/
theorem Complex.regroup_pv_terms_negate
    (pvLower pvUpper arc : ℂ) :
    (-Complex.I * pvLower) + (-Complex.I * pvUpper) + (-arc) =
    -(Complex.I * pvLower + Complex.I * pvUpper) - arc :=
  Eq.trans (congrArg (· + (-arc)) (Complex.pv_negate_group pvLower pvUpper))
    (Eq.symm (sub_eq_add_neg _ _))

/-- Sub-sub-step: Convert subtractions to additions with negation. -/
theorem Complex.left_rest_safe_convert_subs
    (safeLower safeMiddle safeUpper pvLower pvUpper arc : ℂ) :
    Complex.I * safeLower - Complex.I * pvLower +
      Complex.I * safeUpper - Complex.I * pvUpper +
      Complex.I * safeMiddle - arc =
      Complex.I * safeLower + (-(Complex.I * pvLower)) +
      Complex.I * safeUpper + (-(Complex.I * pvUpper)) +
      Complex.I * safeMiddle + (-(arc)) :=
  Eq.trans (congrArg (Complex.I * safeLower + ·) (sub_eq_add_neg (Complex.I * pvLower)))
    (Eq.trans (congrArg (Complex.I * safeLower + (-(Complex.I * pvLower)) + ·) (sub_eq_add_neg (Complex.I * pvUpper)))
      (congrArg (Complex.I * safeLower + (-(Complex.I * pvLower)) + Complex.I * safeUpper + (-(Complex.I * pvUpper)) + Complex.I * safeMiddle + ·) (sub_eq_add_neg arc)))

/-- Atomic: Group three safe terms. -/
theorem Complex.three_safe_group
    (safeLower safeMiddle safeUpper : ℂ) :
    Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper =
    Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper :=
  rfl

/-- Atomic: Group two pv negations. -/
theorem Complex.two_pv_negate_group
    (pvLower pvUpper : ℂ) :
    (-(Complex.I * pvLower)) + (-(Complex.I * pvUpper)) =
    -(Complex.I * pvLower + Complex.I * pvUpper) :=
  Complex.neg_dist_add (Complex.I * pvLower) (Complex.I * pvUpper)

/-- Atomic: abc -> acb swap. -/
theorem Complex.add_three_swap_last_two
    (a b c : ℂ) :
    a + b + c = a + c + b :=
  Eq.trans (add_assoc a b c)
    (Eq.trans (congrArg (a + ·) (add_comm b c))
      ((add_assoc a c b).symm))

/-- Atomic: Swap second and third terms. -/
theorem Complex.swap_bc
    (a b c rest : ℂ) :
    a + b + c + rest = a + c + b + rest :=
  Eq.trans (Eq.symm (add_assoc (a + b) c rest))
    (Eq.trans (congrArg (· + rest) (Complex.add_three_swap_last_two a b c))
      (add_assoc (a + c) b rest))

/-- Atomic: General 6-term rearrangement lemma. -/
theorem Complex.rearrange_six_terms
    (a b c d e f : ℂ) :
    a + b + c + d + e + f = (a + c + e) + (b + d) + f :=
  Eq.trans (Eq.trans (Eq.trans (Complex.swap_bc a b c (d + e + f))
    (Eq.symm (add_assoc a c (b + d + e + f))))
    (congrArg (a + ·) (Eq.symm (add_assoc c (b + d + e + f)))))
    (Eq.trans (congrArg (a + ·) (congrArg (c + ·) (add_assoc b d (e + f))))
      (congrArg (a + ·) (Eq.symm (add_assoc c ((b + d) + (e + f))))))

/-- Sub-sub-step: Group safe terms after converting. -/
theorem Complex.left_safe_group_after_convert
    (safeLower safeMiddle safeUpper pvLower pvUpper arc : ℂ) :
    Complex.I * safeLower + (-(Complex.I * pvLower)) +
      Complex.I * safeUpper + (-(Complex.I * pvUpper)) +
      Complex.I * safeMiddle + (-(arc)) =
      (Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper) -
        (Complex.I * pvLower + Complex.I * pvUpper) - arc :=
  Eq.trans (Complex.rearrange_six_terms
    (Complex.I * safeLower) (-(Complex.I * pvLower))
    (Complex.I * safeUpper) (-(Complex.I * pvUpper))
    (Complex.I * safeMiddle) (-(arc)))
    (Eq.trans (congrArg (· + -(arc)) (Eq.symm (sub_eq_add_neg _ _) ▸ rfl))
      (Eq.symm (sub_eq_add_neg _ _)))

/-- Sub-step: Safe terms rearrangement. -/
theorem Complex.left_rest_safe_rearrange
    (safeLower safeMiddle safeUpper pvLower pvUpper arc : ℂ) :
    Complex.I * safeLower - Complex.I * pvLower +
      Complex.I * safeUpper - Complex.I * pvUpper +
      Complex.I * safeMiddle - arc =
      (Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper) -
        (Complex.I * pvLower + Complex.I * pvUpper) - arc :=
  Eq.trans (Complex.left_rest_safe_convert_subs safeLower safeMiddle safeUpper pvLower pvUpper arc)
    (Complex.left_safe_group_after_convert safeLower safeMiddle safeUpper pvLower pvUpper arc)

/-- Lemma: Simplify rest terms into final form. -/
theorem Complex.leftEndpointCapCollarBoundary_regroup_rest_terms
    (lowerT upperT safeLower safeMiddle safeUpper pvLower pvUpper arc : ℂ) :
    lowerT - upperT + (Complex.I * safeLower - Complex.I * pvLower +
      Complex.I * safeUpper - Complex.I * pvUpper + Complex.I * safeMiddle - arc) =
      lowerT - upperT +
          (Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper) -
        (Complex.I * pvLower + Complex.I * pvUpper) - arc :=
  congrArg (lowerT - upperT + ·) (Complex.left_rest_safe_rearrange safeLower safeMiddle safeUpper pvLower pvUpper arc)

/-- Helper: Convert multiple subtractions to negation form. -/
theorem subs_to_negs
    (a b c d e f g h i j k l : ℂ) :
    a - b + c - d + e - f + g - h + i - j + k - l =
    a + (-b) + c + (-d) + e + (-f) + g + (-h) + i + (-j) + k + (-l) :=
  Eq.trans (congrArg (a + ·) (sub_eq_add_neg b (c - d + e - f + g - h + i - j + k - l)))
    (Eq.trans (congrArg (a + (-b) + c + ·) (sub_eq_add_neg d (e - f + g - h + i - j + k - l)))
      (Eq.trans (congrArg (a + (-b) + c + (-d) + e + ·) (sub_eq_add_neg f (g - h + i - j + k - l)))
        (Eq.trans (congrArg (a + (-b) + c + (-d) + e + (-f) + g + ·) (sub_eq_add_neg h (i - j + k - l)))
          (Eq.trans (congrArg (a + (-b) + c + (-d) + e + (-f) + g + (-h) + i + ·) (sub_eq_add_neg j (k - l)))
            (congrArg (a + (-b) + c + (-d) + e + (-f) + g + (-h) + i + (-j) + k + ·) (sub_eq_add_neg l))))))

/-- Helper: Convert negation form back to subtractions. -/
theorem negs_to_subs
    (a b c d e f g h i j k l : ℂ) :
    a + (-b) + c + (-d) + e + (-f) + g + (-h) + i + (-j) + k + (-l) =
    a - b + c - d + e - f + g - h + i - j + k - l :=
  (subs_to_negs a b c d e f g h i j k l).symm

/-- Atomic step 2: Rearrange flattened terms to grouped form. -/
theorem Complex.leftEndpointCapCollarBoundary_regroup
    (lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper
      pvLower pvUpper arc : ℂ) :
    lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower +
      upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper +
      lowerChord - upperChord + Complex.I * safeMiddle - arc =
      lowerT - upperT +
          (Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper) -
        (Complex.I * pvLower + Complex.I * pvUpper) - arc :=
  let restAfterChords := Complex.I * safeLower - Complex.I * pvLower +
      Complex.I * safeUpper - Complex.I * pvUpper + Complex.I * safeMiddle - arc
  let h_regrouped := Complex.leftEndpointCapCollarBoundary_regroup_chords_regrouped lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper pvLower pvUpper arc
  let h_chords := Complex.boundaryChordsCancelInSum lowerChord upperChord (lowerT - upperT + restAfterChords)
  let h_rest := Complex.leftEndpointCapCollarBoundary_regroup_rest_terms lowerT upperT safeLower safeMiddle safeUpper pvLower pvUpper arc
  Eq.trans h_regrouped (Eq.trans h_chords h_rest)

/-- Helper: rearrange three-part plus three-part left boundary to normalized form. -/
theorem Complex.leftEndpointCapCollarBoundary_rearrange
    (lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper
      pvLower pvUpper arc : ℂ) :
    (lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower) +
        (upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper) +
          (lowerChord - upperChord + Complex.I * safeMiddle - arc) =
      lowerT - upperT +
          (Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper) -
        (Complex.I * pvLower + Complex.I * pvUpper) - arc :=
  Eq.trans (Complex.leftEndpointCapCollarBoundary_flatten lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper pvLower pvUpper arc)
    (Complex.leftEndpointCapCollarBoundary_regroup lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper pvLower pvUpper arc)

/-- Collect the three left endpoint cap/collar boundary pieces after the chord
terms cancel. -/
theorem Complex.leftEndpointCapCollarBoundary_collect
    (lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper
      pvLower pvUpper arc : ℂ) :
    (lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower) +
        (upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper) +
          (lowerChord - upperChord + Complex.I * safeMiddle - arc) =
      lowerT - upperT +
          Complex.I * (safeLower + safeMiddle + safeUpper) -
        Complex.I * (pvLower + pvUpper) - arc :=
  let h_rearrange := Complex.leftEndpointCapCollarBoundary_rearrange
    lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper pvLower pvUpper arc
  let h_safe := Complex.left_mul_add_three_collect Complex.I safeLower safeMiddle safeUpper
  let h_pv := Complex.left_mul_add_two_collect Complex.I pvLower pvUpper
  Eq.trans h_rearrange
    (congrArg₂
      (fun safe pv : ℂ => lowerT - upperT + safe - pv - arc)
      h_safe h_pv)

/-- Right boundary step 1: Flatten associativity. -/
theorem Complex.rightEndpointCapCollarBoundary_flatten
    (lowerT upperT lowerChord upperChord pvLower pvUpper safeLower safeMiddle
      safeUpper arc : ℂ) :
    (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
        (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
          (lowerChord - upperChord - Complex.I * safeMiddle - arc) =
      lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower +
        upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper +
        lowerChord - upperChord - Complex.I * safeMiddle - arc :=
  let a := lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower
  let b := upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper
  let c := lowerChord - upperChord - Complex.I * safeMiddle - arc
  Eq.trans (add_assoc a b c) (congrArg (a + ·) (add_assoc b c))

/-- Sub-sub-step: Convert right rest terms to addition form. -/
theorem Complex.right_rest_convert_subs
    (pvLower pvUpper safeLower safeMiddle safeUpper arc : ℂ) :
    Complex.I * pvLower - Complex.I * safeLower +
      Complex.I * pvUpper - Complex.I * safeUpper -
      Complex.I * safeMiddle - arc =
      Complex.I * pvLower + (-(Complex.I * safeLower)) +
      Complex.I * pvUpper + (-(Complex.I * safeUpper)) +
      (-(Complex.I * safeMiddle)) + (-(arc)) :=
  Eq.trans (congrArg (Complex.I * pvLower + ·) (sub_eq_add_neg (Complex.I * safeLower)))
    (Eq.trans (congrArg (Complex.I * pvLower + (-(Complex.I * safeLower)) + ·) (sub_eq_add_neg (Complex.I * safeUpper)))
      (Eq.trans (congrArg (Complex.I * pvLower + (-(Complex.I * safeLower)) + Complex.I * pvUpper + (-(Complex.I * safeUpper)) + ·) (sub_eq_add_neg (Complex.I * safeMiddle)))
        (congrArg (Complex.I * pvLower + (-(Complex.I * safeLower)) + Complex.I * pvUpper + (-(Complex.I * safeUpper)) + (-(Complex.I * safeMiddle)) + ·) (sub_eq_add_neg arc))))

/-- Sub-step: Right rest terms rearrangement. -/
theorem Complex.right_rest_pv_safe_rearrange
    (pvLower pvUpper safeLower safeMiddle safeUpper arc : ℂ) :
    Complex.I * pvLower - Complex.I * safeLower +
      Complex.I * pvUpper - Complex.I * safeUpper -
      Complex.I * safeMiddle - arc =
      (Complex.I * pvLower + Complex.I * pvUpper) -
        (Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper) -
        arc :=
  Eq.trans (Complex.right_rest_convert_subs pvLower pvUpper safeLower safeMiddle safeUpper arc)
    (Eq.trans (Complex.rearrange_six_terms
      (Complex.I * pvLower) (-(Complex.I * safeLower))
      (Complex.I * pvUpper) (-(Complex.I * safeUpper))
      (-(Complex.I * safeMiddle)) (-(arc)))
      (Eq.trans (congrArg (· + -(arc)) (Eq.symm (sub_eq_add_neg _ _) ▸ rfl))
        (Eq.symm (sub_eq_add_neg _ _))))

/-- Sub-sub-step: Group pv/safe terms after converting. -/
theorem Complex.right_pv_safe_group_after_convert
    (pvLower pvUpper safeLower safeMiddle safeUpper arc : ℂ) :
    Complex.I * pvLower + (-(Complex.I * safeLower)) +
      Complex.I * pvUpper + (-(Complex.I * safeUpper)) +
      (-(Complex.I * safeMiddle)) + (-(arc)) =
      (Complex.I * pvLower + Complex.I * pvUpper) -
        (Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper) -
        arc :=
  Eq.trans (Complex.rearrange_six_terms
    (Complex.I * pvLower) (-(Complex.I * safeLower))
    (Complex.I * pvUpper) (-(Complex.I * safeUpper))
    (-(Complex.I * safeMiddle)) (-(arc)))
    (Eq.trans (congrArg (· + -(arc)) (Eq.symm (sub_eq_add_neg _ _) ▸ rfl))
      (Eq.symm (sub_eq_add_neg _ _)))

/-- Right boundary step 2: Regroup to normalized form. -/
theorem Complex.rightEndpointCapCollarBoundary_regroup
    (lowerT upperT lowerChord upperChord pvLower pvUpper safeLower safeMiddle
      safeUpper arc : ℂ) :
    lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower +
      upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper +
      lowerChord - upperChord - Complex.I * safeMiddle - arc =
      lowerT - upperT +
          (Complex.I * pvLower + Complex.I * pvUpper) -
        (Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper) -
        arc :=
  Eq.trans (Complex.right_rest_pv_safe_rearrange pvLower pvUpper safeLower safeMiddle safeUpper arc)
    (Eq.trans (Eq.symm (sub_eq_add_neg (lowerT - upperT) _))
      (congrArg (fun x => (lowerT - upperT) + x) (Eq.symm (sub_eq_add_neg _ arc))))

/-- Helper: rearrange three-part plus three-part right boundary to normalized form. -/
theorem Complex.rightEndpointCapCollarBoundary_rearrange
    (lowerT upperT lowerChord upperChord pvLower pvUpper safeLower safeMiddle
      safeUpper arc : ℂ) :
    (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
        (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
          (lowerChord - upperChord - Complex.I * safeMiddle - arc) =
      lowerT - upperT +
          (Complex.I * pvLower + Complex.I * pvUpper) -
        (Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper) -
        arc :=
  Eq.trans (Complex.rightEndpointCapCollarBoundary_flatten lowerT upperT lowerChord upperChord pvLower pvUpper safeLower safeMiddle safeUpper arc)
    (Complex.rightEndpointCapCollarBoundary_regroup lowerT upperT lowerChord upperChord pvLower pvUpper safeLower safeMiddle safeUpper arc)

/-- Collect the three right endpoint cap/collar boundary pieces after the chord
terms cancel. -/
theorem Complex.rightEndpointCapCollarBoundary_collect
    (lowerT upperT lowerChord upperChord pvLower pvUpper safeLower safeMiddle
      safeUpper arc : ℂ) :
    (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
        (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
          (lowerChord - upperChord - Complex.I * safeMiddle - arc) =
      lowerT - upperT + Complex.I * (pvLower + pvUpper) -
        Complex.I * (safeLower + safeMiddle + safeUpper) - arc :=
  let h_rearrange := Complex.rightEndpointCapCollarBoundary_rearrange
    lowerT upperT lowerChord upperChord pvLower pvUpper safeLower safeMiddle safeUpper arc
  let h_pv := Complex.left_mul_add_two_collect Complex.I pvLower pvUpper
  let h_safe := Complex.left_mul_add_three_collect Complex.I safeLower safeMiddle safeUpper
  Eq.trans h_rearrange
    (congrArg₂
      (fun pv safe : ℂ => lowerT - upperT + pv - safe - arc)
      h_pv h_safe)

/-- The norm of a purely vertical complex displacement is the absolute value
of its real height. -/
theorem Complex.norm_I_mul_real (y : ℝ) :
    ‖Complex.I * (y : ℂ)‖ = |y| :=
  Eq.trans (norm_mul Complex.I (y : ℂ))
    (Eq.trans
      (congrArg (fun r : ℝ => r * ‖(y : ℂ)‖) Complex.norm_I)
      (Eq.trans (one_mul ‖(y : ℂ)‖) (RCLike.norm_ofReal y)))

/-- Cancelling a real center from a vertical translate leaves only the
vertical displacement. -/
theorem Complex.norm_centered_vertical_translate_sub_center
    (M : ℂ)
    (y : ℝ) :
    ‖(M + Complex.I * (y : ℂ)) - M‖ = |y| :=
  let hcancel : (M + Complex.I * (y : ℂ)) - M = Complex.I * (y : ℂ) :=
    add_sub_cancel_left M (Complex.I * (y : ℂ))
  Eq.trans (congrArg norm hcancel) (Complex.norm_I_mul_real y)

/-- A positive natural number is at least one after coercion to `ℝ`. -/
theorem Real.one_le_natCast_of_pos
    {m : ℕ}
    (hm : 0 < m) :
    (1 : ℝ) ≤ (m : ℝ) :=
  by exact_mod_cast Nat.succ_le_iff.mpr hm

/-- The successor of a natural number is at least one after coercion to `ℝ`. -/
theorem Real.one_le_natCast_succ
    (N : ℕ) :
    (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) :=
  by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)

/-- Natural-number order transports to real coercions. -/
theorem Real.natCast_le_natCast
    {m N : ℕ}
    (h : m ≤ N) :
    (m : ℝ) ≤ (N : ℝ) :=
  (Nat.cast_le : ((m : ℝ) ≤ (N : ℝ) ↔ m ≤ N)).mpr h

/-- Successor coercion to `ℝ`. -/
theorem Real.natCast_succ_eq
    (N : ℕ) :
    ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 :=
  Nat.cast_succ N

/-- The Abel-Plana quarter gap is smaller than a half gap. -/
theorem Real.lt_one_div_two_of_lt_one_div_four
    {ρ : ℝ}
    (hρ : ρ < (1 : ℝ) / 4) :
    ρ < (1 : ℝ) / 2 :=
  lt_trans hρ Real.finiteAbelPlana_one_div_four_lt_one_div_two

/-- Subtracting a nonnegative real number moves weakly left. -/
theorem Real.sub_nonneg_le_self
    (x ρ : ℝ)
    (hρ : 0 ≤ ρ) :
    x - ρ ≤ x :=
  sub_le_self x hρ

/-- Negation reverses a real inequality, named for endpoint-height interval
normalization. -/
theorem Real.endpoint_neg_le_neg_of_le
    {a b : ℝ}
    (h : a ≤ b) :
    -b ≤ -a :=
  neg_le_neg h

/-- If `0 < ρ` and `0 < T`, then the lower indentation height is inside the
ambient upper height. -/
theorem Real.endpoint_neg_radius_le_height
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ) :
    -ρ ≤ T :=
  (neg_nonpos.mpr hρ.le).trans hT.le

/-- If `0 < T` and `0 < ρ`, then the lower ambient height is below the upper
indentation height. -/
theorem Real.endpoint_neg_height_le_radius
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ) :
    -T ≤ ρ :=
  (neg_nonpos.mpr hT.le).trans hρ.le

/-- If `0 < ρ < T`, then the lower ambient height is below the lower
indentation height. -/
theorem Real.endpoint_neg_height_le_neg_radius
    {T ρ : ℝ}
    (hρT : ρ < T) :
    -T ≤ -ρ :=
  Real.endpoint_neg_le_neg_of_le hρT.le

/-- The deleted-geometry half-height condition implies the indentation radius
is smaller than the positive ambient height. -/
theorem Real.endpoint_radius_lt_height_of_lt_abs_height_half
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ_abs : ρ < |T| / 2) :
    ρ < T :=
  let hT_abs : |T| = T := abs_of_pos hT
  let hρ_half : ρ < T / 2 := hT_abs ▸ hρ_abs
  hρ_half.trans (half_lt_self hT)

/-- A radius below a positive height is below the absolute height. -/
theorem Real.endpoint_radius_lt_abs_height
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρT : ρ < T) :
    ρ < |T| :=
  lt_of_lt_of_eq hρT (abs_of_pos hT).symm

/-- The lower endpoint indentation interval lies inside the full vertical
height interval. -/
theorem Real.endpoint_lower_interval_subset_height
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ∀ y ∈ [[(-T), (-ρ)]], y ∈ [[-T, T]] :=
  fun y hy =>
    ⟨hy.1, hy.2.trans (Real.endpoint_neg_radius_le_height hT hρ)⟩

/-- The middle endpoint indentation interval lies inside the full vertical
height interval. -/
theorem Real.endpoint_middle_interval_subset_height
    {T ρ : ℝ}
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ∀ y ∈ [[(-ρ), ρ]], y ∈ [[-T, T]] :=
  fun y hy =>
    ⟨(Real.endpoint_neg_height_le_neg_radius hρT).trans hy.1, hy.2.trans hρT.le⟩

/-- The upper endpoint indentation interval lies inside the full vertical
height interval. -/
theorem Real.endpoint_upper_interval_subset_height
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ∀ y ∈ [[ρ, T]], y ∈ [[-T, T]] :=
  fun y hy =>
    ⟨(Real.endpoint_neg_height_le_radius hT hρ).trans hy.1, hy.2⟩

/-- A radius smaller than `1/2` has doubled radius at most `1`. -/
theorem Real.endpoint_two_radius_le_one_of_lt_half
    {ρ : ℝ}
    (hρ : ρ < (1 : ℝ) / 2) :
    ρ + ρ ≤ (1 : ℝ) :=
  let hsum : ρ + ρ ≤ (1 : ℝ) / 2 + (1 : ℝ) / 2 :=
    add_le_add hρ.le hρ.le
  hsum.trans_eq (add_halves (1 : ℝ))

/-- A radius smaller than `1/2` satisfies the endpoint disk-separation
inequality `ρ - 1 ≤ -ρ`. -/
theorem Real.endpoint_radius_sub_one_le_neg_radius_of_lt_half
    {ρ : ℝ}
    (hρ : ρ < (1 : ℝ) / 2) :
    ρ - 1 ≤ -ρ :=
  let hdouble : ρ + ρ ≤ (1 : ℝ) :=
    Real.endpoint_two_radius_le_one_of_lt_half hρ
  let hle_sub : ρ ≤ 1 - ρ :=
    le_sub_iff_add_le.mpr hdouble
  let hle_add : ρ ≤ -ρ + 1 :=
    Eq.trans hle_sub
      (Eq.trans (sub_eq_add_neg 1 ρ) (add_comm 1 (-ρ)))
  sub_le_iff_le_add.mpr hle_add

/-- Left endpoint collar separation from a nonzero integer center. -/
theorem Real.endpoint_left_re_sub_integer_le_neg_radius
    {x ρ m : ℝ}
    (hx : x ≤ ρ)
    (hm : 1 ≤ m)
    (hρ : ρ < (1 : ℝ) / 2) :
    x - m ≤ -ρ :=
  let hxm : x - m ≤ ρ - 1 := sub_le_sub hx hm
  hxm.trans (Real.endpoint_radius_sub_one_le_neg_radius_of_lt_half hρ)

/-- Rebracketing `M + (1 - ρ)` as `(M + 1) - ρ`. -/
theorem Real.endpoint_add_one_sub_radius_eq
    (M ρ : ℝ) :
    M + (1 - ρ) = (M + 1) - ρ :=
  Eq.trans
    (congrArg (fun x : ℝ => M + x) (sub_eq_add_neg 1 ρ))
    (Eq.trans (add_assoc M 1 (-ρ)) ((sub_eq_add_neg (M + 1) ρ).symm))

/-- Right endpoint collar separation from the previous integer center. -/
theorem Real.endpoint_radius_le_successor_minus_radius_sub_nat
    (N : ℕ)
    {ρ : ℝ}
    (hρ : ρ < (1 : ℝ) / 2) :
    ρ ≤ (((N + 1 : ℕ) : ℝ) - ρ) - (N : ℝ) :=
  let hdouble : ρ + ρ ≤ (1 : ℝ) :=
    Real.endpoint_two_radius_le_one_of_lt_half hρ
  let htarget : ρ ≤ 1 - ρ :=
    le_sub_iff_add_le.mpr hdouble
  let hbase : ρ ≤ (((N : ℝ) + 1) - ρ) - (N : ℝ) :=
    Eq.trans htarget
      (Eq.trans
        ((add_sub_cancel_left (N : ℝ) (1 - ρ)).symm)
        (congrArg (fun x : ℝ => x - (N : ℝ))
          (Real.endpoint_add_one_sub_radius_eq (N : ℝ) ρ)))
  hbase.trans_eq
    (congrArg (fun x : ℝ => (x - ρ) - (N : ℝ))
      (Real.natCast_succ_eq N).symm)

/-- Endpoint-local transport from ordered closed-interval bounds to `uIcc`
membership. -/
theorem Real.endpoint_mem_uIcc_of_bounds
    {a b x : ℝ}
    (horder : a ≤ b)
    (h : a ≤ x ∧ x ≤ b) :
    x ∈ Set.uIcc a b :=
  Set.mem_uIcc.mpr (Or.inl h)

/-- Endpoint-local transport from `uIcc` membership to ordered closed-interval
bounds. -/
theorem Real.endpoint_bounds_of_mem_uIcc
    {a b x : ℝ}
    (horder : a ≤ b)
    (h : x ∈ Set.uIcc a b) :
    a ≤ x ∧ x ≤ b :=
  Set.mem_Icc.mp ((Set.uIcc_of_le horder) ▸ h)

/-- Endpoint-local equality transport for `uIcc` membership. -/
theorem Real.endpoint_mem_uIcc_congr
    {a b x y : ℝ}
    (hxy : x = y)
    (hy : y ∈ Set.uIcc a b) :
    x ∈ Set.uIcc a b :=
  hxy.symm ▸ hy

/-- Endpoint-local equality transport for `uIcc` membership, with equality in
the reverse orientation. -/
theorem Real.endpoint_mem_uIcc_congr_symm
    {a b x y : ℝ}
    (hxy : x = y)
    (hx : x ∈ Set.uIcc a b) :
    y ∈ Set.uIcc a b :=
  hxy ▸ hx

/-- Ball membership as the norm inequality for endpoint collar estimates. -/
theorem Complex.endpoint_norm_lt_of_mem_ball
    (z c : ℂ)
    {ρ : ℝ}
    (h : z ∈ Metric.ball c ρ) :
    ‖z - c‖ < ρ :=
  Eq.mp
    (congrArg (fun r : ℝ => r < ρ) (dist_eq_norm z c))
    (Metric.mem_ball.mp h)

/-- The real part of subtracting a natural-number point on the real axis. -/
theorem Complex.endpoint_sub_natCast_re
    (z : ℂ)
    (m : ℕ) :
    (z - (m : ℂ)).re = z.re - (m : ℝ) :=
  Eq.trans (Complex.sub_re z (m : ℂ)) rfl

/-- The imaginary part of subtracting a natural-number point on the real axis. -/
theorem Complex.endpoint_sub_natCast_im
    (z : ℂ)
    (m : ℕ) :
    (z - (m : ℂ)).im = z.im :=
  Eq.trans (Complex.sub_im z (m : ℂ)) (Eq.trans rfl (sub_zero z.im))

/-- The norm dominates the absolute value of the real coordinate. -/
theorem Complex.endpoint_abs_re_le_norm
    (z : ℂ) :
    |z.re| ≤ ‖z‖ :=
  Complex.abs_re_le_abs z

/-- The norm dominates the absolute value of the imaginary coordinate. -/
theorem Complex.endpoint_abs_im_le_norm
    (z : ℂ) :
    |z.im| ≤ ‖z‖ :=
  Complex.abs_im_le_abs z

/-- A point whose imaginary coordinate has absolute value at least `ρ` cannot
lie in the centered endpoint disk of radius `ρ`. -/
theorem Complex.endpoint_not_mem_center_ball_of_radius_le_abs_im
    {z : ℂ}
    {ρ : ℝ}
    (hρ : ρ ≤ |z.im|) :
    z ∉ Metric.ball (0 : ℂ) ρ :=
  fun hball =>
    let hdist : ‖z‖ < ρ :=
      Complex.endpoint_norm_lt_of_mem_ball z (0 : ℂ) hball
    let him_norm : |z.im| ≤ ‖z‖ :=
      Complex.endpoint_abs_im_le_norm z
    not_lt_of_ge (hρ.trans him_norm) hdist

/-- A point whose centered real coordinate has absolute value at least `ρ`
cannot lie in the endpoint disk of radius `ρ`. -/
theorem Complex.endpoint_not_mem_ball_of_radius_le_abs_re_sub_center
    {z c : ℂ}
    {ρ : ℝ}
    (hρ : ρ ≤ |(z - c).re|) :
    z ∉ Metric.ball c ρ :=
  fun hball =>
    let hdist : ‖z - c‖ < ρ :=
      Complex.endpoint_norm_lt_of_mem_ball z c hball
    let hre_norm : |(z - c).re| ≤ ‖z - c‖ :=
      Complex.endpoint_abs_re_le_norm (z - c)
    not_lt_of_ge (hρ.trans hre_norm) hdist

end

end LFunctions
end Boundary
