import Mathlib.Data.Complex.Basic

namespace Boundary
namespace LFunctions

noncomputable section

open Complex

namespace ZetaAdmissibleFunction

/-- Additive algebra for a project/standard horizontal orientation defect. -/
theorem explicitFormula_orientationDefect_horizontal_algebra
    (A H : ℂ) :
    (A + H) - (A - H) = H + H := by
  have hsum :
      (A - H) + (H + H) = A + H := by
    calc
      (A - H) + (H + H) = (A + -H) + (H + H) := by
        exact congrArg (fun x : ℂ => x + (H + H)) (sub_eq_add_neg A H)
      _ = A + (-H + (H + H)) := by
        exact add_assoc A (-H) (H + H)
      _ = A + ((-H + H) + H) := by
        exact congrArg (fun x : ℂ => A + x) (add_assoc (-H) H H).symm
      _ = A + (0 + H) := by
        exact congrArg (fun x : ℂ => A + (x + H)) (neg_add_cancel H)
      _ = A + H := by
        exact congrArg (fun x : ℂ => A + x) (zero_add H)
  exact (eq_sub_of_add_eq' hsum).symm

/-- Additive form of the horizontal orientation-defect algebra. -/
theorem explicitFormula_orientationDefect_horizontal_add_algebra
    (A H : ℂ) :
    A + H = (A - H) + (H + H) := by
  have hsub :
      (A + H) - (A - H) = H + H :=
    explicitFormula_orientationDefect_horizontal_algebra A H
  calc
    A + H = (A - H) + ((A + H) - (A - H)) := by
      exact (add_sub_cancel (A - H) (A + H)).symm
    _ = (A - H) + (H + H) := by
      exact congrArg (fun z : ℂ => (A - H) + z) hsub

/-- Additive algebra putting the standard rectangle horizontal convention in
`right-minus-left` plus negative horizontal-remainder form. -/
theorem explicitFormula_standardBoundary_horizontal_algebra
    (R L U B : ℂ) :
    B - U + R - L = R - L - (U - B) := by
  calc
    B - U + R - L = (B + -U) + R - L := by
      exact congrArg (fun x : ℂ => x + R - L) (sub_eq_add_neg B U)
    _ = R + (B + -U) - L := by
      exact congrArg (fun x : ℂ => x - L) (add_comm (B + -U) R)
    _ = R + (B - U) - L := by
      exact congrArg (fun x : ℂ => R + x - L) (sub_eq_add_neg B U).symm
    _ = R + (B - U + -L) := by
      exact Eq.trans
        (sub_eq_add_neg (R + (B - U)) L)
        (add_assoc R (B - U) (-L))
    _ = R + (-L + (B - U)) := by
      exact congrArg (fun x : ℂ => R + x) (add_comm (B - U) (-L))
    _ = R + -L + (B - U) := by
      exact (add_assoc R (-L) (B - U)).symm
    _ = R - L + (B - U) := by
      exact congrArg (fun x : ℂ => x + (B - U)) (sub_eq_add_neg R L).symm
    _ = R - L + -(U - B) := by
      exact congrArg (fun x : ℂ => R - L + x) (neg_sub U B).symm
    _ = R - L - (U - B) := by
      exact (sub_eq_add_neg (R - L) (U - B)).symm

/-- Four-side additive algebra for tangent-oriented rectangle boundaries. -/
theorem explicitFormula_tangent_four_side_split
    (R L T B : ℂ) :
    R - L + T - B = R - L + (T - B) := by
  calc
    R - L + T - B = (R - L + T) + -B := by
      exact sub_eq_add_neg (R - L + T) B
    _ = (R - L) + (T + -B) := by
      exact add_assoc (R - L) T (-B)
    _ = R - L + (T - B) := by
      exact congrArg (fun z : ℂ => R - L + z)
        (sub_eq_add_neg T B).symm

/-- Reorder the standard rectangle convention from horizontal-first to
vertical-first grouping. -/
theorem explicitFormula_standardBoundary_verticalFirst_noExcision
    (A C H : ℂ) :
    H + (A - C) = A - C + H :=
  add_comm H (A - C)

/-- Reorder the standard rectangle convention from horizontal-first to
vertical-first grouping, preserving a following excision subtraction. -/
theorem explicitFormula_standardBoundary_verticalFirst
    (A C H E : ℂ) :
    (H + (A - C)) - E = (A - C + H) - E := by
  exact congrArg (fun z : ℂ => z - E)
    (explicitFormula_standardBoundary_verticalFirst_noExcision A C H)

/-- Additive algebra for regrouping a tangent-oriented rectangle boundary so
the left vertical side is isolated first.

The intended substitution is
`A = right * I`, `C = left * I`, `H = top - bottom`, and `E = excision`. -/
theorem explicitFormula_tangentBoundary_leftFirst_algebra
    (A C H E : ℂ) :
    (-C) + (A + H) - E = (A - C + H) - E := by
  calc
    (-C) + (A + H) - E =
        (A + (-C + H)) - E := by
      exact congrArg (fun z : ℂ => z - E)
        (add_left_comm (-C) A H)
    _ = ((A + -C) + H) - E := by
      exact congrArg (fun z : ℂ => z - E)
        (add_assoc A (-C) H).symm
    _ = (A - C + H) - E := by
      exact congrArg (fun z : ℂ => (z + H) - E)
        (sub_eq_add_neg A C).symm

/-- If a tangent rectangle boundary minus an excision term is zero, then the
same identity can be read with the left vertical side isolated first. -/
theorem explicitFormula_tangentBoundary_leftFirst_eq_zero_of_boundary_sub_excision_eq_zero
    (A C H E : ℂ)
    (hboundary : (A - C + H) - E = 0) :
    (-C) + (A + H) - E = 0 := by
  exact Eq.trans
    (explicitFormula_tangentBoundary_leftFirst_algebra A C H E)
    hboundary

/-- Convert a completed-left tangent boundary identity into the prime-left
boundary-sum orientation after the completed left side has been decomposed as
prime plus inverse-Gamma.

The intended substitution is `C = completedLeft`, `P = primeLeft`,
`G = inverseGammaLeft`, `H = finiteHorizontalRightError`, and
`E = finiteExcisionError`. -/
theorem explicitFormula_primeLeftBoundary_of_completedLeftBoundary
    (C P G H E : ℂ)
    (hC : C = P + G)
    (hboundary : (-(C * Complex.I)) + H + E = 0) :
    P + (G + Complex.I * H) + Complex.I * E = 0 := by
  have hI_sq : Complex.I * Complex.I = -(1 : ℂ) :=
    Complex.I_mul_I
  have hI_completed_neg :
      Complex.I * (-(C * Complex.I)) = C := by
    calc
      Complex.I * (-(C * Complex.I)) =
          -(Complex.I * (C * Complex.I)) := by
        exact mul_neg Complex.I (C * Complex.I)
      _ = -((Complex.I * C) * Complex.I) := by
        exact congrArg Neg.neg (mul_assoc Complex.I C Complex.I).symm
      _ = -((C * Complex.I) * Complex.I) := by
        exact congrArg (fun z : ℂ => -(z * Complex.I))
          (mul_comm Complex.I C)
      _ = -(C * (Complex.I * Complex.I)) := by
        exact congrArg Neg.neg (mul_assoc C Complex.I Complex.I)
      _ = -(C * (-(1 : ℂ))) := by
        exact congrArg (fun z : ℂ => -(C * z)) hI_sq
      _ = -(-(C * (1 : ℂ))) := by
        exact congrArg Neg.neg (mul_neg C (1 : ℂ))
      _ = -(-C) := by
        exact congrArg (fun z : ℂ => -(-z)) (mul_one C)
      _ = C := by
        exact neg_neg C
  have hmul_boundary :
      Complex.I * (((-(C * Complex.I)) + H) + E) = 0 := by
    have hmul :
        Complex.I * (((-(C * Complex.I)) + H) + E) =
          Complex.I * 0 :=
      congrArg (fun z : ℂ => Complex.I * z) hboundary
    exact Eq.trans hmul (mul_zero Complex.I)
  have hmul_expand :
      Complex.I * (((-(C * Complex.I)) + H) + E) =
        C + Complex.I * H + Complex.I * E := by
    calc
      Complex.I * (((-(C * Complex.I)) + H) + E) =
          Complex.I * ((-(C * Complex.I)) + H) + Complex.I * E := by
        exact mul_add Complex.I ((-(C * Complex.I)) + H) E
      _ =
          (Complex.I * (-(C * Complex.I)) + Complex.I * H) +
            Complex.I * E := by
        exact congrArg
          (fun z : ℂ => z + Complex.I * E)
          (mul_add Complex.I (-(C * Complex.I)) H)
      _ = (C + Complex.I * H) + Complex.I * E := by
        exact congrArg (fun z : ℂ => (z + Complex.I * H) + Complex.I * E)
          hI_completed_neg
      _ = C + Complex.I * H + Complex.I * E := by
        exact Eq.refl _
  have hcompleted :
      C + Complex.I * H + Complex.I * E = 0 :=
    Eq.trans hmul_expand.symm hmul_boundary
  have hregroup :
      P + (G + Complex.I * H) + Complex.I * E =
        (P + G) + Complex.I * H + Complex.I * E := by
    exact congrArg (fun z : ℂ => z + Complex.I * E)
      (add_assoc P G (Complex.I * H)).symm
  have hreplace :
      (P + G) + Complex.I * H + Complex.I * E =
        C + Complex.I * H + Complex.I * E := by
    exact congrArg
      (fun z : ℂ => z + Complex.I * H + Complex.I * E)
      hC.symm
  exact Eq.trans hregroup (Eq.trans hreplace hcompleted)

/-- Rotating the finite horizontal/right tangent packet by `I` turns the
right vertical tangent contribution into a negative ordinary right vertical
contribution. -/
theorem explicitFormula_rotate_rightTangent_add_horizontal
    (R H : ℂ) :
    Complex.I * (R * Complex.I + H) = -R + Complex.I * H := by
  have hI_sq : Complex.I * Complex.I = -(1 : ℂ) :=
    Complex.I_mul_I
  calc
    Complex.I * (R * Complex.I + H) =
        Complex.I * (R * Complex.I) + Complex.I * H := by
      exact mul_add Complex.I (R * Complex.I) H
    _ = (Complex.I * R) * Complex.I + Complex.I * H := by
      exact congrArg (fun z : ℂ => z + Complex.I * H)
        (mul_assoc Complex.I R Complex.I).symm
    _ = (R * Complex.I) * Complex.I + Complex.I * H := by
      exact congrArg (fun z : ℂ => z * Complex.I + Complex.I * H)
        (mul_comm Complex.I R)
    _ = R * (Complex.I * Complex.I) + Complex.I * H := by
      exact congrArg (fun z : ℂ => z + Complex.I * H)
        (mul_assoc R Complex.I Complex.I)
    _ = R * (-(1 : ℂ)) + Complex.I * H := by
      exact congrArg (fun z : ℂ => R * z + Complex.I * H) hI_sq
    _ = -(R * (1 : ℂ)) + Complex.I * H := by
      exact congrArg (fun z : ℂ => z + Complex.I * H)
        (mul_neg R (1 : ℂ))
    _ = -R + Complex.I * H := by
      exact congrArg (fun z : ℂ => -z + Complex.I * H) (mul_one R)

/-- Convert the completed-left tangent boundary identity into a full
prime/inverse-Gamma split when the right completed side has also been
decomposed.

The intended substitution is:
`C = completedLeft`, `P = primeLeft`, `G = inverseGammaLeft`,
`R = completedRight`, `Q = primeRight`, `J = inverseGammaRight`,
`H = top - bottom`, and `E = finiteExcisionError`. -/
theorem explicitFormula_primeLeftBoundary_fullRightSplit_of_completedBoundary
    (C P G R Q J H E : ℂ)
    (hC : C = P + G)
    (hR : R = Q + J)
    (hboundary : (-(C * Complex.I)) + (R * Complex.I + H) + E = 0) :
    (P - Q) + ((G - J) + Complex.I * H) + Complex.I * E = 0 := by
  have hleft :
      P + (G + Complex.I * (R * Complex.I + H)) + Complex.I * E = 0 :=
    explicitFormula_primeLeftBoundary_of_completedLeftBoundary
      C P G (R * Complex.I + H) E hC hboundary
  have hrotate :
      Complex.I * (R * Complex.I + H) = -R + Complex.I * H :=
    explicitFormula_rotate_rightTangent_add_horizontal R H
  have hright_expand :
      -R + Complex.I * H = (-Q + -J) + Complex.I * H := by
    calc
      -R + Complex.I * H = -(Q + J) + Complex.I * H := by
        exact congrArg (fun z : ℂ => -z + Complex.I * H) hR
      _ = (-Q + -J) + Complex.I * H := by
        exact congrArg (fun z : ℂ => z + Complex.I * H) (neg_add Q J)
  have htarget_eq_left :
      (P - Q) + ((G - J) + Complex.I * H) + Complex.I * E =
        P + (G + Complex.I * (R * Complex.I + H)) + Complex.I * E := by
    calc
      (P - Q) + ((G - J) + Complex.I * H) + Complex.I * E =
          ((P + -Q) + ((G + -J) + Complex.I * H)) + Complex.I * E := by
        exact congrArg
          (fun z : ℂ => z + ((G - J) + Complex.I * H) + Complex.I * E)
          (sub_eq_add_neg P Q)
      _ =
          ((P + -Q) + ((G + -J) + Complex.I * H)) + Complex.I * E := by
        rfl
      _ =
          (P + (-Q + ((G + -J) + Complex.I * H))) + Complex.I * E := by
        exact congrArg (fun z : ℂ => z + Complex.I * E)
          (add_assoc P (-Q) ((G + -J) + Complex.I * H))
      _ =
          (P + (G + (-Q + -J + Complex.I * H))) + Complex.I * E := by
        exact congrArg (fun z : ℂ => (P + z) + Complex.I * E)
          (by
            calc
              -Q + ((G + -J) + Complex.I * H) =
                  (-Q + (G + -J)) + Complex.I * H := by
                exact (add_assoc (-Q) (G + -J) (Complex.I * H)).symm
              _ = (G + (-Q + -J)) + Complex.I * H := by
                exact congrArg
                  (fun z : ℂ => z + Complex.I * H)
                  (by
                    calc
                      -Q + (G + -J) = (-Q + G) + -J := by
                        exact (add_assoc (-Q) G (-J)).symm
                      _ = (G + -Q) + -J := by
                        exact congrArg (fun z : ℂ => z + -J)
                          (add_comm (-Q) G)
                      _ = G + (-Q + -J) := by
                        exact add_assoc G (-Q) (-J))
              _ = G + ((-Q + -J) + Complex.I * H) := by
                exact add_assoc G (-Q + -J) (Complex.I * H))
      _ =
          (P + (G + (-R + Complex.I * H))) + Complex.I * E := by
        exact congrArg
          (fun z : ℂ => (P + (G + z)) + Complex.I * E)
          hright_expand.symm
      _ =
          (P + (G + Complex.I * (R * Complex.I + H))) + Complex.I * E := by
        exact congrArg
          (fun z : ℂ => (P + (G + z)) + Complex.I * E)
          hrotate.symm
      _ = P + (G + Complex.I * (R * Complex.I + H)) + Complex.I * E := by
        rfl
  exact Eq.trans htarget_eq_left hleft

/-- Additive algebra for subtracting a tangent-oriented residue value from a
left-minus-tangent defect. -/
theorem explicitFormula_tangentDefect_sub_residue_algebra
    (L T A B : ℂ) :
    L - T * Complex.I - (A - B * Complex.I) =
      L - A - (T - B) * Complex.I := by
  have hmul :
      (T - B) * Complex.I = T * Complex.I - B * Complex.I :=
    sub_mul T B Complex.I
  calc
    L - T * Complex.I - (A - B * Complex.I) =
        (L + -(T * Complex.I)) - (A - B * Complex.I) := by
      exact congrArg (fun z : ℂ => z - (A - B * Complex.I))
        (sub_eq_add_neg L (T * Complex.I))
    _ = (L + -(T * Complex.I)) + -(A - B * Complex.I) := by
      exact sub_eq_add_neg (L + -(T * Complex.I)) (A - B * Complex.I)
    _ = (L + -(T * Complex.I)) + (-A + B * Complex.I) := by
      exact congrArg
        (fun z : ℂ => (L + -(T * Complex.I)) + z)
        (Eq.trans
          (neg_sub A (B * Complex.I))
          (Eq.trans
            (sub_eq_add_neg (B * Complex.I) A)
            (add_comm (B * Complex.I) (-A))))
    _ = L + (-(T * Complex.I) + (-A + B * Complex.I)) := by
      exact add_assoc L (-(T * Complex.I)) (-A + B * Complex.I)
    _ = L + (-A + (-(T * Complex.I) + B * Complex.I)) := by
      exact congrArg (fun z : ℂ => L + z)
        (add_left_comm (-(T * Complex.I)) (-A) (B * Complex.I))
    _ = (L + -A) + (-(T * Complex.I) + B * Complex.I) := by
      exact (add_assoc L (-A) (-(T * Complex.I) + B * Complex.I)).symm
    _ = (L - A) + (-(T * Complex.I) + B * Complex.I) := by
      exact congrArg
        (fun z : ℂ => z + (-(T * Complex.I) + B * Complex.I))
        (sub_eq_add_neg L A).symm
    _ = (L - A) + -(T * Complex.I - B * Complex.I) := by
      exact congrArg (fun z : ℂ => (L - A) + z)
        (Eq.trans
          (add_comm (-(T * Complex.I)) (B * Complex.I))
          (Eq.trans
            (sub_eq_add_neg (B * Complex.I) (T * Complex.I)).symm
            (neg_sub (T * Complex.I) (B * Complex.I)).symm))
    _ = (L - A) - (T * Complex.I - B * Complex.I) := by
      exact (sub_eq_add_neg (L - A) (T * Complex.I - B * Complex.I)).symm
    _ = (L - A) - (T - B) * Complex.I := by
      exact congrArg (fun z : ℂ => (L - A) - z) hmul.symm

/-- If the residue values are tangent-compatible, the defect is the difference
of the two component errors. -/
theorem explicitFormula_tangentDefect_eq_componentErrors_of_residue_cancel
    (L T A B : ℂ) (hcancel : A - B * Complex.I = 0) :
    L - T * Complex.I = (L - A) - (T - B) * Complex.I := by
  calc
    L - T * Complex.I =
        L - T * Complex.I - 0 := by
      exact (sub_zero (L - T * Complex.I)).symm
    _ = L - T * Complex.I - (A - B * Complex.I) := by
      exact congrArg (fun z : ℂ => L - T * Complex.I - z) hcancel.symm
    _ = (L - A) - (T - B) * Complex.I := by
      exact explicitFormula_tangentDefect_sub_residue_algebra L T A B

/-- Solve the tangent-oriented one-pole boundary identity for the left residue
error relative to a tangent boundary residue value. -/
theorem explicitFormula_leftResidueError_eq_right_add_tangentError_mul_I_sub_horizontal_mul_I
    (R L C H B : ℂ)
    (hC : C = R * Complex.I - L * Complex.I + H) :
    L - B * Complex.I = R + (C - B) * Complex.I - H * Complex.I := by
  have hI_sq : Complex.I * Complex.I = -(1 : ℂ) :=
    Complex.I_mul_I
  exact (calc
    R + (C - B) * Complex.I - H * Complex.I =
        R + ((R * Complex.I - L * Complex.I + H) - B) * Complex.I -
          H * Complex.I := by
      exact congrArg
        (fun z : ℂ => R + (z - B) * Complex.I - H * Complex.I)
        hC
    _ =
        R +
          ((R * Complex.I - L * Complex.I + H) * Complex.I -
            B * Complex.I) -
          H * Complex.I := by
      exact congrArg
        (fun z : ℂ => R + z - H * Complex.I)
        (sub_mul (R * Complex.I - L * Complex.I + H) B Complex.I)
    _ =
        R +
          (((R * Complex.I - L * Complex.I) + H) * Complex.I -
            B * Complex.I) -
          H * Complex.I := by
      rfl
    _ =
        R +
          (((R * Complex.I - L * Complex.I) * Complex.I + H * Complex.I) -
            B * Complex.I) -
          H * Complex.I := by
      exact congrArg
        (fun z : ℂ => R + (z - B * Complex.I) - H * Complex.I)
        (add_mul (R * Complex.I - L * Complex.I) H Complex.I)
    _ =
        R +
          (((R * Complex.I) * Complex.I - (L * Complex.I) * Complex.I +
              H * Complex.I) -
            B * Complex.I) -
          H * Complex.I := by
      exact congrArg
        (fun z : ℂ => R + ((z + H * Complex.I) - B * Complex.I) -
          H * Complex.I)
        (sub_mul (R * Complex.I) (L * Complex.I) Complex.I)
    _ =
        R +
          ((R * (Complex.I * Complex.I) - L * (Complex.I * Complex.I) +
              H * Complex.I) -
            B * Complex.I) -
          H * Complex.I := by
      exact congrArg
        (fun z : ℂ => R + ((z + H * Complex.I) - B * Complex.I) -
          H * Complex.I)
        (congrArg₂ HSub.hSub
          (mul_assoc R Complex.I Complex.I)
          (mul_assoc L Complex.I Complex.I))
    _ =
        R +
          ((R * (-(1 : ℂ)) - L * (-(1 : ℂ)) + H * Complex.I) -
            B * Complex.I) -
          H * Complex.I := by
      exact congrArg
        (fun z : ℂ =>
          R + ((R * z - L * z + H * Complex.I) - B * Complex.I) -
            H * Complex.I)
        hI_sq
    _ =
        R +
          ((-R - -L + H * Complex.I) - B * Complex.I) -
          H * Complex.I := by
      exact congrArg
        (fun z : ℂ => R + ((z + H * Complex.I) - B * Complex.I) -
          H * Complex.I)
        (congrArg₂ HSub.hSub (mul_neg_one R) (mul_neg_one L))
    _ =
        R +
          ((-R + L + H * Complex.I) - B * Complex.I) -
          H * Complex.I := by
      exact congrArg
        (fun z : ℂ => R + ((z + H * Complex.I) - B * Complex.I) -
          H * Complex.I)
        (sub_neg_eq_add (-R) L)
    _ =
        R +
          (-R + (L + H * Complex.I) - B * Complex.I) -
          H * Complex.I := by
      exact congrArg
        (fun z : ℂ => R + (z - B * Complex.I) - H * Complex.I)
        (add_assoc (-R) L (H * Complex.I))
    _ =
        R +
          (-R + (L + H * Complex.I + -(B * Complex.I))) -
          H * Complex.I := by
      exact congrArg
        (fun z : ℂ => R + z - H * Complex.I)
        (Eq.trans
          (sub_eq_add_neg (-R + (L + H * Complex.I)) (B * Complex.I))
          (add_assoc (-R) (L + H * Complex.I) (-(B * Complex.I))))
    _ =
        R +
          (-R + (L + (H * Complex.I + -(B * Complex.I)))) -
          H * Complex.I := by
      exact congrArg
        (fun z : ℂ => R + (-R + z) - H * Complex.I)
        (add_assoc L (H * Complex.I) (-(B * Complex.I)))
    _ =
        R +
          (-R + (L + (-(B * Complex.I) + H * Complex.I))) -
          H * Complex.I := by
      exact congrArg
        (fun z : ℂ => R + (-R + (L + z)) - H * Complex.I)
        (add_comm (H * Complex.I) (-(B * Complex.I)))
    _ =
        R +
          (-R + (L + -(B * Complex.I) + H * Complex.I)) -
          H * Complex.I := by
      exact congrArg
        (fun z : ℂ => R + (-R + z) - H * Complex.I)
        (add_assoc L (-(B * Complex.I)) (H * Complex.I)).symm
    _ =
        R +
          (-R + ((L - B * Complex.I) + H * Complex.I)) -
          H * Complex.I := by
      exact congrArg
        (fun z : ℂ => R + (-R + (z + H * Complex.I)) - H * Complex.I)
        (sub_eq_add_neg L (B * Complex.I)).symm
    _ =
        (R + -R) + ((L - B * Complex.I) + H * Complex.I) -
          H * Complex.I := by
      exact congrArg
        (fun z : ℂ => z - H * Complex.I)
        (add_assoc R (-R) ((L - B * Complex.I) + H * Complex.I)).symm
    _ =
        0 + ((L - B * Complex.I) + H * Complex.I) - H * Complex.I := by
      exact congrArg
        (fun z : ℂ => z + ((L - B * Complex.I) + H * Complex.I) -
          H * Complex.I)
        (add_neg_cancel R)
    _ =
        ((L - B * Complex.I) + H * Complex.I) - H * Complex.I := by
      exact congrArg
        (fun z : ℂ => z - H * Complex.I)
        (zero_add ((L - B * Complex.I) + H * Complex.I))
    _ = L - B * Complex.I := by
      calc
        ((L - B * Complex.I) + H * Complex.I) - H * Complex.I =
            ((L - B * Complex.I) + H * Complex.I) + -(H * Complex.I) := by
          exact sub_eq_add_neg
            ((L - B * Complex.I) + H * Complex.I)
            (H * Complex.I)
        _ = (L - B * Complex.I) + (H * Complex.I + -(H * Complex.I)) := by
          exact add_assoc (L - B * Complex.I) (H * Complex.I) (-(H * Complex.I))
        _ = (L - B * Complex.I) + 0 := by
          exact congrArg (fun z : ℂ => (L - B * Complex.I) + z)
            (add_neg_cancel (H * Complex.I))
        _ = L - B * Complex.I := by
          exact add_zero (L - B * Complex.I)).symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
