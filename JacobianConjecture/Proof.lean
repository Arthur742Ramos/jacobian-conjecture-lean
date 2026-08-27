import JacobianConjecture.Definitions
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Machine-checked proof of the explicit counterexample

The determinant calculation is performed on the formal polynomial Jacobian,
and the fibre calculation uses exact field arithmetic.  The final theorem is
the negation of the usual characteristic-zero, dimension-three injectivity
form of the Jacobian conjecture.
-/

noncomputable section

open Matrix Function
open MvPolynomial

namespace JacobianCounterexample

variable (K : Type*) [Field K]

/-- The formal Jacobian determinant of `F` is the constant polynomial `-2`. -/
theorem jacobianDet_F : MvPolynomial.jacobianDet (F K) = C (-2) := by
  simp only [MvPolynomial.jacobianDet, MvPolynomial.jacobianMatrix,
    det_fin_three, Matrix.of_apply, F, cons_val_zero, cons_val_one,
    cons_val_two, head_cons, tail_cons, map_add, map_sub,
    Derivation.map_one_eq_zero, pderiv_mul, pderiv_pow, pderiv_C,
    pderiv_X_self, pderiv_X_of_ne, ne_eq, Fin.reduceEq,
    not_false_eq_true]
  simp only [map_neg, map_ofNat]
  ring

variable {K}

/-- The first point in the published three-point fibre. -/
theorem evalMap_F_p0 :
    MvPolynomial.evalMap (F K) ![0, 0, -(1 / 4)] = ![-(1 / 4), 0, 0] := by
  funext i
  fin_cases i <;> simp [MvPolynomial.evalMap, F]

/-- The second point in the published three-point fibre. -/
theorem evalMap_F_p1 (h2 : (2 : K) ≠ 0) :
    MvPolynomial.evalMap (F K) ![1, -(3 / 2), 13 / 2] = ![-(1 / 4), 0, 0] := by
  have h4 : (4 : K) ≠ 0 :=
    (by norm_num : (2 : K) * 2 = 4) ▸ mul_ne_zero h2 h2
  funext i
  fin_cases i <;> simp [MvPolynomial.evalMap, F] <;> field_simp [h4] <;> ring

/-- The third point in the published three-point fibre. -/
theorem evalMap_F_p2 (h2 : (2 : K) ≠ 0) :
    MvPolynomial.evalMap (F K) ![-1, 3 / 2, 13 / 2] = ![-(1 / 4), 0, 0] := by
  have h4 : (4 : K) ≠ 0 :=
    (by norm_num : (2 : K) * 2 = 4) ▸ mul_ne_zero h2 h2
  funext i
  fin_cases i <;> simp [MvPolynomial.evalMap, F] <;> field_simp [h4] <;> ring

/-- The three displayed rational points lie in one fibre over `ℂ`. -/
theorem explicit_three_point_fibre :
    MvPolynomial.evalMap (F ℂ) ![0, 0, -(1 / 4)] = ![-(1 / 4), 0, 0] ∧
      MvPolynomial.evalMap (F ℂ) ![1, -(3 / 2), 13 / 2] = ![-(1 / 4), 0, 0] ∧
      MvPolynomial.evalMap (F ℂ) ![-1, 3 / 2, 13 / 2] = ![-(1 / 4), 0, 0] := by
  exact ⟨evalMap_F_p0 (K := ℂ),
    ⟨evalMap_F_p1 (K := ℂ) (by norm_num),
      evalMap_F_p2 (K := ℂ) (by norm_num)⟩⟩

/-- The usual dimension-three Jacobian-conjecture statement is false over `ℂ`.

The witness is `F`: its formal Jacobian determinant is a nonzero constant,
while two distinct rational points have the same image. -/
theorem not_jacobian_conjecture_complex :
    ¬ ∀ P : Fin 3 → MvPolynomial (Fin 3) ℂ,
      IsUnit (MvPolynomial.jacobianDet P) →
        Injective (MvPolynomial.evalMap P) := by
  intro h
  have hunit : IsUnit (MvPolynomial.jacobianDet (F ℂ)) := by
    rw [jacobianDet_F]
    exact (isUnit_iff_ne_zero.mpr
      (neg_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0))).map C
  have h12 : (![1, -(3 / 2), 13 / 2] : Fin 3 → ℂ) =
      ![-1, 3 / 2, 13 / 2] :=
    h (F ℂ) hunit
      ((evalMap_F_p1 (K := ℂ) (by norm_num)).trans
        (evalMap_F_p2 (K := ℂ) (by norm_num)).symm)
  have h0 : (1 : ℂ) = -1 := congrFun h12 0
  norm_num at h0

end JacobianCounterexample
