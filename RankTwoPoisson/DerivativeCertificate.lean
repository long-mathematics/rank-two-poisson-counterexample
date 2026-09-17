import RankTwoPoisson.CoreGeometry

/-!
# Appendix A derivative certificates

All twelve first partials, both auxiliary univariate derivatives, and the
three expanded wedge coefficients match the displayed appendix formulas.
-/

set_option maxHeartbeats 0
namespace RankTwoPoisson
namespace Core
namespace DerivativeCertificate
open MvPolynomial
noncomputable section

def P1 : Polynomial ℚ := 18*Polynomial.X^2 + 78*Polynomial.X + 125
def P2 : Polynomial ℚ := Polynomial.X^3 + 5*Polynomial.X^2 + 10*Polynomial.X - 5

theorem P1_derivative : P1.derivative = 36*Polynomial.X + 78 := by
  simp [P1, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]; ring

theorem P2_derivative : P2.derivative = 3*Polynomial.X^2 + 10*Polynomial.X + 10 := by
  simp [P2, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]; ring

def p1 (v : CoreP) := 18*v^2 + 78*v + 125
def p2 (v : CoreP) := v^3 + 5*v^2 + 10*v - 5
def p1Prime (v : CoreP) := 36*v + 78
def p2Prime (v : CoreP) := 3*v^2 + 10*v + 10

theorem p1_eval (v : CoreP) : Polynomial.aeval v P1 = p1 v := by simp [P1,p1,map_ofNat]
theorem p2_eval (v : CoreP) : Polynomial.aeval v P2 = p2 v := by simp [P2,p2,map_ofNat]
theorem p1Prime_eval (v : CoreP) : Polynomial.aeval v P1.derivative = p1Prime v := by
  rw [P1_derivative]; simp [p1Prime,map_ofNat]
theorem p2Prime_eval (v : CoreP) : Polynomial.aeval v P2.derivative = p2Prime v := by
  rw [P2_derivative]; simp [p2Prime,map_ofNat]

/-- All three first partial derivatives of the core R. -/
theorem r_derivatives (i : CoreVar) : cpartial i r =
    ![2-6*U-3*Xc^2*Wc, -3*Xc^2, -Xc^3] i := by
  fin_cases i <;> apply MvPolynomial.funext <;> intro v <;>
    simp [cpartial, r, U, crat, Xc, Yc, Wc]
  ring

/-- All three first partial derivatives of the core S. -/
theorem s_derivatives (i : CoreVar) : cpartial i s =
    ![3*Wc*(1+U)*(1+3*U) + 6*Yc^2*(2+3*U),
      1+6*Xc^2*Wc*(1+U)+24*U+27*U^2, 3*Xc*(1+U)^2] i := by
  fin_cases i <;> apply MvPolynomial.funext <;> intro v <;>
    simp [cpartial, s, U, crat, Xc, Yc, Wc] <;> ring

/-- All three first partial derivatives of the core T. -/
theorem t_derivatives (i : CoreVar) : cpartial i t =
    ![crat (-1/2)*(3*Wc*Yc*(1+U)^2 + Yc^3*(7+6*U)),
      crat (-1/2)*(3*Wc*Xc*(1+U)^2+2*Yc*(1+U)*(4+3*U)+Xc*Yc^2*(7+6*U)),
      crat (-1/2)*(1+U)^3] i := by
  fin_cases i <;> apply MvPolynomial.funext <;> intro v <;>
    simp [cpartial, t, U, crat, Xc, Yc, Wc] <;> ring

/-- All three first partial derivatives of the core H, in the appendix notation. -/
theorem h_derivatives (i : CoreVar) : cpartial i h =
    ![crat (1/20)*Yc^5*p1Prime U + crat (3/10)*Wc*Yc^3*p2Prime U -
        crat (3/2)*Wc^2*Yc - crat (1/3)*Xc*Wc^3,
      crat (1/20)*(4*Yc^3*p1 U+Xc*Yc^4*p1Prime U) +
        crat (3/10)*Wc*(2*Yc*p2 U+Xc*Yc^2*p2Prime U) - crat (3/2)*Xc*Wc^2,
      crat (3/10)*Yc^2*p2 U - crat (1/3)*Wc*(9*U+2) - crat (1/2)*Xc^2*Wc^2] i := by
  fin_cases i <;> apply MvPolynomial.funext <;> intro v <;>
    simp [cpartial, h, p1, p2, p1Prime, p2Prime, U, crat, Xc, Yc, Wc] <;> ring

/-- The three collected coefficient expressions displayed in Appendix A. -/
theorem expanded_coefficients :
    (wedgeCoeff r h 0 1 + wedgeCoeff t s 0 1 =
      crat (1/2)*(Xc*Wc+3*Yc)*(7*Xc^2*Wc^2+42*Xc*Yc*Wc+3*Wc+63*Yc^2)) ∧
    (wedgeCoeff r h 0 2 + wedgeCoeff t s 0 2 =
      crat (1/6)*(7*Xc^4*Wc^3+63*Xc^3*Yc*Wc^2+6*Xc^2*Wc^2+
        189*Xc^2*Yc^2*Wc+24*Xc*Yc*Wc+Wc+189*Xc*Yc^3+18*Yc^2)) ∧
    (wedgeCoeff r h 1 2 + wedgeCoeff t s 1 2 = crat (1/2)*(Xc^2*Wc+3*Xc*Yc+1)) := by
  rw [coefficient_identity.1, coefficient_identity.2.1, coefficient_identity.2.2]
  refine ⟨?_,?_,?_⟩ <;> apply MvPolynomial.funext <;> intro v <;>
    simp [A1,A2,A3,Q3,crat,Xc,Yc,Wc] <;> ring

end
end DerivativeCertificate
end Core
end RankTwoPoisson
