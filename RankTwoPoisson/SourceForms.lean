import RankTwoPoisson.SourceEquivalence
import RankTwoPoisson.CoreGeometry

/-!
# The source-coordinate symplectic form

Formal one-forms and two-forms are represented by their complete coefficient
arrays in the independent coordinate order (X,Y,W,E₀).
-/

set_option maxHeartbeats 0
namespace RankTwoPoisson
namespace SourceCoordinates
namespace Forms
open MvPolynomial
noncomputable section

@[simp] private theorem pderiv_numeral (i : Var) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : P) = 0 := (pderiv i).map_natCast n

/-- Alternating coefficient of a wedge of two exact polynomial one-forms. -/
def wedge (f g : P) (i j : Var) := pderiv i f * pderiv j g - pderiv j f * pderiv i g

theorem dQ (i : Var) : pderiv i Qs =
    pderiv i q + rat (1/3)*p*pderiv i x + rat (1/3)*x*pderiv i p := by
  fin_cases i <;> apply MvPolynomial.funext <;> intro v <;>
    simp [Qs,rat,x,q,p]
  ring

theorem dC (i : Var) : pderiv i Cs =
    rat (3/2)*(Qs*pderiv i x + x*pderiv i Qs) := by
  fin_cases i <;> apply MvPolynomial.funext <;> intro v <;>
    simp [Cs,Qs,rat,x,q,p] <;> ring

theorem dM (i : Var) : pderiv i Ms = pderiv i p + 18*Qs*pderiv i Qs := by
  fin_cases i <;> apply MvPolynomial.funext <;> intro v <;>
    simp [Ms,Qs,rat,x,q,p] <;> ring

theorem dp (i : Var) : pderiv i pInv =
    -6*z*Qs*pderiv i x + (6*Qs*(p+18*Qs^2)-6*z*x)*pderiv i Qs +
      3*Qs^2*pderiv i p + 2*As*pderiv i z := by
  fin_cases i <;> apply MvPolynomial.funext <;> intro v <;>
    simp [pInv,Qs,Ms,As,rat,x,q,p,z] <;> ring

theorem dz (i : Var) : pderiv i zInv =
    (rat (3/2)*Qs*Ms-6*x*z)*pderiv i x +
      (rat (3/2)*x*Ms+18*Qs*Cs)*pderiv i Qs + Cs*pderiv i p -3*x^2*pderiv i z := by
  fin_cases i <;> apply MvPolynomial.funext <;> intro v <;>
    simp [zInv,Qs,Ms,Cs,rat,x,q,p,z] <;> ring

theorem core_R_Q : coreLift Core.r = x*(2-3*x*Qs) := by
  apply MvPolynomial.funext
  intro v
  simp [coreLift,Core.r,Core.crat,Core.Xc,Core.Yc,Core.Wc,Qs,rat,x,q,p]
  ring

theorem dR (i : Var) : pderiv i (coreLift Core.r) = 2*As*pderiv i x -3*x^2*pderiv i Qs := by
  fin_cases i <;> apply MvPolynomial.funext <;> intro v <;>
    simp [coreLift,Core.r,Core.crat,Core.Xc,Core.Yc,Core.Wc,As,Qs,rat,x,q,p] <;> ring

theorem d_p_first (i : Var) : pderiv i (3*Qs^2*Ms) =
    3*Qs^2*pderiv i p + 6*Qs*(p+18*Qs^2)*pderiv i Qs := by
  fin_cases i <;> apply MvPolynomial.funext <;> intro v <;>
    simp [Qs,Ms,rat,x,q,p] <;> ring

theorem d_p_second (i : Var) : pderiv i (2*As*z) =
    2*As*pderiv i z -6*z*Qs*pderiv i x -6*z*x*pderiv i Qs := by
  fin_cases i <;> apply MvPolynomial.funext <;> intro v <;>
    simp [As,Qs,rat,x,q,p,z] <;> ring

theorem omega_Q_coefficient :
    6*Qs*(p+18*Qs^2)-6*z*x-(rat (3/2)*Qs*Ms-6*x*z) =
      rat (9/2)*Qs*(p+21*Qs^2) := by
  apply MvPolynomial.funext
  intro v
  simp [Ms,rat]
  ring

/-- The source symplectic form before substituting dQ. -/
theorem omega_Q (i j : Var) :
    wedge x pInv i j + wedge Qs zInv i j =
      rat (9/2)*Qs*(p+21*Qs^2)*wedge x Qs i j + 3*Qs^2*wedge x p i j +
      Cs*wedge Qs p i j + 2*As*wedge x z i j -3*x^2*wedge Qs z i j := by
  fin_cases i <;> fin_cases j <;> apply MvPolynomial.funext <;> intro v <;>
    simp [wedge,pInv,zInv,Qs,Ms,As,Cs,rat,x,q,p,z] <;> ring

/-- Residual two-form on (X,Y,W,E₀), with zero fourth row and column. -/
def theta : Matrix Var Var P :=
  !![0,coreLift Core.A1,coreLift Core.A2,0;
     -coreLift Core.A1,0,coreLift Core.A3,0;
     -coreLift Core.A2,-coreLift Core.A3,0,0;
     0,0,0,0]

/-- Every coefficient of ω=dR∧dD₀+Θ in the source coordinates. -/
theorem omega_split (i j : Var) :
    wedge x pInv i j + wedge Qs zInv i j = wedge (coreLift Core.r) z i j + theta i j := by
  fin_cases i <;> fin_cases j <;> apply MvPolynomial.funext <;> intro v <;>
    simp [wedge,theta,pInv,zInv,Qs,Ms,As,Cs,rat,x,q,p,z,coreLift,
      Core.r,Core.A1,Core.A2,Core.A3,Core.Q3,Core.crat,Core.Xc,Core.Yc,Core.Wc] <;> ring

variable (K : Type*) [Field K] [CharZero K]

def wedgeK (f g : MvPolynomial Var K) (i j : Var) :=
  pderiv i f * pderiv j g - pderiv j f * pderiv i g

theorem wedge_map (f g : P) (i j : Var) :
    wedgeK K (mapK K f) (mapK K g) i j = mapK K (wedge f g i j) := by
  simp only [wedgeK,wedge,mapK,pderiv_map,map_sub,map_mul]

/-- Actual source-form coefficients after extension to K, in particular C. -/
theorem omega_split_charZero (i j : Var) :
    wedgeK K (mapK K x) (mapK K pInv) i j +
      wedgeK K (mapK K Qs) (mapK K zInv) i j =
      wedgeK K (mapK K (coreLift Core.r)) (mapK K z) i j + mapK K (theta i j) := by
  simp only [wedge_map, ← map_add, omega_split]

end
end Forms
end SourceCoordinates
end RankTwoPoisson
