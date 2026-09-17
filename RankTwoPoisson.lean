import RankTwoPoisson.CharacteristicZero
import RankTwoPoisson.Complex
import RankTwoPoisson.ExactFiber
import RankTwoPoisson.Symplectic
import RankTwoPoisson.CoreGeometry
import RankTwoPoisson.SourceEquivalence
import RankTwoPoisson.PoissonCalculus
import RankTwoPoisson.InducedBracket
import RankTwoPoisson.DerivativeCertificate
import RankTwoPoisson.SourceForms
import RankTwoPoisson.HigherRank
import RankTwoPoisson.WeylEndomorphism
import RankTwoPoisson.WeylAlgebra

/-!
# An explicit counterexample to the rank-two Poisson conjecture

The main exported theorems are:

* `RankTwoPoisson.explicit_counterexample`, over `ℚ`;
* `RankTwoPoisson.explicit_counterexample_complex`, over `ℂ`;
* `RankTwoPoisson.explicit_counterexample_charZero K`, uniformly for every
  field `K` of characteristic zero;
* `RankTwoPoisson.Fiber.exact_fiber_complex`, the exhaustive three-point fiber;
* `RankTwoPoisson.Symplectic.main_complex`, all conclusions of the main theorem;
* `RankTwoPoisson.HigherRank.every_rank`, non-surjective Poisson maps for every n≥2;
* `RankTwoPoisson.Weyl.explicit_counterexample_complex`, the actual non-surjective
  endomorphism of the fourth Weyl algebra.
-/
