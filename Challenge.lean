module

public import PlanarQuitting.Target

/-!
# Uniform equilibrium in planar quitting games

The target is the existence of a uniform Nash payoff for every finite
quitting game whose singleton absorbing prizes lie in an affine plane.
-/

@[expose] public section

namespace PlanarQuitting

set_option warn.sorry false in
theorem planar_uniform_payoff (I : Type*) [Fintype I] [DecidableEq I] :
    PlanarExistence I := by
  sorry

end PlanarQuitting
