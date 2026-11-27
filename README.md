# Uniform equilibrium in planar quitting games

**Private review draft. Working paper forthcoming.**

The paper theorem asserts existence of a uniform Nash equilibrium payoff in an ordinary finite quitting game when the payoff vectors from singleton quitting coalitions lie in an affine plane. The game permits any finite number of players and arbitrary rewards for larger quitting coalitions and for continuing. The [proof notes](PROOF.md) describe the stationary-exit and directed-cycle cases.

OpenAI Codex helped with the Lean formalization.

## Lean verification

The [target definition](PlanarQuitting/Target.lean) states the full planar existence problem in the ordinary quitting game. Its payoff and regret tests use one independently randomized behavioral profile per tolerance for every sufficiently large horizon. Each deviation can change the player's quitting probability at every live date. There is exactly one live public history per date, so these sequences represent all live behavioral strategies. Absorbing initial states pay their prize forever.

The [checked theorem](PlanarQuitting/Independent.lean) proves that a periodic volunteer calendar satisfying the displayed promise equations, individual rationality inequalities, and rival quitting opportunities yields a uniform Nash payoff. Its formal game model sums the independent product distribution over all quitting coalitions. The proof bisects each scheduled step to lower the collision risk while preserving the initial promise. It bounds finite-horizon regret for every deviation, including never quitting.

The [Challenge](Challenge.lean), [Solution](Solution.lean), and [Comparator configuration](comparator.json) select this conditional calendar theorem. The existence of an exit or suitable calendar from the affine-plane assumption itself remains a paper argument. In particular the general continuous degree comparison for the cube and the piecewise-linear complementarity map, the polygon classification, and the stationary-exit implementation remain outside the checked theorem.

## Local build

```sh
lake exe cache get
lake --wfail build PlanarQuitting Solution
lake build Challenge
```

The intentional proof hole in Challenge states the result independently. The solution theorem's transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`. This snapshot uses Lean 4.33.1. A Palomar submission would need a public release licence, a supported toolchain replay, a full mechanical preflight, and maintainer approval of the exact snapshot.
