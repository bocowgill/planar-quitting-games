# Uniform equilibrium in planar quitting games

**A finite quitting game has a uniform Nash equilibrium payoff if its singleton quitting payoff vectors lie in an affine plane.** There can be any finite number of players. Payoffs when several players quit together, and payoffs while everyone continues, are unrestricted. This proves a special case of the multiplayer stochastic-game question. [Proof notes](PROOF.md) · [Formal Conjectures #7957](https://github.com/google-deepmind/formal-conjectures/issues/7957)

**Private review draft. Working paper forthcoming.** OpenAI Codex helped with the Lean formalization.

## The game and the result

At each live date, every player simultaneously chooses whether to quit or continue, using independent randomization. If everyone continues, the players receive the live-stage payoff and play moves to the next date. Otherwise the set of players who quit determines a payoff vector that is paid on that date and every later date. The planar condition concerns the vectors paid when exactly one player quits.

The theorem gives one payoff vector $`u`$. For each tolerance $`\varepsilon>0`$, it gives one strategy profile $`\sigma^\varepsilon`$ and one threshold $`H`$. For every horizon $`N\ge H`$, every player $`i`$, and every unilateral behavioral deviation $`\tau_i`$, the expected $N$-stage average payoffs satisfy

```math
\left|\gamma_i^N(\sigma^\varepsilon)-u_i\right|\le\varepsilon,
\qquad
\gamma_i^N(\tau_i,\sigma_{-i}^\varepsilon)
\le\gamma_i^N(\sigma^\varepsilon)+\varepsilon.
```

Before absorption there is only one possible public history at each date, so a deviation can select any sequence of quitting probabilities, including a plan to continue forever. An absorbing initial state pays its fixed prize at every date.

## Proof outline

1. Compare the payoff of quitting immediately with the payoff of waiting. Brouwer degree can force a stationary exit by comparing the local behavior at unanimous continuation with the global behavior of the payoff comparisons.
2. In the directed-cycle case, use the polygon formed by the solo-payoff inequalities to schedule quitting attempts. At each date only one player may quit with positive probability. Subdividing those attempts makes simultaneous quits with a deviator rare and preserves the initial promised payoff.

The proof handles degenerate planar configurations by perturbing the singleton rewards and bounding the effect on every finite-horizon payoff. [Proof notes](PROOF.md)

## Lean formalization

The checked theorem is `PlanarQuitting.periodic_calendar_uniform_payoff`. It starts from a periodic calendar with individually rational continuation promises and a positive rival quitting opportunity for every player. It proves that the calendar can be refined to support its initial promise as a uniform Nash payoff. The proof checks the independent distribution over quitting coalitions and the bounds against arbitrary behavioral deviations. [Challenge.lean](Challenge.lean) · [Solution.lean](Solution.lean) · [Lean proof](PlanarQuitting/Independent.lean)

The full affine-plane existence statement is recorded in Lean. The step that derives a stationary exit or a suitable calendar from the geometry remains a paper proof. The Comparator configuration selects the checked calendar implication. [Full target](PlanarQuitting/Target.lean) · [Comparator configuration](comparator.json) · [Formalization metadata](formalization.yaml)

## Local verification

The review draft pins Lean 4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Run these commands from the project root with Elan installed.

```sh
lake exe cache get
lake --wfail build PlanarQuitting Solution
lake build Challenge
```

The Challenge contains one deliberate `sorry` at the statement to compare. The solution theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. A Palomar submission requires a public release licence, a supported toolchain replay, full mechanical preflight, and maintainer approval of the exact snapshot. [Palomar submission guide](https://palomar-registry.org/how-to-submit)
