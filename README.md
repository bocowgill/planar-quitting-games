# Uniform equilibrium in planar quitting games

**A finite quitting game has a uniform Nash equilibrium payoff if its singleton quitting payoff vectors lie in an affine plane.** There can be any finite number of players. Payoffs when several players quit together, and payoffs while everyone continues, are unrestricted. This proves a special case of the multiplayer stochastic-game question. [Proof notes](PROOF.md) · [Formal Conjectures #7957](https://github.com/google-deepmind/formal-conjectures/issues/7957)

**Working paper forthcoming.** OpenAI Codex helped with the Lean formalization.

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

1. Compare the payoff of quitting immediately with the payoff of waiting. A signed count of the roots near unanimous continuation can force a stationary exit. When the comparison selects one quitter, a finite cutoff controls the incentive to wait indefinitely.
2. In the directed-cycle case, use the polygon formed by the solo-payoff inequalities to schedule quitting attempts. At each date only one player may quit with positive probability. Subdividing those attempts makes simultaneous quits with a deviator rare and preserves the initial promised payoff.

The proof handles degenerate planar configurations by perturbing the singleton rewards and bounding the effect on every finite-horizon payoff. [Proof notes](PROOF.md)

## Lean formalization

The complete planar theorem is checked as `PlanarQuitting.planar_uniform_payoff`. The definition of `HasUniformPayoff` quantifies over every later horizon and every unilateral behavioral deviation after choosing one profile and threshold. The same profile and threshold also work from every absorbing initial state, as checked by `PlanarQuitting.planar_uniform_payoff_all_states`. [Theorems](PlanarQuitting/Existence.lean) · [Game and payoff definitions](PlanarQuitting/Target.lean)

- **Stationary comparison or directed cycle.** The signed count and the boundary walk give the existence alternative for the regular core. [Signed count](PlanarQuitting/PlanarComparison.lean) · [Stationary comparisons](PlanarQuitting/StationaryGuard.lean)
- **Uniform payoff.** The equilibrium verification covers the directed quitting calendar, the stationary profile, the one-quitter cutoff, and permanent continuation. [Cycle](PlanarQuitting/CycleImplementation.lean) · [Stationary profile](PlanarQuitting/Stationary.lean) · [One quitter and permanent continuation](PlanarQuitting/SoloVerification.lean)
- **Degenerate cases.** Approximation by regular planar games and uniform payoff bounds extend existence to every affine-plane representation. [Regular approximation](PlanarQuitting/RegularApproximation.lean) · [Payoff stability](PlanarQuitting/PayoffClosure.lean)

## Local verification

The review draft pins Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. Run these commands from the project root with Elan installed.

```sh
lake exe cache get
lake --wfail build PlanarQuitting Solution
lake build Challenge
```

The Comparator configuration selects the full theorem. The standalone Challenge contains one deliberate `sorry` at that statement. The solution uses only `propext`, `Classical.choice`, and `Quot.sound`. [Challenge](Challenge.lean) · [Comparator configuration](comparator.json) · [Formalization metadata](formalization.yaml)
