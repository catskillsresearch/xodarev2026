# Why Lemma 78 (Lemma B.2 / (2.20), local Lipschitz bound for `ℛ`) fails

**Lean:** `not_lemma78_local_lipschitz` (`Lemma78RiccatiLipschitzFalse.lean`), compared.

**Claim.** The Riccati operator `ℛ` is locally Lipschitz on bounded subsets of `T_w`.

**Counterexample.** Take the H2 weight `w ≡ 1`, at least one space letter `ℓ`, radius `ρ = 1`
and `v = 0` (`ℛ(0) = 0`). Then `u_k = e_{ℓ^(k+1)}` has `‖u_k‖_w = 1`. But the coefficient of
`ℛ(u_k)` at `ℓ^(2k)`, which comes from the quadratic shuffle term, is `½ binom(2k, k) ≥ k`. So
`‖ℛ(u_k) − ℛ(0)‖_w ≥ k`, and no `L` works: `ℛ` is not even bounded on the unit ball.

The Lean statement is the negation of
`∀ ρ > 0, ∃ L, ∀ u v ∈ T_w, ‖u‖, ‖v‖ ≤ ρ → ℛu − ℛv ∈ T_w ∧ ‖ℛu − ℛv‖_w ≤ L ‖u − v‖_w`,
for `w ≡ 1` and `d + 2` letters.

**Source material.** No verbatim Carbon text found. See `README.md`.
