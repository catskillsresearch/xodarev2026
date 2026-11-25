# Why Lemma 77 (Lemma B.1, weighted shuffle estimate) fails

**Lean:** `not_lemma77_shuffle_estimate`, `not_lemma77_of_hypH2`
(`Lemma77ShuffleEstimateFalse.lean`). Both are compared.

**Claim.** Under H2 there is `C` with `‖a ⧢ b‖_w ≤ C ‖a‖_w ‖b‖_w` on `T_w`.

**Counterexample.** This already fails on basis words, for every weight and every letter `ℓ`. We
have `ℓ^k ⧢ ℓ = (k+1) ℓ^(k+1)`. So `‖e_{ℓ^k} ⧢ e_ℓ‖_w = (k+1) w(k+1) ≥ (k+1) w(k)`, while
`‖e_{ℓ^k}‖_w ‖e_ℓ‖_w = w(k) w(1)`. Taking `k ≥ |C| w(1)` contradicts any `C`.

The paper's proof absorbs a binomial factor `≤ 2ⁿ` into "an equivalent weight", but `2ⁿ w(n)` is
not equivalent to `w`. The Lean statement is `¬ ∃ C, ∀ I J, ‖e_I ⧢ e_J‖_w ≤ C ‖e_I‖_w ‖e_J‖_w`.

**Source material.** No verbatim Carbon text found. See `README.md`.
