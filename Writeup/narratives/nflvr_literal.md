# Literal and terminal-only NFLVR fail

Lean: `not_literal_nflvr` and `not_terminal_bdd_nflvr`, compared as `not_literal_nflvr_unwrapped` and `not_terminal_bdd_nflvr_unwrapped`. The construction and the distinction among the three NFLVR wordings are due to Gemini Carbon.

The paper's Definition 2.17 asks only that a predictable $H$ satisfy $\int_0^T H_s^2 S_s^2 \sigma_s^2\,ds < \infty$ almost surely, with no lower bound on the wealth $V^H$. Definition 4.3 then forms the cone of terminal gains of such strategies. Section 4.6 later writes that the terminal wealths are "bounded from below". Neither wording is the Delbaen–Schachermayer condition, which requires a uniform-in-time bound: some $a \ge 0$ with $V^H_t \ge -a$ almost surely for every $t \in [0,T]$.

Lean refutes the first two wordings, and only those, for the Black–Scholes market ($T > 0$, $s_0 > 0$, $\sigma_0 \neq 0$, one-dimensional Brownian motion), with the closed-form price $s_0 \exp(\sigma_0 B_t - \tfrac12 \sigma_0^2 t)$ on $[0,T]$ and constant volatility $\sigma_0$.

The counterexample is a geometric-grid doubling strategy. On the grid $t_n = T(1-2^{-n})$, the integrand $K$ holds the constant weight $c_n = (1-X_{t_n})/\sqrt{\Delta t_n}$ on the stochastic interval $(t_n, \tau_n]$, where $\tau_n$ is the first hit of $B_t - B_{t_n} = \sqrt{\Delta t_n}$, and is zero after the first miss. No Dambis–Dubins–Schwarz time change is used: the decay $P(E_n) \le q^n$ comes from independent Brownian increments. The wealth $V = \int K\,dB$ starts at $0$, has continuous paths, and satisfies $V_T = 1$ almost surely. The Black–Scholes transfer is $H = K/(S\sigma_0)$, which is $S$-admissible and satisfies $H S \sigma_0 = K$, so the same $V$ is the Itô integral in that market.

Thus $V_T = 1$ is a nontrivial free lunch in the literal cone and also in the terminal-only bounded-below cone (since $V_T \ge 0$ almost surely). That does not refute Delbaen–Schachermayer NFLVR: this $V$ is unbounded below on $[0,T]$. The uniformly bounded-below cone is precisely the one for which `theorem_B_mp_unwrapped` proves `SatisfiesNFLVR_DS`.
