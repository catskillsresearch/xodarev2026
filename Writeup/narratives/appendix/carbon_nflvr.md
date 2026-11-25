# Carbon audit of literal and terminal-only NFLVR

This is a compact excerpt of the Gemini "Carbon" outside notes pasted by Lars Warren Ericson for the NFLVR formalization (full draft in the working tree at `.carbon/carbon_nflvr_v1.txt`, not part of the publication). It is preserved so the write-up can cite the source of the doubling construction and of the distinction among the three wordings. Lean theorems that were actually proved are `not_literal_nflvr` and `not_terminal_bdd_nflvr` (compared as `…_unwrapped`); Result 1 below is Carbon's analysis of the uniformly bounded-below statement and is **not** a Lean theorem in this repository.

## Exact discrepancy in the paper (arXiv:2605.17142v1)

- **Definition 2.17 + Definition 4.3** define $S$-admissibility with **no lower bound** on $V^H$, and define the NFLVR cone literally as $C := \{V^H_T - f : H\text{ is }S\text{-admissible},\ f \ge 0\} \cap L^\infty(\mathcal F^{\widehat W}_T, P)$. Under this literal definition, **NFLVR fails**.
- **Section 4.6** later writes "whose terminal wealths are bounded from below" and $C = (K - L^0_+) \cap L^\infty$. A lower bound **only on the terminal wealth** $V^H_T \ge -a$ is **still false**. The counterexample produces $V^H_T = 1$ a.s. (bounded below by $0$ at maturity $T$), while $\inf_{t \le T} V^H_t$ is unbounded below, so $1$ already lies in the terminal-bounded-below cone.
- **What is true (Carbon's Result 1, not formalized here):** Delbaen–Schachermayer (1994) admissibility — a **uniform-in-time** lower bound: $\exists a \ge 0$ such that $\forall t \in [0,T]$, $V^H_t \ge -a$ a.s.

## Role of H3

Carbon's analysis is that the uniformly bounded-below NFLVR does not use H3: once $S$ is a continuous local martingale of the form $dS = S\,\xi\,dB$, $P$ is an equivalent local martingale measure, and every bounded-below local martingale $V^H = \int H S \xi\,dB$ is a supermartingale under $P$. H3 (Novikov) is what upgrades $S$ itself to a square-integrable true $P$-martingale, as in Theorem A / the martingale clause of Theorem B.

## The counterexample (no DDS)

Instead of $K_s = 1/(T-s)$ (which would need Dambis–Dubins–Schwarz), Carbon uses a **geometric-grid doubling strategy** on $t_n = T(1-2^{-n})$ with a single constant position $c_n = (1-X_{t_n})/\sqrt{\Delta t_n}$ on $[t_n, t_{n+1}]$, stopped at the first hit $\tau_n$ of $B_t - B_{t_n} = \sqrt{\Delta t_n}$. Because the increments are independent and $P(\text{no hit on }[t_n,t_{n+1}]) \le q < 1$, the argument uses only Itô isometry on $L^2$ integrands, path continuity, independent increments, and a standard-normal tail. The Black–Scholes transfer is $H = K/(S\sigma_0)$.
