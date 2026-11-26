# Carbon's analysis of literal and terminal-only NFLVR

The following is a compact mathematical account of the Gemini Carbon analysis that supplied the doubling construction and the distinction among the three NFLVR wordings. The uniformly bounded-below statement, which Carbon identified as the correct one, is now a proved theorem: `SatisfiesNFLVR_DS` for `BoundedBelowGains` of the unwrapped signature-price process.

Definitions 2.17 and 4.3 define $S$-admissibility with no lower bound on $V^H$, and form the NFLVR cone literally from the terminal gains of such strategies. Under that definition, NFLVR fails. Section 4.6 later requires only that terminal wealth be bounded from below. A lower bound only on $V^H_T$ is still false: the counterexample produces $V^H_T = 1$ almost surely, hence is bounded below at maturity, while $\inf_{t\le T} V^H_t$ is unbounded below.

What holds is Delbaen–Schachermayer admissibility: a uniform-in-time lower bound, some $a\ge 0$ with $V^H_t \ge -a$ almost surely for every $t\in[0,T]$. Once $S$ is a continuous local martingale of the form $dS = S\xi\,dB$, every such bounded-below integral is a supermartingale, hence has nonpositive mean. Hypothesis H3 is not used for that implication; it upgrades $S$ itself to a square-integrable true martingale.

Instead of a exploding integrand $1/(T-s)$, the counterexample is a geometric-grid doubling strategy on $t_n = T(1-2^{-n})$, with constant position $c_n = (1-X_{t_n})/\sqrt{\Delta t_n}$ on $[t_n,t_{n+1}]$, stopped at the first hit of $B_t-B_{t_n}=\sqrt{\Delta t_n}$. Independent increments give a uniform miss probability $q<1$. The Black–Scholes transfer is $H=K/(S\sigma_0)$.
