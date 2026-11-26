# Appendix: Arguments due to Carbon

Two arguments in this formalization are due to Gemini Carbon, and were subsequently proved in Lean.

## The converse affine–Riccati duality

The paper's converse implication in Theorem 4.2(ii) asserts that, whenever a finitely supported initial tensor $u_0$ has a finite signature transform and the exponential-affine formula holds through some classical Riccati solution, a classical solution of the Riccati equation exists for which
$\mathbb{E}\bigl[\exp\langle u_0,\widehat W_T\rangle \bigm| \mathcal F_t\bigr]
= \exp\langle \psi(T-t), \widehat W_t\rangle$
almost surely for every $t\in[0,T]$. This fails as a universal statement, for every signature volatility model and every Brownian driver, with no appeal to hypothesis H3.

The counterexample is the one-parameter family
$u_0^{(\lambda)} = 2\lambda\, e_{[1,1,1]} - \lambda\, e_{[1,0]} - 12\lambda^2\, e_{[1,1,1,1,0]}$,
for $\lambda\ge 1$.
The Riccati vector field vanishes on each such tensor, and the signature transform is finite: $\int \exp\langle u_0^{(\lambda)},\widehat W_t\rangle\,dP \le 1$. If the affine identity held for some Riccati solution, Brownian scaling would force $\log v_1$ to agree almost everywhere with an entire function of exponential type zero and at most quartic growth, hence with a polynomial; a polynomial bounded on $(-\infty,0]$ is constant, contradicting $v_1\to 0$ at $+\infty$. Lean proves this contradiction, and does not claim that the exponential is a local martingale or that it fails to be a true martingale. The same family refutes the paper's iff and the full Theorem B conjunction.

## Literal and terminal-only NFLVR

Definitions 2.17 and 4.3 form the cone of terminal gains of $S$-admissible strategies with no lower bound on wealth. Section 4.6 later requires only that the terminal wealth be bounded from below. Neither wording is the Delbaen–Schachermayer condition, which asks for a uniform-in-time bound: some $a\ge 0$ with $V^H_t\ge -a$ almost surely for every $t\in[0,T]$.

On the geometric grid $t_n=T(1-2^{-n})$, a doubling integrand holds the constant weight $c_n=(1-X_{t_n})/\sqrt{\Delta t_n}$ on the stochastic interval $(t_n,\tau_n]$, where $\tau_n$ is the first hit of $B_t-B_{t_n}=\sqrt{\Delta t_n}$, and vanishes after the first miss. The decay of the miss probabilities uses only independent Brownian increments; no Dambis–Dubins–Schwarz time change is required. The wealth $V=\int K\,dB$ has continuous paths, starts at $0$, and satisfies $V_T=1$ almost surely. The Black–Scholes transfer $H=K/(S\sigma_0)$ yields the same terminal free lunch in that market. Thus both the literal cone and the terminal-only cone fail NFLVR. The same $V$ is unbounded below on $[0,T]$, so the construction does not refute Delbaen–Schachermayer NFLVR, which is proved for the unwrapped signature-price process in the forward fragment of Theorem B.

Carbon also observed that the uniformly bounded-below statement does not use H3: once $S$ is a continuous local martingale of the form $dS=S\xi\,dB$, every bounded-below stochastic integral $\int H S\xi\,dB$ is a supermartingale, hence has nonpositive mean. Hypothesis H3 (Novikov) upgrades $S$ itself to a square-integrable true martingale, as in Theorem A.
