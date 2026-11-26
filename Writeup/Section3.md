# §3 Theorem B — NFLVR and Riccati duality

Paper: Theorem B / §4 (true martingale and NFLVR under H3; special semimartingales of signature coordinates; affine–Riccati duality for finite transforms).

The proved forward fragment `theorem_B_mp_unwrapped` asserts, under H3, that there is a signature-price process $S$ which is a martingale on the signature filtration, for which Delbaen–Schachermayer NFLVR holds in the cone of uniformly bounded-below admissible gains whose integrand $HS\sigma$ lies in $\mathcal{F}^W$-predictable $L^2$ and whose wealth is a continuous genuine $L^2$ Itô integral against $W^0$ (narrower than the paper's local class $\int H^2\,d\langle S\rangle<\infty$ almost surely), for which every signature coordinate is a special semimartingale, and for which the forward half of the affine–Riccati duality holds. The bundled theorem `theorem_B_mp` keeps the pointwise packaged solution of Theorem A and asserts the same NFLVR for a continuous version of that solution, equal to it almost surely at each time. This is not a proof of the paper's full Theorem B, whose conjunction includes the converse duality.

The converse affine/Riccati duality is false as a universal statement. The false theorem has been removed; its negation, and the resulting failure of the full Theorem B conjunction, are proved and compared. The scaled-tensor family that drives the disproof is due to Gemini Carbon. Why the counterexample works is recorded with the main results.

The paper's literal NFLVR (Definitions 2.17 and 4.3, no wealth lower bound) and the terminal-only bound in Section 4.6 are both false for Black–Scholes. The compared refutations use a geometric-grid doubling strategy due to Gemini Carbon, transferred by $H=K/(S\sigma_0)$. That construction does not refute Delbaen–Schachermayer NFLVR: the wealth is unbounded below on $[0,T]$. The uniformly bounded-below genuine $L^2$ Itô cone is the one for which NFLVR is proved in the forward fragment, and that cone is narrower than the paper's local class.

- [Theorem B (statement and proof)](Section3/TheoremB.md)
- [Supporting modules](Section3/SupportingModules.md)
