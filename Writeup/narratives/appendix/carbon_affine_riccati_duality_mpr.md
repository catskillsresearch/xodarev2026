# Affine / Riccati duality, `←` direction — counterexample notes

**Status (this repository):** The false sorry'd theorem `affine_riccati_duality_mpr` has been **removed** from the library. There is no `AffineRiccatiDualityMpr`. The honest negation `not_affine_riccati_duality_mpr` is proved sorry-free in [`AffineRiccatiDualityMprCounterexample`](../../../SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMprCounterexample.lean). `not_affine_riccati_duality` (the paper iff fails), `not_theorem_B_mpr` and `not_theorem_B` hang off that module. The proved directions `affine_riccati_duality_mp` and `theorem_B_mp` are kept. The kit constructor `signatureRiccatiKit_of_setup` has been dropped. All four negations are proved and compared in `comparator.json`. A short, accurate narrative of the Lean proof is in [`../affine_riccati_duality_mpr.md`](../affine_riccati_duality_mpr.md); the text below is the verbatim outside source.

**Source of the argument:** Gemini Carbon (outside opinion), 2026-11-24, pasted by Lars (t80u). The sections below are preserved as a historical memorialization of that message: the verdict, literature context, the complete 7-step disproof, the first Lean 4 blueprint, the practical takeaway, the later filled-in Lean file (Parts 1–5), and the four-pillar roadmap. Later work folded Carbon's Girsanov-free routes into the build; the text below should not be taken as a description of the current module split. The citation [arXiv:2606.29622](https://arxiv.org/abs/2606.29622) has **not** been verified by us.

---

## Editorial note

Lars asked Gemini Carbon for a disproof of `affine_riccati_duality_mpr`. The first reply included a 7-step argument and a Lean blueprint that still had `sorry`s. Lars then asked for a filled-in version; that second file fills the algebraic and assembly parts and isolates four analytic/probabilistic pillars as `sorry`. Both texts are included below, in order, as received.

---

### Verdict

**`affine_riccati_duality_mpr` is FALSE as stated — you cannot fill the `sorry`.**

In fact, a stronger disproof holds: **for *every* fixed `M : SignatureVolatilityModel` (any dimension $d \ge 1$, any horizon $T > 0$, and any admissible weight `M.w`) and any `B : MultiBrownian Ω P M.d`, there exists a finitely supported tensor $u_0$ for which both hypotheses hold and the conclusion fails.**

This also explains why Carbon kept looping and timing out: Carbon found the right base counterexample $u_0 = 2 e_{[1,1,1]} - e_{[1,0]} - 12 e_{[1,1,1,1,0]}$ (for which `riccatiOp u₀ = 0` and $\exp\langle u_0, \widehat{W}_t\rangle$ is a strict local martingale), and then got stuck trying to rule out the existential quantifier `∃ sol` for that *single* $u_0$ at fixed weight $w \equiv 1$ — where exponential type $1$ alone **cannot** rule out $\log v(s, x)$ (there *do* exist entire functions of exponential type $1$ that are bounded on $(-\infty, 0]$ and grow like $-\frac{2}{3}x^3$ as $x \to +\infty$, e.g. convolving $-y^3 \mathbf{1}_{y>0}$ with a band-limited Schwartz kernel).

To kill the existential quantifier `∃ sol` completely, you only need to **scale** $u_0$ into a one-parameter family $u_0^{(\lambda)}$ ($\lambda \ge 1$). Brownian scaling then forces the conditional log-transform to be an entire function of **exponential type zero** (not just type $1$) with polynomial growth on $\mathbb{R}$, which forces it to be a polynomial — yielding an immediate, completely elementary contradiction.

---

### Literature Context (2025–2026)

Your earlier survey predated two key papers by Abi Jaber and coauthors that explain both halves of why this theorem breaks:

1. **Strict local martingales in signature models — Abi Jaber, Gassiat, and Sotnikov**, *Martingale property and moment explosions in signature volatility models* ([arXiv:2503.17103](https://arxiv.org/abs/2503.17103), *Finance and Stochastics*, 2026):
   They prove that for a signature volatility process $\sigma_t = \langle \sigma, \widehat{W}_t \rangle$, the Doléans–Dade exponential $\mathcal{E}(\int \sigma_s\, dB_s)$ is a **strict local martingale** whenever the leading degree of $\sigma$ is even (or the correlation has the wrong sign). Our counterexample takes the simplest even-degree case $\sigma_t = \lambda W_t^2$ (degree $2$), which corresponds to a finitely supported $u_0^{(\lambda)}$ with `riccatiOp u₀^(λ) = 0`.
2. **Failure of global signature expansions for the log-Laplace transform — Abi Jaber, Attal, and Sotnikov**, *Affine Structure of the Brownian Signature* ([arXiv:2606.29622](https://arxiv.org/abs/2606.29622), June/July 2026):
   They prove that while the conditional Fourier–Laplace transform admits an entire signature expansion solving a linear tensor ODE, its **logarithm (the Riccati representation) is intrinsically local**. Zeros/singularities in the complex plane prevent a global Riccati representation in $T_w$; global representations require randomized Riccati equations via recentering.

**Editorial note:** The arXiv:2606.29622 citation has not been verified by us.

**Consequence for your formalization:** Adding a true-martingale / CSFT integrability condition is **mathematically necessary**, not merely a proof convenience. Without ruling out strict local martingales, `affine_riccati_duality_mpr` is literally refutable.

---

### Complete Disproof of `affine_riccati_duality_mpr`

Fix **any** `M : SignatureVolatilityModel` (so $d := M.d \ge 1$, $T := M.T > 0$, and $w := M.w$ satisfies $w(0) = 1$, $w > 0$, `Monotone w`, and `HypH2 w`), and any probability space $(\Omega, P)$ carrying `B : MultiBrownian Ω P M.d`.

Let $1 := (0 : \mathrm{Fin}\, d).\mathrm{succ} \in \mathrm{Fin}(d+1)$ denote the first spatial letter (well-defined since $d > 0$), and write $W_t := B.\mathrm{W}\, t\, \cdot\, 0$ for the first 1D Brownian coordinate.

#### Step 1. The counterexample family $u_0^{(\lambda)}$
For every $\lambda > 0$, define the finitely supported tensor $u_0^{(\lambda)} \in \mathrm{FreeTensorAlgebra}(d+1)$ (supported on words of length $\le 5$) by
$$u_0^{(\lambda)} := 2\lambda\, e_{[1,1,1]} - \lambda\, e_{[1,0]} - 12\lambda^2\, e_{[1,1,1,1,0]}.$$

#### Step 2. `Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀^(λ))` holds
Check `riccatiOp` directly against the exact definitions in `foo.lean.txt`:
- **`rightShift 0`:** `(rightShift 0 u₀^(λ)).coeff K = u₀^(λ).coeff (K ++ [0])`, which equals $-\lambda$ at $K = [1]$, $-12\lambda^2$ at $K = [1,1,1,1]$, and $0$ otherwise.
- **`stratonovichHalfLaplacian`:** `(1/2) * ∑ i, u₀^(λ).coeff (K ++ [i.succ, i.succ])` is nonzero only for $i = 0$ and $K = [1]$ (since $[1] ++ [1,1] = [1,1,1]$), where it equals $\frac{1}{2}(2\lambda) = \lambda$.
- **`rightShift i.succ`:** vanishes for $i \neq 0$, and for $i = 0$ equals $2\lambda\, e_{[1,1]}$.
- **Shuffle square:** `(1/2) * (shuffleFinite (2λ e_{[1,1]}) (2λ e_{[1,1]}) K.length).coeff K`.
  Every word in `shuffleWords [1,1] [1,1]` is $[1,1,1,1]$ of length $4$, with multiplicity $\binom{4}{2} = 6$. At $K = [1,1,1,1]$, `K.length = 4 ≥ 2`, so $m = 2, n = 2 \in \mathrm{Finset.range}\ 5$ are included, giving
  $$\frac{1}{2} (2\lambda)(2\lambda) \cdot 6 = 12\lambda^2.$$
  At all other $K$, the term is $0$.

Summing the three pieces gives **`riccatiOp u₀^(λ) = 0` identically**. Therefore the constant curve $\psi_{\mathrm{const}}(s) \equiv u_0^{(\lambda)}$ is a `ClassicalRiccatiSolution M.w M.T riccatiOp u₀^(λ)`:
- `mem_Tw` and `uniform_bdd` hold trivially because $u_0^{(\lambda)}$ is finitely supported;
- `init` is `rfl`;
- `integral_eq` holds because the integrand is identically $0$.

#### Step 3. `SignatureTransformFinite P (paperSetup B M.hT) u₀^(λ)` holds
By `paperSig2_shuffle` and `ae_itoWordIntegral_time_cons` (already proved in `foo.lean.txt`), for every $t \in [0, T]$, almost surely:
$$\langle e_{[1,1,1]}, \widehat{W}_t \rangle = \frac{1}{6} W_t^3, \qquad \langle e_{[1,0]}, \widehat{W}_t \rangle = \int_0^t W_r\, dr, \qquad \langle e_{[1,1,1,1,0]}, \widehat{W}_t \rangle = \frac{1}{24} \int_0^t W_r^4\, dr.$$
Hence, by Itô's formula on $f(x) = \frac{\lambda}{3} x^3$ ($d(\frac{\lambda}{3}W_t^3) = \lambda W_t^2\, dW_t + \lambda W_t\, dt$),
$$\langle u_0^{(\lambda)}, \widehat{W}_t \rangle = \frac{\lambda}{3} W_t^3 - \lambda \int_0^t W_r\, dr - \frac{\lambda^2}{2} \int_0^t W_r^4\, dr = \int_0^t \lambda W_r^2\, dW_r - \frac{1}{2} \int_0^t (\lambda W_r^2)^2\, dr \quad \text{a.s.}$$
Thus $M_t^{(\lambda)} := \exp\langle u_0^{(\lambda)}, \widehat{W}_t \rangle = \mathcal{E}\!\left(\int_0^\cdot \lambda W_r^2\, dW_r\right)_t$ is a positive continuous local martingale starting at $M_0^{(\lambda)} = 1$, hence a nonnegative supermartingale by Fatou's lemma along any localizing sequence. Consequently,
$$\mathbb{E}\!\left[\exp\langle u_0^{(\lambda)}, \widehat{W}_t \rangle\right] \le 1 < \infty \qquad \forall t \in [0, T],$$
verifying `SignatureTransformFinite`.

#### Step 4. Conditional expectation and Brownian scaling
Note that `(paperSetup B M.hT).signatureFiltration.σAlg t = (pathFiltration B).σAlg t` (since `(W_hat u).coeff [i.succ] = W^i_u` and `sig_adapted_to_W` gives the reverse inclusion). For any $t \in (0, T)$, writing $W_{t+r} = W_t + \widetilde{B}_r$ where $\widetilde{B}$ is a standard 1D Brownian motion independent of $\mathcal{F}_t$,
$$\mathbb{E}\!\left[M_T^{(\lambda)} \,\middle|\, \mathcal{F}_t\right] = M_t^{(\lambda)} \cdot v_\lambda(T - t, W_t) \quad \text{a.s.},$$
where for $s > 0$ and $x \in \mathbb{R}$,
$$v_\lambda(s, x) := \mathbb{E}\!\left[\exp\!\left(\frac{\lambda}{3}\big((x + B_s)^3 - x^3\big) - \lambda \int_0^s (x + B_r)\, dr - \frac{\lambda^2}{2} \int_0^s (x + B_r)^4\, dr\right)\right].$$
Setting $c := \lambda^{1/3}$ and substituting the rescaled Brownian motion $\widehat{B}_u := c B_{c^{-2} u}$ ($u = c^2 r$) gives the **exact scaling identity**
$$v_\lambda(s, x) = v_1\!\left(\lambda^{2/3} s,\; \lambda^{1/3} x\right) \qquad (\lambda, s > 0,\ x \in \mathbb{R}).$$

#### Step 5. Exact conditional signature polynomials and exponential-type bound
We claim that for any $t \in (0, T)$ and any $\phi \in T_w$, the function $G(x) := \mathbb{E}[\langle \phi, \widehat{W}_t \rangle \mid W_t = x]$ agrees Lebesgue-a.e. with an **entire function of exponential type $\le 1$**:
$$|G(z)| \le C(\phi, t, d)\, e^{|z|} \qquad \forall z \in \mathbb{C}.$$

**Proof:** Let $E_t(\mu) := \exp(\mu W_t - \frac{1}{2}\mu^2 t)$ (involving only the first Brownian coordinate $W = W^0$). For every word $I \in \{0, 1, \dots, d\}^*$, let $f_I(t) := \mathbb{E}[\langle e_I, \widehat{W}_t \rangle E_t(\mu)]$. Using $dE_t = \mu E_t\, dW_t$, Fubini, and Itô isometry on the Stratonovich recursion $\langle e_{Ij}, \widehat{W}_t \rangle = \int_0^t \langle e_I, \widehat{W}_r \rangle \circ dX_r^j$ (noting that $W^i$ is independent of $W^0$ for $i \ge 1$):
$$f_{[]}(t) = 1, \quad f_{I0}'(t) = f_I(t), \quad f_{I1}'(t) = \mu f_I(t) + \frac{1}{2}\mathbf{1}_{I = K1} f_K(t), \quad f_{Ij}'(t) = \frac{1}{2}\mathbf{1}_{I = Kj} f_K(t)\ (j \ge 2),$$
with $f_I(0) = 0$ for $I \neq []$. By induction on $|I|$ (this is the Girsanov-tilted Fawcett formula),
$$\mathbb{E}\!\left[\langle e_I, \widehat{W}_t \rangle\, e^{\mu W_t}\right] = e^{\frac{1}{2}\mu^2 t} \left\langle e_I,\; \exp_\otimes\!\left(t \left(e_0 + \mu e_1 + \frac{1}{2}\sum_{j=1}^d e_{jj}\right)\right) \right\rangle.$$
Let $H_k(z; t) := \mathbb{E}[(z + i\sqrt{t}\, G)^k]$ ($G \sim \mathcal{N}(0, 1)$) be the monic Hermite polynomial of variance $t$, which satisfies $\mathbb{E}[H_k(W_t; t)\, e^{\mu W_t}] = e^{\frac{1}{2}\mu^2 t} (t\mu)^k$. Matching bilateral Laplace transforms yields the exact closed form
$$P_{I, t}(x) := \mathbb{E}\!\left[\langle e_I, \widehat{W}_t \rangle \,\middle|\, W_t = x\right] = \sum_{a + k + 2b = |I|} c(I; a, k, b_1, \dots, b_d)\, \frac{t^{a + b}}{2^b (a + k + b)!}\, H_k(x; t),$$
where $b = b_1 + \dots + b_d$ and $c(I; a, k, b_1, \dots, b_d)$ counts decompositions of $I$ into $a$ copies of $[0]$, $k$ copies of $[1]$, and $b_j$ copies of $[j, j]$.

Now bound $|H_k(z; t)| \le \mathbb{E}[(|z| + \sqrt{t}\, |G|)^k]$ and sum over all words $I$ of length $n$. Since $\sum_{|I|=n} c(I; a, k, b_1, \dots, b_d) = \frac{(a + k + b)!}{a!\, k!\, b_1! \cdots b_d!}$, the $(a + k + b)!$ factor cancels completely:
$$\sum_{n=0}^\infty \sum_{|I| = n} |P_{I, t}(z)| \le \sum_{a, k, b_1, \dots, b_d \ge 0} \frac{t^a}{a!} \left(\prod_{j=1}^d \frac{(t/2)^{b_j}}{b_j!}\right) \frac{\mathbb{E}[(|z| + \sqrt{t}\,|G|)^k]}{k!} \le 2 \exp\!\left(t + \frac{(d+1)t}{2}\right) e^{|z|}.$$
Since `M.w` is monotone with $w(0) = 1$, we have $w(n) \ge 1$ for all $n$, so $|\phi_I| \le \|\phi_n\|_2 \le w(n)\|\phi_n\|_2 \le \|\phi\|_{T_w}$. Therefore
$$G(z) := \sum_{n=0}^\infty \sum_{|I| = n} \phi_I\, P_{I, t}(z)$$
converges absolutely and uniformly on compacts to an entire function satisfying $|G(z)| \le 2 \|\phi\|_{T_w} \exp(t + \frac{(d+1)t}{2})\, e^{|z|}$. By `factorial_moment_control` ($p = 1$, constant weight $1$), $\sum_n |\mathrm{levelInner}\ \phi\ \widehat{W}_t\ n| \in L^1(P)$, so dominated convergence lets us interchange $\mathbb{E}[\cdot \mid W_t]$ with the sum, giving $\mathbb{E}[\langle \phi, \widehat{W}_t \rangle \mid W_t] = G(W_t)$ a.s. $\square$

#### Step 6. Assuming `affine_riccati_duality_mpr` forces $F(x) = \log v_1(s_0, x)$ to be a polynomial
Assume for contradiction that `affine_riccati_duality_mpr` holds for `M`, `B`, and all $u_0^{(\lambda)}$ ($\lambda \ge 1$). Fix $s_0 := T / 2 > 0$. For each $\lambda \ge 1$, set
$$s_\lambda := \lambda^{-2/3} s_0 \in (0, T/2], \qquad t_\lambda := T - s_\lambda \in [T/2, T),$$
and let $\mathrm{sol}_\lambda$ be the resulting `ClassicalRiccatiSolution`. At $t = t_\lambda$, taking logarithms of the conditional expectation identity and setting $\phi_\lambda := \mathrm{sol}_\lambda.\psi(s_\lambda) - u_0^{(\lambda)} \in T_w$ gives
$$\langle \phi_\lambda, \widehat{W}_{t_\lambda} \rangle = \log v_\lambda(s_\lambda, W_{t_\lambda}) = \log v_1(s_0, \lambda^{1/3} W_{t_\lambda}) \quad \text{a.s.}$$
By Step 5, for each $\lambda \ge 1$ there is an entire function $G_\lambda$ with $|G_\lambda(z)| \le C_\lambda e^{|z|}$ such that $G_\lambda(x) = \log v_1(s_0, \lambda^{1/3} x)$ for Lebesgue-a.e. $x \in \mathbb{R}$.

Define $F_\lambda(z) := G_\lambda(\lambda^{-1/3} z)$. Then:
1. $F_\lambda$ is entire and satisfies $|F_\lambda(z)| \le C_\lambda \exp(\lambda^{-1/3} |z|)$ for all $z \in \mathbb{C}$.
2. For Lebesgue-a.e. $x \in \mathbb{R}$, $F_\lambda(x) = \log v_1(s_0, x) = F_1(x)$. Since $F_\lambda$ and $F_1$ are continuous, $F_\lambda = F_1$ on $\mathbb{R}$, hence on all of $\mathbb{C}$ by the Identity Theorem.

Thus $F := F_1$ is an entire function of **exponential type zero**:
$$\forall \varepsilon > 0,\ \exists C_\varepsilon,\ \forall z \in \mathbb{C},\quad |F(z)| \le C_\varepsilon e^{\varepsilon |z|}.$$

Next, $F$ is **polynomially bounded on $\mathbb{R}$**:
- Upper bound: $v_1(s_0, x) \le 1$, so $F(x) \le 0$.
- Lower bound: on the event $E = \{\sup_{0 \le r \le s_0} |B_r| \le 1\}$ (which has probability $p_0 > 0$), every term in the exponent of $v_1(s_0, x)$ is bounded below by $-C_1(1 + |x|^4)$, so $v_1(s_0, x) \ge p_0 \exp(-C_1(1 + |x|^4))$, hence
  $$-C(1 + |x|^4) \le F(x) \le 0 \qquad \forall x \in \mathbb{R}.$$

Let $P_4(z)$ be the degree-$4$ Taylor polynomial of $F$ at $0$, and set $H(z) := (F(z) - P_4(z)) / z^5$. Then $H$ is entire of exponential type zero, and $H(x) \to 0$ as $|x| \to \infty$, so $M := \sup_{x \in \mathbb{R}} |H(x)| < \infty$. By Phragmén–Lindelöf on the upper and lower half-planes (for each $\delta > 0$, $e^{i\delta z} H(z)$ is bounded on $\mathbb{H}_+$ via the two quadrants with comparison factor $\exp(-\eta(e^{-i\pi/4}z)^{3/2})$, then bounded by $M$ on $\mathbb{H}_+$ via $(z+i)^{-\eta}$ as $\eta \to 0^+$; letting $\delta \to 0^+$ gives $|H(z)| \le M$ on $\mathbb{H}_+$, and symmetrically on $\mathbb{H}_-$), $H$ is bounded on $\mathbb{C}$. By Liouville's theorem $H \equiv 0$, so **$F = P_4$ is a polynomial of degree $\le 4$**.

#### Step 7. Contradiction: $\log v_1(s_0, x)$ cannot be a polynomial
By Girsanov's theorem on the exit times $\tau_R = \inf\{r \ge 0 : |x + B_r| \ge R\}$ (where the drift is bounded, so Novikov holds) and monotone convergence as $R \to \infty$,
$$v_1(s_0, x) = \mathbb{Q}_x(\tau_\infty > s_0),$$
where under $\mathbb{Q}_x$, $Y$ solves $dY_r = Y_r^2\, dr + d\widetilde{B}_r$, $Y_0 = x$, up to its explosion time $\tau_\infty$. (Note $Y_r \ge x + \widetilde{B}_r$, so $Y$ can only explode to $+\infty$.)

1. **Bounded on $(-\infty, 0]$:** For any $x \le 0$, couple $Y^{(x)}$ and $Y^{(0)}$ with the same Brownian motion $\widetilde{B}$. Then $D_r := Y_r^{(0)} - Y_r^{(x)}$ is $C^1$ with $D_0 = -x \ge 0$ and $D'(r) = (Y_r^{(0)} + Y_r^{(x)}) D(r)$, so $D_r \ge 0$ up to $\tau_\infty(0)$. Hence $\tau_\infty(x) \ge \tau_\infty(0)$ a.s., giving
   $$0 < v_1(s_0, 0) \le v_1(s_0, x) \le 1 \qquad \forall x \le 0.$$
   Therefore $\log v_1(s_0, 0) \le F(x) \le 0$ for all $x \le 0$. The only polynomial bounded on $(-\infty, 0]$ is a **constant**: $F(x) \equiv c$.

2. **Decays to $-\infty$ as $x \to +\infty$:** For $x > 2/s_0$, consider the event $A_x = \{\sup_{0 \le r \le s_0} |\widetilde{B}_r| \le x/2\}$. If $\tau_\infty > s_0$ on $A_x$, then $u(r) := \int_0^r Y_q^2\, dq$ satisfies $Y_q = x + u(q) + \widetilde{B}_q \ge \frac{x}{2} + u(q) > 0$, so $u'(q) \ge (\frac{x}{2} + u(q))^2$ on $[0, s_0]$. Integrating gives
   $$\frac{2}{x} > \frac{2}{x} - \frac{1}{\frac{x}{2} + u(s_0)} = \int_0^{s_0} \frac{u'(q)}{(\frac{x}{2} + u(q))^2}\, dq \ge s_0,$$
   contradicting $x > 2/s_0$. Hence $Y$ must explode by time $s_0$ on $A_x$, so
   $$v_1(s_0, x) = \mathbb{Q}_x(\tau_\infty > s_0) \le \mathbb{P}\!\left(\sup_{0 \le r \le s_0} |\widetilde{B}_r| > \frac{x}{2}\right) \xrightarrow{x \to +\infty} 0.$$
   Thus $F(x) \to -\infty$ as $x \to +\infty$, contradicting that $F$ is constant. $\blacksquare$

---

### Lean 4 Blueprint for the Counterexample

Below is the exact Lean 4 construction of the counterexample family $u_0^{(\lambda)}$ and the algebraic half (`riccatiOp (counterexampleTensor d hd lam) = 0` and `Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp ...)`), matching the declarations in `foo.lean.txt` *(not compiled against Lean in this chat; you may need minor `simp`/`fin_cases` tweaks depending on your Mathlib version)*:

```lean
namespace SignatureVolatility

open ExtTensorAlgebra Set

/-- First spatial letter `1 = (0 : Fin d).succ` when `0 < d`. -/
def firstSpace {d : ℕ} (hd : 0 < d) : Letter (d + 1) :=
  (⟨0, hd⟩ : Fin d).succ

/-- Counterexample tensor `u₀^(λ) = 2λ e_{[1,1,1]} - λ e_{[1,0]} - 12λ² e_{[1,1,1,1,0]}`. -/
def counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ) : ExtTensorAlgebra (d + 1) :=
  let l1 := firstSpace hd
  ⟨fun I =>
    if I = [l1, l1, l1] then 2 * lam
    else if I = [l1, 0] then -lam
    else if I = [l1, l1, l1, l1, 0] then -12 * lam ^ 2
    else 0⟩

lemma counterexampleU0_isFinitelySupported {d : ℕ} (hd : 0 < d) (lam : ℝ) :
    IsFinitelySupported (counterexampleU0 hd lam) := by
  refine ⟨5, fun I hI => ?_⟩
  simp only [counterexampleU0]
  split_ifs with h1 h2 h3
  · subst h1; simp at hI
  · subst h2; simp at hI
  · subst h3; simp at hI
  · rfl

/-- Exact algebraic kernel property: `ℛ(u₀^(λ)) = 0`. -/
lemma riccatiOp_counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ) :
    riccatiOp (counterexampleU0 hd lam) = 0 := by
  -- Sketch: ext K, split into K = [l1], K = [l1,l1,l1,l1], and all other K:
  -- • At K = [l1]: rightShift 0 gives -lam, stratonovichHalfLaplacian gives +lam, shuffle gives 0.
  -- • At K = [l1,l1,l1,l1]: rightShift 0 gives -12*lam^2, half-Laplacian gives 0,
  --   and shuffleFinite (2*lam e_{[l1,l1]}) (2*lam e_{[l1,l1]}) 4 gives (1/2)*(2*lam)*(2*lam)*6 = 12*lam^2.
  -- • Elsewhere: all three terms are 0.
  sorry

/-- Constant classical Riccati solution `ψ(s) ≡ u₀^(λ)` (valid for any `M.w`, `M.T`). -/
noncomputable def counterexampleRiccatiSol (M : SignatureVolatilityModel) (lam : ℝ) :
    ClassicalRiccatiSolution M.w M.T riccatiOp (counterexampleU0 M.hd lam) where
  ψ := fun _ => counterexampleU0 M.hd lam
  mem_Tw := fun _ _ => by
    -- Finitely supported ⇒ `levelNorm n = 0` for `n > 5` ⇒ summable
    sorry
  uniform_bdd := ⟨normW M.w (counterexampleU0 M.hd lam),
    tsum_nonneg fun n => mul_nonneg (M.w.pos n).le (ExtTensorAlgebra.levelNorm.nonneg _ _),
    fun _ _ => le_rfl⟩
  init := rfl
  integral_eq := fun t _ I => by
    have h0 : riccatiOp (counterexampleU0 M.hd lam) = 0 := riccatiOp_counterexampleU0 M.hd lam
    refine ⟨by simpa [h0] using continuousOn_const, ?_⟩
    simp [h0]

/-- The negation of `affine_riccati_duality_mpr` holds for EVERY fixed `M` and `B`. -/
theorem not_affine_riccati_duality_mpr (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d) :
    ¬ ∀ u₀ : FreeTensorAlgebra (M.d + 1),
      SignatureTransformFinite P (paperSetup B M.hT) u₀.1 →
      Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1) →
      ∃ sol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
        ∀ t ∈ Icc 0 M.T,
          Integrable (fun ω => Real.exp (dualPairing u₀.1 ((paperSetup B M.hT).W_hat M.T ω))) P ∧
          P[fun ω => Real.exp (dualPairing u₀.1 ((paperSetup B M.hT).W_hat M.T ω)) |
            (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
            fun ω => Real.exp (dualPairing (sol.ψ (M.T - t)) ((paperSetup B M.hT).W_hat t ω)) := by
  -- Follows from Steps 1–7 above applied to `u₀ = ⟨counterexampleU0 M.hd lam, ...⟩` for `lam ≥ 1`.
  sorry

end SignatureVolatility
```

---

### Practical Takeaway for Your Project

1. **You can close the open question definitively:** Theorem 4.2(ii) of the paper you are formalizing is **false as stated** — the gap in §4.4 is not just an unsupported step, it is a genuine false theorem.
2. **To get a true (and useful) Theorem B:** Add **CSFT's integrability / uniform-integrability bound** (e.g., $\mathbb{E}[\sup_{t \in [0,T]} \exp\langle \psi(T-t), \widehat{W}_t \rangle] < \infty$, or directly assuming the local martingale $\exp\langle \psi(T-t), \widehat{W}_t \rangle$ is a true martingale), as discussed in your earlier notes. That is the weakest, sharpest hypothesis that rules out exactly the strict-local-martingale counterexamples above.
3. **If you want to formalize `not_affine_riccati_duality_mpr` in Lean:** Notice that formalizing the *full* disproof in Lean requires Girsanov + Fawcett/Hermite conditional expectation + Phragmén–Lindelöf (substantial Mathlib work), whereas formalizing a **refutation of the stronger version** ("*for a given* `sol`, $\exp\langle \text{sol.}\psi(T-t), \widehat{W}_t\rangle$ is a true martingale") only needs `u₀ = counterexampleU0 M.hd 1` + showing $\mathbb{E}[M_T] < 1$ via a single ODE comparison on the stopped Girsanov measure.

---

## Filled-in Lean file (Parts 1–5)

The first blueprint still had `sorry`s. Lars asked for a filled-in version. The text below is Gemini Carbon's second reply, preserved verbatim-faithfully. Being completely upfront about what is filled vs. what still needs Mathlib infrastructure, as in that reply:

- **Completely filled (no `sorry`s):**
  1. `counterexampleU0` and `counterexampleU0_isFinitelySupported`
  2. `riccatiOp_counterexampleU0`: complete algebraic proof that $\mathcal{R}(u_0^{(\lambda)}) = 0$ for all $d > 0$ and $\lambda \in \mathbb{R}$
  3. `counterexampleRiccatiSol`: complete `ClassicalRiccatiSolution` (`mem_Tw`, `uniform_bdd`, `init`, `integral_eq`) for every `M : SignatureVolatilityModel`
  4. `dualPairing_counterexampleU0`: exact 3-term reduction of the infinite `tsum`
  5. `ae_paperSig2_space_two` / `three` / `four`, `ae_paperSig2_append_zero`, and `ae_dualPairing_counterexampleU0_eq`: complete proof that
     $$\langle u_0^{(\lambda)}, \widehat{W}_t \rangle = \frac{\lambda}{3} W_t^3 - \lambda \int_0^t W_r\, dr - \frac{\lambda^2}{2} \int_0^t W_r^4\, dr \quad \text{a.s.}$$
     using only lemmas already proved in `foo.lean.txt`
  6. `poly4_const_of_bdd_nonpos`: degree-$\le 4$ polynomial bounded on $(-\infty, 0]$ is constant
  7. `not_affine_riccati_duality_mpr`: complete top-level disproof assembling the 4 analytic pillars below.

- **Isolated as 4 modular analytic/probabilistic sub-lemmas (still `sorry`):**
  - `signatureTransformFinite_counterexampleU0` (Itô's formula + localization + Fatou $\Rightarrow \mathbb{E}[M_t^{(\lambda)}] \le 1$)
  - `condExp_counterexampleU0_eq` (Markov property + Brownian scaling + stopped Girsanov + ODE explosion bounds for $v_1(s_0, x)$)
  - `exists_entire_expTypeOne_of_memTw` (Girsanov–Fawcett/Hermite expansion $\Rightarrow \mathbb{E}[\langle \phi, \widehat{W}_t\rangle \mid W_t = x]$ extends to an entire function of exponential type $\le 1$)
  - `entire_expTypeZero_polyBound_is_poly4` (Phragmén–Lindelöf + Liouville)

Those four are genuine multi-hundred-line Mathlib projects (especially Girsanov + Itô's formula on stopped processes), so isolating them cleanly is the right decomposition before building them out.

Here is a full attempt at formalizing the disproof directly on top of `foo.lean.txt`.

I don't have a live Lean 4 compiler in this chat, so minor tactic/Mathlib-name tweaks may be needed when you drop it into your repo. **This file has not been compiled in this repository.**

```lean
section Counterexample

open MeasureTheory Filter Topology Set
open scoped BigOperators Classical ENNReal NNReal

namespace SignatureVolatility

open ExtTensorAlgebra

/-! ## Part 1: Purely algebraic / combinatorial core (sorry-free) -/

private lemma append_singleton_eq_iff {α : Type*} {K L : List α} {a b : α} :
    K ++ [a] = L ++ [b] ↔ K = L ∧ a = b := by
  constructor
  · intro h
    have hr := congrArg List.reverse h
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.cons.injEq] at hr
    exact ⟨List.reverse_injective hr.2, hr.1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private lemma shuffleWords_nil_left {d : ℕ} (J : Word d) :
    shuffleWords [] J = [J] := by
  simp [shuffleWords]

private lemma shuffleWords_cons_nil {d : ℕ} (i : Letter d) (I : Word d) :
    shuffleWords (i :: I) [] = [i :: I] := by
  simp [shuffleWords]

private lemma shuffleWords_cons_cons {d : ℕ} (i j : Letter d) (I J : Word d) :
    shuffleWords (i :: I) (j :: J) =
      (shuffleWords I (j :: J)).map (i :: ·) ++ (shuffleWords (i :: I) J).map (j :: ·) := by
  rw [shuffleWords]

private lemma shuffleWords_single_single {d : ℕ} (a : Letter d) :
    shuffleWords [a] [a] = [[a, a], [a, a]] := by
  rw [shuffleWords_cons_cons, shuffleWords_nil_left, shuffleWords_cons_nil]
  simp

private lemma shuffleWords_single_pair {d : ℕ} (a : Letter d) :
    shuffleWords [a] [a, a] = [[a, a, a], [a, a, a], [a, a, a]] := by
  rw [shuffleWords_cons_cons, shuffleWords_nil_left, shuffleWords_single_single]
  simp

private lemma shuffleWords_pair_single {d : ℕ} (a : Letter d) :
    shuffleWords [a, a] [a] = [[a, a, a], [a, a, a], [a, a, a]] := by
  rw [shuffleWords_cons_cons, shuffleWords_single_single, shuffleWords_cons_nil]
  simp

private lemma shuffleWords_single_triple {d : ℕ} (a : Letter d) :
    shuffleWords [a] [a, a, a] =
      [[a, a, a, a], [a, a, a, a], [a, a, a, a], [a, a, a, a]] := by
  rw [shuffleWords_cons_cons, shuffleWords_nil_left, shuffleWords_single_pair]
  simp

private lemma shuffleWords_pair_pair {d : ℕ} (a : Letter d) :
    shuffleWords [a, a] [a, a] =
      [[a, a, a, a], [a, a, a, a], [a, a, a, a],
       [a, a, a, a], [a, a, a, a], [a, a, a, a]] := by
  rw [shuffleWords_cons_cons, shuffleWords_single_pair, shuffleWords_pair_single]
  simp

private lemma shuffleBasis_pair_pair {d : ℕ} (a : Letter d) (K : Word d) :
    (shuffleBasis [a, a] [a, a]).coeff K = if K = [a, a, a, a] then 6 else 0 := by
  simp only [shuffleBasis, shuffleWords_pair_pair, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  split_ifs <;> norm_num

/-- First spatial letter `1 = (0 : Fin d).succ` when `0 < d`. -/
def firstSpace {d : ℕ} (hd : 0 < d) : Letter (d + 1) :=
  (⟨0, hd⟩ : Fin d).succ

lemma firstSpace_ne_zero {d : ℕ} (hd : 0 < d) : firstSpace hd ≠ 0 :=
  Fin.succ_ne_zero _

/-- Counterexample tensor family `u₀^(λ) = 2λ e_{[1,1,1]} - λ e_{[1,0]} - 12λ² e_{[1,1,1,1,0]}`. -/
def counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ) : ExtTensorAlgebra (d + 1) :=
  let l1 := firstSpace hd
  ⟨fun I =>
    if I = [l1, l1, l1] then 2 * lam
    else if I = [l1, 0] then -lam
    else if I = [l1, l1, l1, l1, 0] then -12 * lam ^ 2
    else 0⟩

lemma counterexampleU0_isFinitelySupported {d : ℕ} (hd : 0 < d) (lam : ℝ) :
    IsFinitelySupported (counterexampleU0 hd lam) := by
  refine ⟨5, fun I hI => ?_⟩
  simp only [counterexampleU0]
  split_ifs with h1 h2 h3
  · subst h1; simp at hI
  · subst h2; simp at hI
  · subst h3; simp at hI
  · rfl

lemma rightShift_zero_counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ) (K : Word (d + 1)) :
    (rightShift 0 (counterexampleU0 hd lam)).coeff K =
      if K = [firstSpace hd] then -lam
      else if K = [firstSpace hd, firstSpace hd, firstSpace hd, firstSpace hd] then
        -12 * lam ^ 2
      else 0 := by
  set l1 := firstSpace hd
  have hl1 : l1 ≠ 0 := firstSpace_ne_zero hd
  have h1 : K ++ [0] ≠ [l1, l1, l1] := by
    intro h
    have h' : K ++ [0] = [l1, l1] ++ [l1] := h
    exact hl1 ((append_singleton_eq_iff.mp h').2.symm)
  have h2 : K ++ [0] = [l1, 0] ↔ K = [l1] := by
    simpa using (append_singleton_eq_iff (K := K) (L := [l1]) (a := (0 : Letter (d + 1))) (b := 0))
  have h3 : K ++ [0] = [l1, l1, l1, l1, 0] ↔ K = [l1, l1, l1, l1] := by
    simpa using (append_singleton_eq_iff (K := K) (L := [l1, l1, l1, l1])
      (a := (0 : Letter (d + 1))) (b := 0))
  simp only [rightShift, counterexampleU0, h1, ↓reduceIte, h2, h3]

lemma rightShift_succ_counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ) (i : Fin d)
    (K : Word (d + 1)) :
    (rightShift i.succ (counterexampleU0 hd lam)).coeff K =
      if i = ⟨0, hd⟩ ∧ K = [firstSpace hd, firstSpace hd] then 2 * lam else 0 := by
  set l1 := firstSpace hd
  have hi0 : i.succ ≠ 0 := Fin.succ_ne_zero i
  have h1 : K ++ [i.succ] = [l1, l1, l1] ↔ i = ⟨0, hd⟩ ∧ K = [l1, l1] := by
    have he : K ++ [i.succ] = [l1, l1] ++ [l1] ↔ K = [l1, l1] ∧ i.succ = l1 :=
      append_singleton_eq_iff
    rw [show ([l1, l1, l1] : Word (d + 1)) = [l1, l1] ++ [l1] from rfl, he]
    simp only [l1, firstSpace, Fin.succ_inj, and_comm]
  have h2 : K ++ [i.succ] ≠ [l1, 0] := by
    intro h
    have h' : K ++ [i.succ] = [l1] ++ [0] := h
    exact hi0 (append_singleton_eq_iff.mp h').2
  have h3 : K ++ [i.succ] ≠ [l1, l1, l1, l1, 0] := by
    intro h
    have h' : K ++ [i.succ] = [l1, l1, l1, l1] ++ [0] := h
    exact hi0 (append_singleton_eq_iff.mp h').2
  simp only [rightShift, counterexampleU0, h1, h2, h3, ↓reduceIte]

lemma halfLaplacian_counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ) (K : Word (d + 1)) :
    (stratonovichHalfLaplacian (counterexampleU0 hd lam)).coeff K =
      if K = [firstSpace hd] then lam else 0 := by
  set l1 := firstSpace hd
  have hterm : ∀ i : Fin d,
      (counterexampleU0 hd lam).coeff (K ++ [i.succ, i.succ]) =
        if i = ⟨0, hd⟩ ∧ K = [l1] then 2 * lam else 0 := by
    intro i
    have hi0 : i.succ ≠ 0 := Fin.succ_ne_zero i
    have h1 : K ++ [i.succ, i.succ] = [l1, l1, l1] ↔ i = ⟨0, hd⟩ ∧ K = [l1] := by
      have he : (K ++ [i.succ]) ++ [i.succ] = ([l1] ++ [l1]) ++ [l1] ↔
          K ++ [i.succ] = [l1] ++ [l1] ∧ i.succ = l1 := append_singleton_eq_iff
      rw [show K ++ [i.succ, i.succ] = (K ++ [i.succ]) ++ [i.succ] by simp,
        show ([l1, l1, l1] : Word (d + 1)) = ([l1] ++ [l1]) ++ [l1] from rfl, he,
        append_singleton_eq_iff]
      simp only [l1, firstSpace, Fin.succ_inj]
      tauto
    have h2 : K ++ [i.succ, i.succ] ≠ [l1, 0] := by
      intro h
      have h' : (K ++ [i.succ]) ++ [i.succ] = [l1] ++ [0] := by simpa using h
      exact hi0 (append_singleton_eq_iff.mp h').2
    have h3 : K ++ [i.succ, i.succ] ≠ [l1, l1, l1, l1, 0] := by
      intro h
      have h' : (K ++ [i.succ]) ++ [i.succ] = [l1, l1, l1, l1] ++ [0] := by simpa using h
      exact hi0 (append_singleton_eq_iff.mp h').2
    simp only [counterexampleU0, h1, h2, h3, ↓reduceIte]
  simp only [stratonovichHalfLaplacian, hterm]
  rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · simp only [true_and]
    split_ifs <;> ring
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma quadTerm_counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ) (K : Word (d + 1)) :
    (1 / 2 : ℝ) * ∑ i : Fin d,
      (shuffleFinite (rightShift i.succ (counterexampleU0 hd lam))
        (rightShift i.succ (counterexampleU0 hd lam)) K.length).coeff K =
      if K = [firstSpace hd, firstSpace hd, firstSpace hd, firstSpace hd] then
        12 * lam ^ 2
      else 0 := by
  set l1 := firstSpace hd
  rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · simp only [shuffleFinite, rightShift_succ_counterexampleU0, true_and]
    by_cases hK : K = [l1, l1, l1, l1]
    · subst hK
      have hlen : ([l1, l1, l1, l1] : Word (d + 1)).length = 4 := rfl
      rw [hlen]
      rw [Finset.sum_eq_single 2]
      · rw [Finset.sum_eq_single 2]
        · rw [Finset.sum_eq_single [l1, l1]]
          · rw [Finset.sum_eq_single [l1, l1]]
            · simp only [↓reduceIte, shuffleBasis_pair_pair]
              ring
            · intro J _ hJ; simp [hJ]
            · intro h; exact absurd (wordsOfLength.mem.mpr rfl) h
          · intro I _ hI; simp [hI]
          · intro h; exact absurd (wordsOfLength.mem.mpr rfl) h
        · intro n _ hn
          refine Finset.sum_eq_zero fun I _ => Finset.sum_eq_zero fun J hJ => ?_
          have hJne : J ≠ [l1, l1] := by
            intro heq; subst heq; exact hn (wordsOfLength.mem.mp hJ).symm
          simp [hJne]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      · intro m _ hm
        refine Finset.sum_eq_zero fun n _ =>
          Finset.sum_eq_zero fun I hI => Finset.sum_eq_zero fun J _ => ?_
        have hIne : I ≠ [l1, l1] := by
          intro heq; subst heq; exact hm (wordsOfLength.mem.mp hI).symm
        simp [hIne]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · simp only [hK, ↓reduceIte]
      have hzero :
          ∑ m ∈ Finset.range (K.length + 1),
            ∑ n ∈ Finset.range (K.length + 1),
              ∑ I ∈ wordsOfLength (d + 1) m,
                ∑ J ∈ wordsOfLength (d + 1) n,
                  (if I = [l1, l1] then 2 * lam else 0) *
                    (if J = [l1, l1] then 2 * lam else 0) *
                    (shuffleBasis I J).coeff K = 0 := by
        refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun n _ =>
          Finset.sum_eq_zero fun I _ => Finset.sum_eq_zero fun J _ => ?_
        by_cases hI : I = [l1, l1]
        · by_cases hJ : J = [l1, l1]
          · subst hI; subst hJ
            simp [shuffleBasis_pair_pair, hK]
          · simp [hJ]
        · simp [hI]
      rw [hzero, mul_zero]
  · intro i _ hi
    simp only [shuffleFinite, rightShift_succ_counterexampleU0, hi, false_and, ↓reduceIte,
      zero_mul, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Exact algebraic kernel property**: `ℛ(u₀^(λ)) = 0` identically. -/
theorem riccatiOp_counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ) :
    riccatiOp (counterexampleU0 hd lam) = 0 := by
  ext K
  change ((rightShift 0 (counterexampleU0 hd lam)).coeff K +
      (stratonovichHalfLaplacian (counterexampleU0 hd lam)).coeff K) +
      (1 / 2 : ℝ) * ∑ i : Fin d,
        (shuffleFinite (rightShift i.succ (counterexampleU0 hd lam))
          (rightShift i.succ (counterexampleU0 hd lam)) K.length).coeff K = 0
  rw [rightShift_zero_counterexampleU0, halfLaplacian_counterexampleU0, quadTerm_counterexampleU0]
  set l1 := firstSpace hd
  by_cases h1 : K = [l1]
  · subst h1
    have hne : ([l1] : Word (d + 1)) ≠ [l1, l1, l1, l1] := by simp
    simp only [↓reduceIte, hne]
    ring
  · by_cases h4 : K = [l1, l1, l1, l1]
    · subst h4
      simp only [h1, ↓reduceIte]
      ring
    · simp only [h1, h4, ↓reduceIte]
      ring

/-- Constant classical Riccati solution `ψ(s) ≡ u₀^(λ)` for EVERY `M : SignatureVolatilityModel`. -/
noncomputable def counterexampleRiccatiSol (M : SignatureVolatilityModel) (lam : ℝ) :
    ClassicalRiccatiSolution M.w M.T riccatiOp (counterexampleU0 M.hd lam) where
  ψ := fun _ => counterexampleU0 M.hd lam
  mem_Tw := fun _ _ => by
    refine summable_of_ne_finset_zero (s := Finset.range 6) fun n hn => ?_
    have hn5 : 5 < n := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    obtain ⟨_, hsupp⟩ := ⟨rfl, counterexampleU0_isFinitelySupported M.hd lam⟩
    have hsq : (counterexampleU0 M.hd lam).levelNormSq n = 0 := by
      unfold levelNormSq
      refine Finset.sum_eq_zero fun I hI => ?_
      have hlen : 5 < I.length := by rwa [wordsOfLength.mem.mp hI]
      have h0 : (counterexampleU0 M.hd lam).coeff I = 0 := by
        simp only [counterexampleU0]
        split_ifs with c1 c2 c3
        · subst c1; simp at hlen
        · subst c2; simp at hlen
        · subst c3; simp at hlen
        · rfl
      simp [h0]
    simp [levelNorm, hsq]
  uniform_bdd := ⟨normW M.w (counterexampleU0 M.hd lam),
    tsum_nonneg fun n => mul_nonneg (M.w.pos n).le (levelNorm.nonneg _ _),
    fun _ _ => le_rfl⟩
  init := rfl
  integral_eq := fun t _ I => by
    have h0 : riccatiOp (counterexampleU0 M.hd lam) = 0 := riccatiOp_counterexampleU0 M.hd lam
    have hcoeff : ∀ s, (riccatiOp (counterexampleU0 M.hd lam)).coeff I = 0 := fun _ => by
      rw [h0]; rfl
    refine ⟨?_, ?_⟩
    · simpa only [hcoeff] using continuousOn_const
    · simp only [hcoeff, intervalIntegral.integral_zero, add_zero]

/-! ## Part 2: Exact signature evaluation for `u₀^(λ)` (sorry-free) -/

/-- The infinite `tsum` in `dualPairing (counterexampleU0 hd lam) X` reduces to 3 explicit terms. -/
lemma dualPairing_counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ)
    (X : ExtTensorAlgebra (d + 1)) :
    dualPairing (counterexampleU0 hd lam) X =
      2 * lam * X.coeff [firstSpace hd, firstSpace hd, firstSpace hd]
      - lam * X.coeff [firstSpace hd, 0]
      - 12 * lam ^ 2 *
          X.coeff [firstSpace hd, firstSpace hd, firstSpace hd, firstSpace hd, 0] := by
  set l1 := firstSpace hd
  set u := counterexampleU0 hd lam
  have hzero_len : ∀ n : ℕ, n ≠ 2 → n ≠ 3 → n ≠ 5 → u.levelInner X n = 0 := by
    intro n h2 h3 h5
    refine Finset.sum_eq_zero fun I hI => ?_
    have hlen : I.length = n := wordsOfLength.mem.mp hI
    have hc : u.coeff I = 0 := by
      simp only [u, counterexampleU0]
      split_ifs with c1 c2 c3
      · subst c1; exact absurd hlen.symm h3
      · subst c2; exact absurd hlen.symm h2
      · subst c3; exact absurd hlen.symm h5
      · rfl
    simp [hc]
  have htsum : dualPairing u X = ∑ n ∈ Finset.range 6, u.levelInner X n :=
    tsum_eq_sum fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      exact hzero_len n (by omega) (by omega) (by omega)
  have h2 : u.levelInner X 2 = -lam * X.coeff [l1, 0] := by
    unfold levelInner
    rw [Finset.sum_eq_single [l1, 0]]
    · have hne : ([l1, 0] : Word (d + 1)) ≠ [l1, l1, l1] := by simp
      simp [u, counterexampleU0, hne]
    · intro I hI hIne
      have hlen : I.length = 2 := wordsOfLength.mem.mp hI
      have hc : u.coeff I = 0 := by
        simp only [u, counterexampleU0]
        split_ifs with c1 c2 c3
        · subst c1; simp at hlen
        · exact absurd c2 hIne
        · subst c3; simp at hlen
        · rfl
      simp [hc]
    · intro h; exact absurd (wordsOfLength.mem.mpr rfl) h
  have h3 : u.levelInner X 3 = 2 * lam * X.coeff [l1, l1, l1] := by
    unfold levelInner
    rw [Finset.sum_eq_single [l1, l1, l1]]
    · simp [u, counterexampleU0]
    · intro I hI hIne
      have hlen : I.length = 3 := wordsOfLength.mem.mp hI
      have hc : u.coeff I = 0 := by
        simp only [u, counterexampleU0]
        split_ifs with c1 c2 c3
        · exact absurd c1 hIne
        · subst c2; simp at hlen
        · subst c3; simp at hlen
        · rfl
      simp [hc]
    · intro h; exact absurd (wordsOfLength.mem.mpr rfl) h
  have h5 : u.levelInner X 5 = -12 * lam ^ 2 * X.coeff [l1, l1, l1, l1, 0] := by
    unfold levelInner
    rw [Finset.sum_eq_single [l1, l1, l1, l1, 0]]
    · have hne1 : ([l1, l1, l1, l1, 0] : Word (d + 1)) ≠ [l1, l1, l1] := by simp
      have hne2 : ([l1, l1, l1, l1, 0] : Word (d + 1)) ≠ [l1, 0] := by simp
      simp [u, counterexampleU0, hne1, hne2]
    · intro I hI hIne
      have hlen : I.length = 5 := wordsOfLength.mem.mp hI
      have hc : u.coeff I = 0 := by
        simp only [u, counterexampleU0]
        split_ifs with c1 c2 c3
        · subst c1; simp at hlen
        · subst c2; simp at hlen
        · exact absurd c3 hIne
        · rfl
      simp [hc]
    · intro h; exact absurd (wordsOfLength.mem.mpr rfl) h
  rw [htsum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  rw [hzero_len 0 (by omega) (by omega) (by omega),
    hzero_len 1 (by omega) (by omega) (by omega),
    h2, h3, hzero_len 4 (by omega) (by omega) (by omega), h5]
  ring

section SignatureEval

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

lemma ae_paperSig2_space_two (B : MultiBrownian Ω P d) (i : Fin d) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, (paperSig2 B 0 t ω).coeff [i.succ, i.succ] =
      (MultiBrownian.W B t ω i) ^ 2 / 2 := by
  filter_upwards [paperSig2_shuffle B ht [i.succ] [i.succ]] with ω hω
  simp only [paperSig2_space, MultiBrownian.W_zero, sub_zero, evalShuffleBasis,
    shuffleWords_single_single, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hω
  linarith

lemma ae_paperSig2_space_three (B : MultiBrownian Ω P d) (i : Fin d) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, (paperSig2 B 0 t ω).coeff [i.succ, i.succ, i.succ] =
      (MultiBrownian.W B t ω i) ^ 3 / 6 := by
  filter_upwards [paperSig2_shuffle B ht [i.succ] [i.succ, i.succ],
    ae_paperSig2_space_two B i ht] with ω hω h2
  simp only [paperSig2_space, MultiBrownian.W_zero, sub_zero, h2, evalShuffleBasis,
    shuffleWords_single_pair, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hω
  linarith

lemma ae_paperSig2_space_four (B : MultiBrownian Ω P d) (i : Fin d) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, (paperSig2 B 0 t ω).coeff [i.succ, i.succ, i.succ, i.succ] =
      (MultiBrownian.W B t ω i) ^ 4 / 24 := by
  filter_upwards [paperSig2_shuffle B ht [i.succ] [i.succ, i.succ, i.succ],
    ae_paperSig2_space_three B i ht] with ω hω h3
  simp only [paperSig2_space, MultiBrownian.W_zero, sub_zero, h3, evalShuffleBasis,
    shuffleWords_single_triple, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hω
  linarith

/-- Appending the time letter `0` integrates a Stratonovich signature coordinate in time. -/
lemma ae_paperSig2_append_zero (B : MultiBrownian Ω P d) (I : Word (d + 1)) {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, (paperSig2 B 0 t ω).coeff (I ++ [0]) =
      ∫ s in (0 : ℝ)..t, (paperSig2 B 0 s ω).coeff I := by
  filter_upwards [ae_continuousOn_itoWordIntegral B ht, ae_itoWordIntegral_time_cons B ht]
    with ω hω h0
  set K := I.reverse
  have hH : ∀ s, (paperSig2 B 0 s ω).coeff I =
      ((contractions K).map (fun p => p.1 * itoWordIntegral B 0 s ω p.2)).sum := fun s => by
    rw [paperSig2_coeff, stratWordIntegral_eq_list]
  have hT : (paperSig2 B 0 t ω).coeff (I ++ [0]) =
      ((contractions K).map
        (fun p => p.1 * ∫ s in (0 : ℝ)..t, itoWordIntegral B 0 s ω p.2)).sum := by
    rw [paperSig2_coeff, stratWordIntegral_eq_list]
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      contractions_cons_zero, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp [h0]
  have hint := integral_list_sum (f := fun w s => itoWordIntegral B 0 s ω w) ht hω (contractions K)
  rw [hT, ← hint.2]
  simp only [hH]

lemma ae_continuousOn_paperSig2_coeff (B : MultiBrownian Ω P d) (I : Word (d + 1)) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, ContinuousOn (fun s => (paperSig2 B 0 s ω).coeff I) (Icc 0 N) := by
  filter_upwards [ae_all_iff.2 fun N : ℕ =>
    ae_continuousOn_itoWordIntegral B (Nat.cast_nonneg N)] with ω hω N
  have hH : (fun s => (paperSig2 B 0 s ω).coeff I) =
      fun s => ((contractions I.reverse).map
        (fun p => p.1 * itoWordIntegral B 0 s ω p.2)).sum := by
    funext s; rw [paperSig2_coeff, stratWordIntegral_eq_list]
  rw [hH]
  exact (integral_list_sum (f := fun w s => itoWordIntegral B 0 s ω w)
    (Nat.cast_nonneg N) (hω N) (contractions I.reverse)).1

/-- Exact pathwise evaluation of `⟨u₀^(λ), Ŵ_t⟩` for every `t ≥ 0` (almost surely). -/
theorem ae_dualPairing_counterexampleU0_eq (B : MultiBrownian Ω P d) (hd : 0 < d) (lam : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P,
      dualPairing (counterexampleU0 hd lam) (paperSig2 B 0 t ω) =
        (lam / 3) * (MultiBrownian.W B t ω ⟨0, hd⟩) ^ 3
        - lam * (∫ r in (0 : ℝ)..t, MultiBrownian.W B r ω ⟨0, hd⟩)
        - (lam ^ 2 / 2) * (∫ r in (0 : ℝ)..t, (MultiBrownian.W B r ω ⟨0, hd⟩) ^ 4) := by
  set i0 : Fin d := ⟨0, hd⟩
  set l1 : Letter (d + 1) := firstSpace hd
  have h4_all : ∀ᵐ ω ∂P, ∀ s, 0 ≤ s →
      (paperSig2 B 0 s ω).coeff [l1, l1, l1, l1] = (MultiBrownian.W B s ω i0) ^ 4 / 24 := by
    refine ae_forall_of_continuousOn
      (ae_continuousOn_paperSig2_coeff B [l1, l1, l1, l1])
      (ae_of_all _ fun ω N =>
        (((continuous_W_coord B i0 ω).pow 4).div_const 24).continuousOn)
      fun s hs => ae_paperSig2_space_four B i0 hs.le
  filter_upwards [ae_paperSig2_space_three B i0 ht,
    ae_paperSig2_append_zero B [l1] ht,
    ae_paperSig2_append_zero B [l1, l1, l1, l1] ht,
    h4_all] with ω h3 h10 h40 h4s
  rw [dualPairing_counterexampleU0]
  have h10' : (paperSig2 B 0 t ω).coeff [l1, 0] = ∫ r in (0 : ℝ)..t, MultiBrownian.W B r ω i0 := by
    have h := h10
    simp only [List.singleton_append] at h
    rw [h]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp [paperSig2_space, l1, firstSpace, i0, MultiBrownian.W_zero]
  have h40' : (paperSig2 B 0 t ω).coeff [l1, l1, l1, l1, 0] =
      (∫ r in (0 : ℝ)..t, (MultiBrownian.W B r ω i0) ^ 4) / 24 := by
    have h := h40
    simp only [List.cons_append, List.nil_append] at h
    rw [h, ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht] at hr
    exact h4s r hr.1
  rw [h3, h10', h40']
  ring

/-! ## Part 3: Degree-4 polynomial bounded on `(-∞, 0]` is constant (sorry-free) -/

private lemma poly4_const_of_bdd_nonpos {a₀ a₁ a₂ a₃ a₄ L : ℝ}
    (hbdd : ∀ x : ℝ, x ≤ 0 →
      L ≤ a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 ∧
      a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 ≤ 0) :
    a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 := by
  have habs : ∀ n : ℕ,
      |a₀ + a₁ * (-(n : ℝ)) + a₂ * (-(n : ℝ)) ^ 2 +
        a₃ * (-(n : ℝ)) ^ 3 + a₄ * (-(n : ℝ)) ^ 4| ≤ |L| := by
    intro n
    have h := hbdd (-(n : ℝ)) (neg_nonpos.mpr (Nat.cast_nonneg n))
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le L], by linarith [abs_nonneg L]⟩
  have hpow0 : ∀ (k : ℕ), 0 < k → ∀ c : ℝ,
      Tendsto (fun n : ℕ => c / ((n : ℝ) ^ k)) atTop (𝓝 0) := fun k hk c => by
    have h := tendsto_const_nhds (x := c) |>.div_atTop
      ((tendsto_pow_atTop (Nat.ne_of_gt hk)).comp tendsto_natCast_atTop_atTop)
    simpa [Function.comp_def] using h
  have ha4 : a₄ = 0 := by
    have hlim : Tendsto (fun n : ℕ =>
        |(a₀ + a₁ * (-(n : ℝ)) + a₂ * (-(n : ℝ)) ^ 2 +
          a₃ * (-(n : ℝ)) ^ 3 + a₄ * (-(n : ℝ)) ^ 4) / (n : ℝ) ^ 4|) atTop (𝓝 |a₄|) := by
      have h1 : Tendsto (fun n : ℕ =>
          a₀ / (n : ℝ) ^ 4 - a₁ / (n : ℝ) ^ 3 + a₂ / (n : ℝ) ^ 2 - a₃ / (n : ℝ) ^ 1 + a₄)
          atTop (𝓝 (0 - 0 + 0 - 0 + a₄)) :=
        ((((hpow0 4 (by norm_num) a₀).sub (hpow0 3 (by norm_num) a₁)).add
          (hpow0 2 (by norm_num) a₂)).sub (hpow0 1 (by norm_num) a₃)).add tendsto_const_nhds
      simp only [sub_zero, zero_add] at h1
      refine (h1.abs).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      congr 1; field_simp; ring
    have hle : |a₄| ≤ 0 := le_of_tendsto_of_tendsto hlim (hpow0 4 (by norm_num) |L|) <| by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 4)]
      exact div_le_div_of_nonneg_right (habs n) (by positivity)
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  subst ha4
  have ha3 : a₃ = 0 := by
    have hlim : Tendsto (fun n : ℕ =>
        |(a₀ + a₁ * (-(n : ℝ)) + a₂ * (-(n : ℝ)) ^ 2 +
          a₃ * (-(n : ℝ)) ^ 3) / (n : ℝ) ^ 3|) atTop (𝓝 |-a₃|) := by
      have h1 : Tendsto (fun n : ℕ =>
          a₀ / (n : ℝ) ^ 3 - a₁ / (n : ℝ) ^ 2 + a₂ / (n : ℝ) ^ 1 + (-a₃))
          atTop (𝓝 (0 - 0 + 0 + (-a₃))) :=
        (((hpow0 3 (by norm_num) a₀).sub (hpow0 2 (by norm_num) a₁)).add
          (hpow0 1 (by norm_num) a₂)).add tendsto_const_nhds
      simp only [sub_zero, zero_add] at h1
      refine (h1.abs).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      congr 1; field_simp; ring
    have hle : |-a₃| ≤ 0 := le_of_tendsto_of_tendsto hlim (hpow0 3 (by norm_num) |L|) <| by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 3)]
      have h := habs n; simp only [zero_mul, add_zero] at h
      exact div_le_div_of_nonneg_right h (by positivity)
    simpa [abs_neg] using le_antisymm hle (abs_nonneg _)
  subst ha3
  have ha2 : a₂ = 0 := by
    have hlim : Tendsto (fun n : ℕ =>
        |(a₀ + a₁ * (-(n : ℝ)) + a₂ * (-(n : ℝ)) ^ 2) / (n : ℝ) ^ 2|) atTop (𝓝 |a₂|) := by
      have h1 : Tendsto (fun n : ℕ => a₀ / (n : ℝ) ^ 2 - a₁ / (n : ℝ) ^ 1 + a₂)
          atTop (𝓝 (0 - 0 + a₂)) :=
        ((hpow0 2 (by norm_num) a₀).sub (hpow0 1 (by norm_num) a₁)).add tendsto_const_nhds
      simp only [sub_zero, zero_add] at h1
      refine (h1.abs).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      congr 1; field_simp; ring
    have hle : |a₂| ≤ 0 := le_of_tendsto_of_tendsto hlim (hpow0 2 (by norm_num) |L|) <| by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
      have h := habs n; simp only [zero_mul, add_zero] at h
      exact div_le_div_of_nonneg_right h (by positivity)
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  subst ha2
  have ha1 : a₁ = 0 := by
    have hlim : Tendsto (fun n : ℕ =>
        |(a₀ + a₁ * (-(n : ℝ))) / (n : ℝ) ^ 1|) atTop (𝓝 |-a₁|) := by
      have h1 : Tendsto (fun n : ℕ => a₀ / (n : ℝ) ^ 1 + (-a₁)) atTop (𝓝 (0 + (-a₁))) :=
        (hpow0 1 (by norm_num) a₀).add tendsto_const_nhds
      simp only [zero_add] at h1
      refine (h1.abs).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      congr 1; field_simp; ring
    have hle : |-a₁| ≤ 0 := le_of_tendsto_of_tendsto hlim (hpow0 1 (by norm_num) |L|) <| by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 1)]
      have h := habs n; simp only [zero_mul, add_zero] at h
      exact div_le_div_of_nonneg_right h (by positivity)
    simpa [abs_neg] using le_antisymm hle (abs_nonneg _)
  exact ⟨ha1, rfl, rfl, rfl⟩

/-! ## Part 4: Four isolated analytic/probabilistic pillars (open sub-goals) -/

/-- **Pillar A (Doléans–Dade supermartingale bound)**:
`exp ⟨u₀^(λ), Ŵ_t⟩ = ℰ(∫ λ W_r² dW_r)_t` is a positive local martingale starting at `1`,
hence `𝔼[exp ⟨u₀^(λ), Ŵ_t⟩] ≤ 1 < ∞` for all `t ∈ [0, T]`. -/
lemma signatureTransformFinite_counterexampleU0 (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) (lam : ℝ) :
    SignatureTransformFinite P (paperSetup B M.hT) (counterexampleU0 M.hd lam) := by
  sorry

/-- **Pillar B (Markov + Brownian scaling + stopped Girsanov explosion asymptotics)**:
There exists a function `v₁ : ℝ → ℝ` (namely `x ↦ ℚ_x(τ_∞ > T/2)` for `dY = Y² dr + dB̃`)
such that:
1. `0 < v₁ x ≤ 1` for all `x : ℝ`;
2. polynomial lower bound on `log v₁`: `∃ C ≥ 0, ∀ x, -C * (1 + |x|^4) ≤ Real.log (v₁ x)`;
3. uniform positive lower bound on `(-∞, 0]`: `∀ x ≤ 0, v₁ 0 ≤ v₁ x`;
4. decay to `0` as `x → +∞`: `Tendsto v₁ atTop (𝓝 0)`;
5. for every `lam ≥ 1`, at `t = M.T - lam ^ (-(2/3 : ℝ)) * (M.T / 2) ∈ [M.T/2, M.T)`:
   `𝔼[M_T^(λ) | ℱ_t] = M_t^(λ) * v₁(lam^(1/3) * W_t)` a.s. -/
lemma exists_scaled_survival_function (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    ∃ v₁ : ℝ → ℝ,
      (∀ x, 0 < v₁ x ∧ v₁ x ≤ 1) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, -C * (1 + |x| ^ 4) ≤ Real.log (v₁ x)) ∧
      (∀ x : ℝ, x ≤ 0 → v₁ 0 ≤ v₁ x) ∧
      Tendsto v₁ atTop (𝓝 0) ∧
      ∀ lam : ℝ, 1 ≤ lam →
        let s_lam := lam ^ (-(2 / 3 : ℝ)) * (M.T / 2)
        let t_lam := M.T - s_lam
        P[fun ω => Real.exp (dualPairing (counterexampleU0 M.hd lam)
            ((paperSetup B M.hT).W_hat M.T ω)) |
          (paperSetup B M.hT).signatureFiltration.σAlg t_lam] =ᵐ[P]
          fun ω =>
            Real.exp (dualPairing (counterexampleU0 M.hd lam)
              ((paperSetup B M.hT).W_hat t_lam ω)) *
            v₁ (lam ^ (1 / 3 : ℝ) * MultiBrownian.W B t_lam ω ⟨0, M.hd⟩) := by
  sorry

/-- **Pillar C (Girsanov–Fawcett / Hermite conditional signature expansion)**:
If `ϕ ∈ T_w` and `⟨ϕ, Ŵ_t⟩ = f(W_t^0)` a.s. for a measurable function `f : ℝ → ℝ` at `t ∈ (0, T)`,
then `f` agrees Lebesgue-a.e. with the restriction to `ℝ` of an entire function `G : ℂ → ℂ`
of exponential type `≤ 1` (`∃ C ≥ 0, ∀ z, ‖G z‖ ≤ C * Real.exp ‖z‖`). -/
lemma exists_entire_expTypeOne_of_memTw (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ M.T)
    {ϕ : ExtTensorAlgebra (M.d + 1)} (hϕ : MemTw M.w ϕ) {f : ℝ → ℝ}
    (hfeq : (fun ω => dualPairing ϕ ((paperSetup B M.hT).W_hat t ω)) =ᵐ[P]
      fun ω => f (MultiBrownian.W B t ω ⟨0, M.hd⟩)) :
    ∃ (G : ℂ → ℂ) (C : ℝ), Differentiable ℂ G ∧ 0 ≤ C ∧
      (∀ z : ℂ, ‖G z‖ ≤ C * Real.exp ‖z‖) ∧
      (∀ᵐ x : ℝ ∂volume, G x = (f x : ℂ)) := by
  sorry

/-- **Pillar D (Phragmén–Lindelöf + Liouville)**:
An entire function of exponential type zero with quartic growth on `ℝ` is a polynomial
of degree `≤ 4`. -/
lemma entire_expTypeZero_polyBound_is_poly4 {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (htype0 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (ε * ‖z‖))
    (hpoly : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖F x‖ ≤ C * (1 + |x| ^ 4)) :
    ∃ a₀ a₁ a₂ a₃ a₄ : ℂ, ∀ z : ℂ,
      F z = a₀ + a₁ * z + a₂ * z ^ 2 + a₃ * z ^ 3 + a₄ * z ^ 4 := by
  sorry

/-! ## Part 5: Complete assembly of `not_affine_riccati_duality_mpr` (sorry-free modulo A–D) -/

theorem not_affine_riccati_duality_mpr (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    ¬ ∀ u₀ : FreeTensorAlgebra (M.d + 1),
      SignatureTransformFinite P (paperSetup B M.hT) u₀.1 →
      Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1) →
      ∃ sol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
        ∀ t ∈ Icc 0 M.T,
          Integrable (fun ω => Real.exp (dualPairing u₀.1
            ((paperSetup B M.hT).W_hat M.T ω))) P ∧
          P[fun ω => Real.exp (dualPairing u₀.1 ((paperSetup B M.hT).W_hat M.T ω)) |
            (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
            fun ω => Real.exp (dualPairing (sol.ψ (M.T - t))
              ((paperSetup B M.hT).W_hat t ω)) := by
  intro hthm
  obtain ⟨v₁, hv₁_pos_le, ⟨C_poly, hC_poly0, hv₁_poly⟩, hv₁_nonpos, hv₁_tendsto, hcond⟩ :=
    exists_scaled_survival_function M B
  -- For every `lam ≥ 1`, obtain an entire `F_lam` of exponential type `≤ lam^(-1/3)`
  -- agreeing a.e. on `ℝ` with `log ∘ v₁`.
  have hex_F : ∀ lam : ℝ, 1 ≤ lam →
      ∃ (F : ℂ → ℂ) (C : ℝ), Differentiable ℂ F ∧ 0 ≤ C ∧
        (∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (lam ^ (-(1 / 3 : ℝ)) * ‖z‖)) ∧
        (∀ᵐ x : ℝ ∂volume, F x = (Real.log (v₁ x) : ℂ)) := by
    intro lam hlam
    have hlam_pos : 0 < lam := by linarith
    set u₀ : FreeTensorAlgebra (M.d + 1) :=
      ⟨counterexampleU0 M.hd lam, counterexampleU0_isFinitelySupported M.hd lam⟩
    obtain ⟨sol, hsol⟩ := hthm u₀
      (signatureTransformFinite_counterexampleU0 M B lam)
      ⟨counterexampleRiccatiSol M lam⟩
    set s_lam := lam ^ (-(2 / 3 : ℝ)) * (M.T / 2)
    set t_lam := M.T - s_lam
    have hs_pos : 0 < s_lam := mul_pos (Real.rpow_pos_of_pos hlam_pos _) (half_pos M.hT)
    have hs_le : s_lam ≤ M.T / 2 := by
      have h1 : lam ^ (-(2 / 3 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hlam (by norm_num)
      nlinarith [M.hT]
    have ht_pos : 0 < t_lam := by linarith [M.hT]
    have ht_mem : t_lam ∈ Icc 0 M.T := ⟨ht_pos.le, by linarith⟩
    have hs_mem : M.T - t_lam ∈ Icc 0 M.T := ⟨by simp [t_lam]; linarith, by simp [t_lam]; linarith⟩
    -- Subtract `u₀` from `sol.ψ (M.T - t_lam)` and take logs.
    set ϕ : ExtTensorAlgebra (M.d + 1) := sol.ψ (M.T - t_lam) - u₀.1
    have hϕ_mem : MemTw M.w ϕ := by
      have h1 := sol.mem_Tw (M.T - t_lam) hs_mem
      have h2 := (counterexampleRiccatiSol M lam).mem_Tw 0 ⟨le_rfl, M.hT.le⟩
      refine Summable.of_nonneg_of_le
        (fun n => mul_nonneg (M.w.pos n).le (levelNorm.nonneg _ _))
        (fun n => ?_) (h1.add h2)
      -- Triangle inequality on `levelNorm`: `‖a - b‖_n ≤ ‖a‖_n + ‖b‖_n`.
      have htri : ϕ.levelNorm n ≤ (sol.ψ (M.T - t_lam)).levelNorm n + u₀.1.levelNorm n := by
        unfold levelNorm levelNormSq
        rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
        apply Real.sqrt_le_sqrt
        set A := sol.ψ (M.T - t_lam)
        have hcs :
            (∑ I ∈ wordsOfLength (M.d + 1) n, A.coeff I * u₀.1.coeff I) ^ 2 ≤
              (∑ I ∈ wordsOfLength (M.d + 1) n, A.coeff I ^ 2) *
                (∑ I ∈ wordsOfLength (M.d + 1) n, u₀.1.coeff I ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        have hcs' :
            -(∑ I ∈ wordsOfLength (M.d + 1) n, A.coeff I * u₀.1.coeff I) ≤
              Real.sqrt (∑ I ∈ wordsOfLength (M.d + 1) n, A.coeff I ^ 2) *
                Real.sqrt (∑ I ∈ wordsOfLength (M.d + 1) n, u₀.1.coeff I ^ 2) := by
          rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
          exact (neg_le_abs _).trans (Real.abs_le_sqrt hcs)
        have hexp :
            ∑ I ∈ wordsOfLength (M.d + 1) n, (A.coeff I - u₀.1.coeff I) ^ 2 =
              (∑ I ∈ wordsOfLength (M.d + 1) n, A.coeff I ^ 2) -
                2 * (∑ I ∈ wordsOfLength (M.d + 1) n, A.coeff I * u₀.1.coeff I) +
                (∑ I ∈ wordsOfLength (M.d + 1) n, u₀.1.coeff I ^ 2) := by
          simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, mul_assoc]
          ring
        rw [add_sq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
          Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        change ∑ I ∈ wordsOfLength (M.d + 1) n, (A.coeff I - u₀.1.coeff I) ^ 2 ≤ _
        rw [hexp]
        linarith
      nlinarith [M.w.pos n]
    have hlog_eq : (fun ω => dualPairing ϕ ((paperSetup B M.hT).W_hat t_lam ω)) =ᵐ[P]
        fun ω => Real.log (v₁ (lam ^ (1 / 3 : ℝ) * MultiBrownian.W B t_lam ω ⟨0, M.hd⟩)) := by
      have hce := (hsol t_lam ht_mem).2.symm.trans (hcond lam hlam)
      have hsumm := (paperSetup B M.hT).factorial_moment_control 1 le_rfl (fun _ => 1)
        (fun _ => zero_le_one) ⟨1, fun _ => by simp⟩ ht_pos.le ht_mem.2
      filter_upwards [hce, hsumm.1] with ω hω hWsum
      have hdp_sub :
          dualPairing ϕ ((paperSetup B M.hT).W_hat t_lam ω) =
            dualPairing (sol.ψ (M.T - t_lam)) ((paperSetup B M.hT).W_hat t_lam ω) -
              dualPairing u₀.1 ((paperSetup B M.hT).W_hat t_lam ω) := by
        -- Follows from summability of both `levelInner` series via Cauchy-Schwarz + `MemTw` + `hWsum`.
        have hcs_sum : ∀ a : ExtTensorAlgebra (M.d + 1), MemTw M.w a →
            Summable (fun n => a.levelInner ((paperSetup B M.hT).W_hat t_lam ω) n) := by
          intro a ha
          obtain ⟨K, hK⟩ : ∃ K, ∀ n, a.levelNorm n ≤ K := by
            refine ⟨∑' n, M.w n * a.levelNorm n, fun n => ?_⟩
            have hw1 : 1 ≤ M.w n := by simpa [M.w.w_zero] using M.w.mono (Nat.zero_le n)
            calc a.levelNorm n ≤ M.w n * a.levelNorm n :=
                  le_mul_of_one_le_left (levelNorm.nonneg _ _) hw1
              _ ≤ ∑' k, M.w k * a.levelNorm k :=
                  ha.le_tsum n fun k _ => mul_nonneg (M.w.pos k).le (levelNorm.nonneg _ _)
          refine Summable.of_norm_bounded (hWsum.mul_left K) fun n => ?_
          simp only [Real.norm_eq_abs, one_mul]
          have hcs := Finset.sum_mul_sq_le_sq_mul_sq (wordsOfLength (M.d + 1) n)
            (fun I => a.coeff I) (fun I => ((paperSetup B M.hT).W_hat t_lam ω).coeff I)
          have hle : |a.levelInner ((paperSetup B M.hT).W_hat t_lam ω) n| ≤
              a.levelNorm n * ((paperSetup B M.hT).W_hat t_lam ω).levelNorm n := by
            unfold levelInner levelNorm levelNormSq
            rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
            exact Real.abs_le_sqrt hcs
          exact hle.trans (mul_le_mul_of_nonneg_right (hK n) (levelNorm.nonneg _ _))
        have hsub : ∀ n, ϕ.levelInner ((paperSetup B M.hT).W_hat t_lam ω) n =
            (sol.ψ (M.T - t_lam)).levelInner ((paperSetup B M.hT).W_hat t_lam ω) n -
              u₀.1.levelInner ((paperSetup B M.hT).W_hat t_lam ω) n := fun n => by
          unfold levelInner
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun I _ => ?_
          change ((sol.ψ (M.T - t_lam)).coeff I - u₀.1.coeff I) * _ = _
          ring
        simp only [dualPairing, hsub]
        exact (hcs_sum _ (sol.mem_Tw _ hs_mem)).tsum_sub
          (hcs_sum _ ((counterexampleRiccatiSol M lam).mem_Tw 0 ⟨le_rfl, M.hT.le⟩))
      have hv_pos := (hv₁_pos_le (lam ^ (1 / 3 : ℝ) * MultiBrownian.W B t_lam ω ⟨0, M.hd⟩)).1
      have hlog := congrArg Real.log hω
      rw [Real.log_exp, Real.log_mul (Real.exp_pos _).ne' hv_pos.ne', Real.log_exp] at hlog
      linarith [hdp_sub, hlog]
    obtain ⟨G, C, hG_diff, hC0, hG_bd, hG_ae⟩ :=
      exists_entire_expTypeOne_of_memTw M B ht_pos ht_mem.2 hϕ_mem hlog_eq
    -- Rescale `F(z) = G(lam^(-1/3) * z)`.
    set c : ℝ := lam ^ (-(1 / 3 : ℝ))
    have hc_pos : 0 < c := Real.rpow_pos_of_pos hlam_pos _
    refine ⟨fun z => G ((c : ℂ) * z), C,
      hG_diff.comp (differentiable_const _ |>.mul differentiable_id), hC0, fun z => ?_, ?_⟩
    · calc ‖G ((c : ℂ) * z)‖ ≤ C * Real.exp ‖(c : ℂ) * z‖ := hG_bd _
        _ = C * Real.exp (c * ‖z‖) := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc_pos.le]
    · -- Scaling `x ↦ c * x` preserves Lebesgue null sets.
      have hscale : ∀ᵐ x : ℝ ∂volume,
          G ((c * x : ℝ) : ℂ) = (Real.log (v₁ (lam ^ (1 / 3 : ℝ) * (c * x))) : ℂ) :=
        (Measure.quasiMeasurePreserving_mul_left volume hc_pos.ne').ae hG_ae
      filter_upwards [hscale] with x hx
      have hcancel : lam ^ (1 / 3 : ℝ) * (c * x) = x := by
        rw [← mul_assoc, show c = lam ^ (-(1 / 3 : ℝ)) from rfl,
          ← Real.rpow_add hlam_pos, add_neg_cancel, Real.rpow_zero, one_mul]
      simpa [hcancel, Complex.ofReal_mul] using hx
  -- Fix `F := F_1` and show `F_lam = F` for all `lam ≥ 1` by the Identity Theorem.
  obtain ⟨F, C₁, hF_diff, -, -, hF_ae⟩ := hex_F 1 le_rfl
  have hF_type0 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (ε * ‖z‖) := by
    intro ε hε
    set lam : ℝ := max 1 (ε⁻¹ ^ (3 : ℕ))
    have hlam1 : 1 ≤ lam := le_max_left _ _
    have hlam_pos : 0 < lam := by linarith
    obtain ⟨F_lam, C_lam, hFlam_diff, hClam0, hFlam_bd, hFlam_ae⟩ := hex_F lam hlam1
    -- `F = F_lam` a.e. on `ℝ`, hence everywhere on `ℝ` by continuity, hence on `ℂ` by analyticity.
    have heq_real : ∀ x : ℝ, F x = F_lam x := by
      have hae : (fun x : ℝ => F x) =ᵐ[volume] fun x : ℝ => F_lam x := by
        filter_upwards [hF_ae, hFlam_ae] with x h1 h2
        rw [h1, h2]
      exact Continuous.ae_eq_iff_eq volume
        (hF_diff.continuous.comp Complex.continuous_ofReal)
        (hFlam_diff.continuous.comp Complex.continuous_ofReal) |>.mp hae
    have heq_all : F = F_lam := by
      have hF_an : AnalyticOnNhd ℂ F univ :=
        fun z _ => hF_diff.analyticAt z
      have hFlam_an : AnalyticOnNhd ℂ F_lam univ :=
        fun z _ => hFlam_diff.analyticAt z
      have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), F z = F_lam z := by
        rw [Filter.frequently_iff]
        intro U hU
        rw [mem_nhdsWithin] at hU
        obtain ⟨V, hVopen, h0V, hVU⟩ := hU
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hVopen 0 h0V
        refine ⟨((r / 2 : ℝ) : ℂ), hVU ⟨hball ?_, ?_⟩, heq_real (r / 2)⟩
        · simp [Complex.dist_eq, abs_of_pos (half_pos hr)]; linarith
        · simp [ne_of_gt (half_pos hr)]
      funext z
      exact hF_an.eqOn_of_preconnected_of_frequently_eq hFlam_an isPreconnected_univ
        (mem_univ 0) hfreq (mem_univ z)
    refine ⟨C_lam, hClam0, fun z => ?_⟩
    rw [heq_all]
    have hpow_le : lam ^ (-(1 / 3 : ℝ)) ≤ ε := by
      have h1 : ε⁻¹ ^ (3 : ℕ) ≤ lam := le_max_right _ _
      have h2 : lam ^ (-(1 / 3 : ℝ)) ≤ (ε⁻¹ ^ (3 : ℕ)) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
      refine h2.trans (le_of_eq ?_)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
      exact Real.rpow_neg_one _ ▸ inv_inv ε
    exact (hFlam_bd z).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hpow_le (norm_nonneg z))) hClam0)
  -- `F` has quartic polynomial bound on `ℝ` (from `hF_ae` + continuity + `hv₁_poly`).
  have hF_real_bounds : ∀ x : ℝ, (F x).im = 0 ∧
      -C_poly * (1 + |x| ^ 4) ≤ (F x).re ∧ (F x).re ≤ 0 := by
    have h_ae : ∀ᵐ x : ℝ ∂volume,
        (F x).im = 0 ∧ -C_poly * (1 + |x| ^ 4) ≤ (F x).re ∧ (F x).re ≤ 0 := by
      filter_upwards [hF_ae] with x hx
      rw [hx]
      refine ⟨Complex.ofReal_im _, ?_, ?_⟩
      · simpa [Complex.ofReal_re] using hv₁_poly x
      · simpa [Complex.ofReal_re] using Real.log_nonpos (hv₁_pos_le x).1.le (hv₁_pos_le x).2
    have hclosed : IsClosed {x : ℝ | (F x).im = 0 ∧
        -C_poly * (1 + |x| ^ 4) ≤ (F x).re ∧ (F x).re ≤ 0} := by
      have hcont : Continuous (fun x : ℝ => F x) :=
        hF_diff.continuous.comp Complex.continuous_ofReal
      exact (isClosed_eq (Complex.continuous_im.comp hcont) continuous_const).inter <|
        (isClosed_le (continuous_const.mul (continuous_const.add (continuous_abs.pow 4)))
          (Complex.continuous_re.comp hcont)).inter
        (isClosed_le (Complex.continuous_re.comp hcont) continuous_const)
    have hdense : Dense {x : ℝ | (F x).im = 0 ∧
        -C_poly * (1 + |x| ^ 4) ≤ (F x).re ∧ (F x).re ≤ 0} := by
      refine dense_iff_inter_open.mpr fun U hU hUne => ?_
      have hpos : 0 < volume U := hU.measure_pos volume hUne
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have hsub : U ⊆ {x : ℝ | (F x).im = 0 ∧
          -C_poly * (1 + |x| ^ 4) ≤ (F x).re ∧ (F x).re ≤ 0}ᶜ :=
        Set.disjoint_iff_inter_eq_empty.mpr hempty |>.subset_compl_right
      exact hpos.ne' (measure_mono_null hsub h_ae)
    intro x
    have hx : x ∈ {x : ℝ | (F x).im = 0 ∧ -C_poly * (1 + |x| ^ 4) ≤ (F x).re ∧ (F x).re ≤ 0} := by
      rw [← hclosed.closure_eq, hdense.closure_eq]
      exact mem_univ x
    exact hx
  have hF_poly : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖F x‖ ≤ C * (1 + |x| ^ 4) := by
    refine ⟨C_poly, hC_poly0, fun x => ?_⟩
    obtain ⟨him, hlo, hhi⟩ := hF_real_bounds x
    have hnorm : ‖F x‖ = |(F x).re| := by
      rw [show F x = ((F x).re : ℂ) from Complex.ext rfl him, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, abs_of_nonpos hhi]
    linarith
  -- Apply Pillar D: `F` is a polynomial of degree `≤ 4`.
  obtain ⟨a₀, a₁, a₂, a₃, a₄, hF_eq⟩ := entire_expTypeZero_polyBound_is_poly4 hF_diff hF_type0 hF_poly
  -- On `(-∞, 0]`, `F` is bounded between `log (v₁ 0)` and `0` (by `hv₁_nonpos` + density).
  have hF_nonpos : ∀ x : ℝ, x ≤ 0 → Real.log (v₁ 0) ≤ (F x).re ∧ (F x).re ≤ 0 := by
    have h_ae : ∀ᵐ x : ℝ ∂volume, x ≤ 0 → Real.log (v₁ 0) ≤ (F x).re := by
      filter_upwards [hF_ae] with x hx hx0
      rw [hx, Complex.ofReal_re]
      exact Real.log_le_log (hv₁_pos_le 0).1 (hv₁_nonpos x hx0)
    intro x hx
    refine ⟨?_, (hF_real_bounds x).2.2⟩
    by_contra hlt
    push_neg at hlt
    have hopen : IsOpen {y : ℝ | y < 0 ∧ (F y).re < Real.log (v₁ 0)} :=
      isOpen_Iio.inter (isOpen_lt (Complex.continuous_re.comp
        (hF_diff.continuous.comp Complex.continuous_ofReal)) continuous_const)
    have hne : {y : ℝ | y < 0 ∧ (F y).re < Real.log (v₁ 0)}.Nonempty := by
      have hcont : Continuous (fun y : ℝ => (F y).re) :=
        Complex.continuous_re.comp (hF_diff.continuous.comp Complex.continuous_ofReal)
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont.continuousAt
        ((Real.log (v₁ 0) - (F x).re) / 2) (by linarith)
      refine ⟨x - δ / 2, by linarith, ?_⟩
      have hd : dist (x - δ / 2) x < δ := by
        rw [Real.dist_eq, show x - δ / 2 - x = -(δ / 2) by ring, abs_neg, abs_of_pos (half_pos hδ)]
        linarith
      have h := hball hd
      rw [Real.dist_eq, abs_lt] at h
      linarith
    have hpos := hopen.measure_pos volume hne
    have hsub : {y : ℝ | y < 0 ∧ (F y).re < Real.log (v₁ 0)} ⊆
        {y : ℝ | y ≤ 0 → Real.log (v₁ 0) ≤ (F y).re}ᶜ := by
      intro y ⟨hy0, hylt⟩ h
      exact not_le.mpr hylt (h hy0.le)
    exact hpos.ne' (measure_mono_null hsub h_ae)
  -- Real part of `F(x)` is a real degree-4 polynomial bounded on `(-∞, 0]`, hence constant!
  have hre_poly : ∀ x : ℝ, (F x).re =
      a₀.re + a₁.re * x + a₂.re * x ^ 2 + a₃.re * x ^ 3 + a₄.re * x ^ 4 := by
    intro x
    rw [hF_eq x]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_succ]
    ring
  obtain ⟨ha1, ha2, ha3, ha4⟩ := poly4_const_of_bdd_nonpos (L := Real.log (v₁ 0)) fun x hx => by
    rw [← hre_poly x]; exact hF_nonpos x hx
  have hF_const : ∀ x : ℝ, (F x).re = a₀.re := fun x => by
    rw [hre_poly x, ha1, ha2, ha3, ha4]; ring
  -- Contradiction: `v₁ x → 0` as `x → +∞`, so `log (v₁ x) < a₀.re - 1` for all sufficiently large `x`.
  have hev : ∀ᶠ x : ℝ in atTop, v₁ x < Real.exp (a₀.re - 1) :=
    hv₁_tendsto.eventually (gt_mem_nhds (Real.exp_pos _))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨R, hR⟩ := hev
  -- On `(R, R + 1)` (positive Lebesgue measure), `F x = log (v₁ x)` a.e., giving `a₀.re < a₀.re - 1`.
  have hpos : 0 < volume (Ioo R (R + 1)) := by
    rw [Real.volume_Ioo]; norm_num
  have hsub : Ioo R (R + 1) ⊆ {x : ℝ | F x = (Real.log (v₁ x) : ℂ)}ᶜ := by
    intro x ⟨hxR, _⟩ hxEq
    have hre : a₀.re = Real.log (v₁ x) := by
      rw [← hF_const x, hxEq, Complex.ofReal_re]
    have hlt : v₁ x < Real.exp (a₀.re - 1) := hR x hxR.le
    have hlog : Real.log (v₁ x) < a₀.re - 1 := by
      rw [← Real.log_exp (a₀.re - 1)]
      exact Real.log_lt_log (hv₁_pos_le x).1 hlt
    linarith
  exact hpos.ne' (measure_mono_null hsub hF_ae)

end SignatureVolatility

end Counterexample
```

### Quick Roadmap if You Want to Finish the 4 Pillars in Lean

If your goal is a completely sorry-free refutation in Lean rather than just patching Theorem B with CSFT's integrability bound, here is the relative effort of the 4 pillars:

1. **Pillar D (`entire_expTypeZero_polyBound_is_poly4`) — easiest (~100 lines):** Pure complex analysis using Mathlib's `Complex.norm_le_of_forall_mem_frontier_norm_le` (Maximum Modulus Principle) and `Differentiable.apply_eq_apply_of_bounded` (Liouville). No probability at all.
2. **Pillar C (`exists_entire_expTypeOne_of_memTw`) — medium (~200–300 lines):** You already have `paperSig2_factorial_moment_control` and `paperSig2_dynamics` in `foo.lean.txt`; you compute $\mathbb{E}[\langle e_I, \widehat{W}_t \rangle e^{\mu W_t^0}]$ by induction on $|I|$ and match against the monic Hermite polynomials $H_k(x; t) = \mathbb{E}[(x + i\sqrt{t} G)^k]$.
3. **Pillar A (`signatureTransformFinite_counterexampleU0`) — medium (~200 lines):** Define the discrete or continuous stopping time $\tau_R = \inf\{s \le t : |W_s^0| \ge R\}$, prove $\mathbb{E}[M_{t \wedge \tau_R}^{(\lambda)}] = 1$ via bounded Itô / Novikov (which you may already have in your repo's `ItoCalculusKit`), and take $R \to \infty$ by Fatou's lemma.
4. **Pillar B (`exists_scaled_survival_function`) — hardest (~400+ lines):** Needs Markov/independent increments of Brownian motion, Brownian scaling, Girsanov on the stopped process (for $dY = Y^2 dt + d\widetilde{B}$ up to $\tau_R$), and the two short ODE comparisons.

*(And if your actual paper/library goal is to ship a true Theorem B for option pricing rather than formalizing a 1,000-line counterexample to the paper's false Lemma 4.2(ii), keeping `riccatiOp_counterexampleU0` + `counterexampleRiccatiSol` + `ae_dualPairing_counterexampleU0_eq` as a documented witness in a comment/appendix and adding CSFT's integrability hypothesis to `affine_riccati_duality_mpr` is by far the fastest and cleanest path.)*
