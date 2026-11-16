# Computational Companion: examples

Self-contained Python 3 scripts (standard library + numpy) that compute,
exactly or with stated error bounds, granular answers to problems that are
classically ill-posed, without object, or dependent on ad hoc
regularisation. Each script **asserts every claim it prints**, so it is a
test; `run_all.py` runs them all and exits non-zero on any failure.

    make examples            # or: python3 examples/run_all.py [-v]

The scripts are listed and discussed in the appendix
*Computational Companion* (`chapters/D-computational-companion.tex`).
The framework is a conservative extension: the classical theory is not
wrong; it lacks the object or the information that the granular theory keeps.

| Script | Classical problem | Granular resolution | Chapter |
|---|---|---|---|
| `01_openness.py` | Lebesgue cannot tell [a,b], [a,b), (a,b], (a,b) apart | exact μ and first moment; (μ, moment) recovers the interval (2 bits) | 3 |
| `02_countable.py` | ℚ∩[0,1] has measure 0, like ∅ | Farey set on N = M! has μ = \|F_M\|/M! > 0, shadow 0 | 3 |
| `03_random_integer.py` | no uniform law on ℕ | uniform on {1..H}, P(m \| X) = 1/m exactly, coprimality → 6/π² | 13 |
| `04_borel_kolmogorov.py` | conditioning on a null great circle is ill-posed | equator row, lune, tube: three exact conditional laws | 13 |
| `05_bertrand.py` | "random chord" is ill-posed | three finite spaces: 1/2, 1/3 − 1/(3M), 1/4 + O(ε) | 13 |
| `06_schwartz.py` | δ·δ undefined; Schwartz impossibility | δ_ε² = δ_ε/(2ε), x·pv = 1 − 2ε δ_ε, associativity kept | 6 |
| `07_ito_stratonovich.py` | ∫W dW depends on the sampling point | (ΔW)² = τ; Itô = (W²−T)/2, Strat = W²/2 exactly on every path | 15 |
| `08_differential_entropy.py` | h is unit-dependent and can be negative | H = h_ε − log₂(2ε) ≥ 0, unit-invariant (12.0 bits) | 16 |
| `09_zero_is_one_bit.py` | Lebesgue identifies ∅ and {0} | μ = 0 vs 2ε; registers, NULL, pruning masks, Landauer | 16 |
| `10_doubling_map.py` | float orbits of 2x mod 1 "artefactually" die | dyadic lattice: collapse in exactly K − v₂(k) steps; IEEE = K = 53 | 17 |
| `10b_cantor.py` | Cantor set uncountable but null; diagonal argument gives a cardinal, not a number | #C_K = 2^K, μ = (2/3)^K > 0 exactly, shadow 0; exact Cantor function; dust 4^K; a list of K strings misses exactly 2^K − #distinct ≥ 2^K − K | 12 |
| `10b_fractal_dimension.py` | box dimension may not exist; fitted estimates depend on the scaling range | exact counts N(3^j) = \|D\|^(K−j); dim_K = (a_K log 2 + c_K log 3)/(K log 3) definite at every K (oscillates 0.7540 / 0.8770); N(A×B) = N(A)N(B) | 12 |
| `10b_lsystem_exact.py` | float turtles drift; shared vertices disagree; contact needs a tolerance | Gaussian-integer L-system σ(v) = [round(p_j v/e) differences]: closes exactly at every depth; quadratic Koch = F+F−F−F+F; exact self-contact count | 12 |
| `11_cat_map_echo.py` | recurrence without bound; echo fails in floats | exact periods Π(N); exact integer Loschmidt echo | 17 |
| `12_peano.py` | ẋ = √\|x\|, x(0) = 0 non-unique | granular Euler is unique; one lattice step selects the branch | 8 |
| `13_self_energy.py` | self-energy of a point charge diverges | lattice Green's function finite, → W/6 = I₃/2 (Watson) | 7 |
| `13_walsh_chaos.py` | Wiener–Itô chaos is an infinite L² series | exact finite Walsh expansion = discrete multiple Itô sums; kernels → Wiener chaos at rate τ (m=1), √τ (m=2); W(T)² sharpness √(2Tτ) | 15 |
| `14_quantisability.py` | weight robustness as a Lebesgue volume | quantisability profile q(ε') as a count, Hoeffding CI, int8 bit flips | 3, 13 |
| `15_gibbs_paradox.py` | non-extensive mixing entropy; N! by hand | configurations are sets; N! is a theorem; ΔS ≤ ln(2N+1) | 20 |
| `15b_quantisability_toy.py` | robustness of a trained model as a volume of weights | exact solution-set counts on an int8 toy logit; quantisation algebra on lattice indices | 18 |
| `15b_transformer_lattice.py` | parameter spaces of networks as continua | exact parameter counts and bits of GPT-2/LLaMA lattices, symmetry orders, Occam radius | 18 |
| `16_no_paradoxical_decomposition.py` | Banach–Tarski, Hilbert's hotel | counting: no internal paradoxical decomposition | 3 |
| `17_isotropy_lorentz.py` | Lebesgue measure is rotation and Lorentz invariant; is the granular content? | exact first-order terms: rotation by arctan(3/4) costs 16ε/5, a boost with Doppler factor 2 costs 3ε; boost orbits are infinite (no-go) | 9, 20 |
| `17_periods_overflow.py` | periods of discretised chaos: random-map heuristics (√M, M²) | circular granulation: exact periods ord(2 mod d); x-rounded map overflows twice, half the horizon; cat map periods ≤ p+1; reversible maps ≥ N/2 cycles; cascade ≤ M/2+1, n_* ≈ 0.42 log₂ M | 17, 20 |
| `18_pesin_htheorem.py` | Pesin's formula only as t → ∞; H-theorem vs Loschmidt; rounded descent can cycle | H_t = min(t ln λ, 2 ln N) + O(1) for the cat map; #decrease = #increase exactly, Boltzmann bound K e^−Δ; symmetric rounded descent has periods 1, 2 | 17, 18, 20 |
| `19_lattice_atom.py` | hydrogen: Coulomb singularity, no position eigenstates, centre of mass only via Galilean invariance, collapse outside the dynamics | two point-spheres: exact two-body reduction, reduced mass at θ = 0, θ-dependent internal motion, unitary Cayley step, uniform Zeno bound, GRW energy per collapse → ħ²/(4 m r_C²) | 20 |
| `20_bell_decay.py` | Bell/Tsirelson on infinite spaces; exponential decay postulated against recurrence; no Lyapunov exponent for quantum chaos | CHSH local max 2 by enumeration, singlet 2√2, Tsirelson on ℂ^m⊗ℂ^n, no-signalling; exact survival #{τ ≥ t} = Σ(g_b − t)₊: linear for x ↦ x+1, near-geometric for x ↦ 5x mod p, exact 2^−t profile; recurrence t ≤ N^d; isometric many-body evolution, cubic Hartree field, Poisson vs GOE level ratios | 20 |
| `21_hilbert_axioms.py` | which of Hilbert's axioms makes the point dimensionless? | exact arithmetic in Q(e): groups I–IV hold, the chain (ie,0) never passes (1,0), n²e² < 1, the shadow identifies (0,0) and (e,0), the finite/infinite cut has no separating point, Pythagoras and medians transfer | 10 |

Script file numbers are not chapter numbers; the Chapter column gives the
printed chapter. Scripts named `10b_*.py` belong to the *Fractal Geometry*
chapter (Chapter 12), and scripts named `15b_*.py` to the *Learning Machines*
chapter (Chapter 18); `run_all.py` runs them as well (it discovers every `*.py`).
| `32_switchboard_n4_circuit.py` | is the small circuit for the 3-SAT switchboard on four variables correct? | 56 gates over AND, OR, NOT and 120 over AND, NOT (55 AND, 65 NOT), checked on all 2^32 switchboards | 19 |
| `33_granular_thresholds.py` | are the thresholds and counts of granular complexity right? | 272 cores (4 on one triple), deg P_SAT = 2^n C(n,3), least n with 8C(n,3) > 10^80, 8C(399,3) = 84059192, lattice counts | 19 |
