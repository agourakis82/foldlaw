# foldlaw — zero-divisor dimension theory of the Cayley–Dickson tower, machine-checked

Lean 4 formalisation of the anti-associator kernel `W(x,y) a = (x a) y + x (a y)` on the
real Cayley–Dickson tower, culminating in a closed per-pair formula (the *birth function*)
for `dim ker W(e_a, e_b)` over all pairs of distinct imaginary basis units at every level,
and the corresponding annihilator dimension of `z = e_a + e_b ℓ`.

## Pinned environment

| item | value |
|---|---|
| Lean | `leanprover/lean4:v4.35.0-rc3` (`lean-toolchain`) |
| Mathlib | git rev `738e62bd6df530a89ac01b20e937ad70923a7b96` (`lake-manifest.json`) |
| axioms used (every sealed theorem) | `propext`, `Classical.choice`, `Quot.sound` |
| `sorry` | none (`sorryAx` absent from every `#print axioms`) |

Build and seal:

```sh
lake build            # builds Foldlaw and Foldlaw.Birth; prints every #print axioms line
```

## Conventions

* `CD : ℕ → Type`, `CD 0 = ℝ`, `CD (n+1) = CD n × CD n` written `dbl x y` for `x + y ℓ`.
* Conjugation `conj (dbl x y) = dbl (conj x) (neg y)`.
* **Multiplication (code convention, fixed throughout):**

  `(x, y) · (a, b) = (x a − b ȳ,  x̄ b + a y)`.

  The literature uses several equivalent doublings differing in where the conjugates
  sit; they give isomorphic algebras, so all dimension statements are convention-free.
  The explicit sign tables in `Foldlaw/Birth.lean` (`key_*`, `class_*`) are specific to ours.
* Basis units are indexed by `BUnit m` (bit strings: `lower` = bit 0, `upper` = bit 1 at
  each doubling), evaluated by `beval : BUnit m → CD m`; `bone m` is the unit `1`;
  `bxor` is the index of `±(e_a e_b)`.
* `W(x,y) = WA x y : CD m →ₗ[ℝ] CD m` is `(x a) y + x (a y)`; `WT x y` is the same map one
  level up for the lifted pair `(x,0), (y,0)`; `CA x y` is the complementary block.

## Main results (all in namespace `Foldlaw`)

### `Foldlaw.lean` — the fold law (formalises Biss–Dugger–Isaksen 2005, Lemma 8.9 and Prop. 11.1, for basis units)

| theorem | statement |
|---|---|
| `finrank_cd` | `finrank (CD m) = 2^m` |
| `ker_Lz_iff_ker_W` | `(x,y)·(a,b) = 0 ↔ b = (x a) y ∧ W(x,y) a = 0` (under unit art of `x`, `y`) |
| `W_block`, `ker_WT_iff` | `W_T(a₀ + a₁ℓ) = W_A(a₀) + C(a₁)ℓ` — diagonal blocks across a doubling |
| `finrank_ker_CA` | `dim ker C = 4 + dim ker W` for distinct imaginary basis units |
| `finrank_ker_WT_fold` | `dim ker W_{m+1}((x,0),(y,0)) = 2 · dim ker W_m(x,y) + 4` (the fold law) |
| `finrank_ker_WT_octonion`, `finrank_ker_WT_sedenion` | closed numerals `4` and `12` |

### `Foldlaw/Birth.lean` — the birth function

| theorem | statement |
|---|---|
| `finrank_ker_WA_eq_N` | `dim ker W(e_a,e_b) = #{r : (e_a e_r) e_b = −e_a (e_r e_b)}` (count of anti-associating triples) |
| `N_LL`, `N_UU_gen` | `((a,0),(b,0))`, `((0,a),(0,b))` with `a,b ≠ 1` distinct: `2N + 4` |
| `N_LU_gen` | `((a,0),(0,b))`, `b ∉ {1,a}`: `N' + 2N + 4 = 2^{n+1}` |
| `N_LU_bone`, `N_LU_self`, `N_UU_bone` | `((a,0),(0,1))`, `((a,0),(0,a))`, `((0,1),(0,b))`: `N' + 4 = 2^{n+1}` (the maximum) |
| `N_symm` | symmetry in the two slots |
| `birth` | the computable recursion on bit strings implementing the six cases |
| **`finrank_ker_WA_birth`** | **`dim ker W(e_a,e_b) = birth a b`** for all distinct imaginary `a, b`, every level |
| `finrank_ker_WA_birth'` | element form (hypotheses `BasisUnit x`, `conj x = −x`, …) |
| `birth_props` | `birth ≡ 0 (mod 4)` and `birth + 4 ≤ 2^m` |
| `birth_mod_eight` | from level 3 on, `birth ≡ 4 (mod 8)`: every value is `4·(odd)` |
| **`finrank_ann_birth`** | **`dim ker L_{e_a + e_b ℓ} = birth a b`** at level `m+1` (annihilator dimension) |
| `exists_annihilator` | at every level `≥ 4`, `e_a + e_b ℓ` is a zero divisor |
| **`birth_closed`** | **closed form**: `birth a b = 2^(m−1) + T_m`, `T_(J+1) = 2^J − 4`, `T_k = σ_(k−1)(2T_(k−1)+4)`, `J = max lsb(a, b, a xor b)`, `σ` from the bits of `a xor b` (`lsbB`, `Jlev`, `Tclosed`) |
| **`birth_four_lifts`** | **four-lift sum rule**: for distinct imaginary `a, b` at level `n`, `birth` of the four lifts `((a,0),(b,0)), ((a,0),(0,b)), ((0,a),(b,0)), ((0,a),(0,b))` sums to `2^(n+2)` — `birth a b` cancels |
| **`birthTotal_succ`** | **total**: `Σ birth` over ordered distinct imaginary pairs at level `n+1` satisfies `S + 28·2^n = 4·8^n + 24`, i.e. `S = 4(2^n+3)(2^n−1)(2^n−2)`; no dependence on the level-`n` total. Edge count of the Zhilina graph: 168, 1848, 15960, 130200, 1046808, … |
| `birthHistogram` | computable census; `#eval birthHistogram 6` reproduces the exhaustive 128-census bin by bin |
| `birthSpectrum`, `spectrumCheck` | closed form of the whole histogram: `H_m(k) = 21·2^(m−3) + Σ_{j=3}^{m−2} 3·2^(m−j−1)(2^j−1)·[k in the 2^(m−j−2) lowest or highest bins] + 3(2^(m−1)−1)·[top bin]`; proved on paper (uniform count by `J` and pattern; bin dynamics "append 1 / complement, append 0"), `spectrumCheck m = true` for `m = 3..8`; **not a theorem** (sealing it is the first item of further work) |
| `birthClosed`, `closedCheck` | integer-indexed reading of the closed form; `#eval closedCheck m` compares it with `birth` on every pair (true through `m = 8`); not a theorem |
| `zhilina_degree_eq_birth` | degree of the vertex `±(e_a + τ e_b ℓ)` in the two-sided zero-divisor graph on doubly pure unit-pair lines `= birth a b` (with `ann_two_sided`, `ann_char`, `ann_line_unique`, `line_inj`, `line_ne_neg`, `annLine_bilateral`, `lineElem_sq_ne_zero`) |

## Literature position (honest)

* The fold law and the annihilator reduction are Biss–Dugger–Isaksen, *Large annihilators in
  Cayley–Dickson algebras* (Comm. Algebra 2008; arXiv math/0511691), Lemma 8.9 and Prop. 11.1;
  Lemmas 8.7–8.10 give the `LL` and `LU` embeddings; Prop. 8.11 is an existence statement
  for the values `≡ 4 (mod 8)`.
* Zhilina, *Orthogonality graphs of real Cayley–Dickson algebras II* (Internat. J. Algebra
  Comput. 31, 2021, DOI 10.1142/S0218196721500338; graph defined in Part I, DOI ...0326)
  proves the special-vertex degree `2^n − 4` and divisibility by 4 for the rest.
* New here, as far as the 2026-10-02 literature check reaches: the three remaining cases
  (`N_LU_bone`, `N_LU_self`, `N_UU_bone`), the closed per-pair function `birth`, the
  anti-associating-triple reformulation `finrank_ker_WA_eq_N`, the mod-8 law as a per-pair
  theorem, and the formalisation itself.
