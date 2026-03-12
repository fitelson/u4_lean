# u4_lean

Formal verification in Lean 4 that Ulrich's candidate **u4** is not a single axiom for positive implication.

## Main Result

**Theorem** (`thm5_not_unifiable`): For all *i* >= 1, *j* >= 0, CD(T_i, T_j) is undefined.

**Corollary** (`Cpp_not_derivable`): *p* -> *p* is not derivable from u4 by condensed detachment.

This settles the last of Ulrich's four 15-symbol candidates, establishing that Meredith's 17-symbol axiom is the shortest single axiom for positive implication.

## The Axiom

u4 = ((X -> Y) -> Z) -> ((Y -> (Z -> U)) -> (Y -> U))

In Polish notation: `CCCabcCCbCcdCbd`

## Proof Structure

The CD closure of u4 is a single infinite chain T_0, T_1, T_2, ... defined by the recurrence:
- T_0 = u4, T_{n+1} = CD(u4, T_n)
- Key subterms: Y_0 = c, R_0 = C(C(b,C(c,d)),C(b,d)), Y_{n+1} = C(R_n, z), R_{n+1} = C(Y_n, z)

Every T_n has weight >= 15 (while *p* -> *p* has weight 3). The proof that no other CD pairs are productive proceeds by three cases, all resolved via weight contradictions:

- **Case A** (i >= 2, j = 0): direct weight contradiction
- **Case B** (i = 1, any j): weight contradiction in two subcases
- **Case C** (i >= 2, j >= 1): reduces to the **Cascade Lemma** -- a mutual induction showing sigma(Y_n) != C(sigma(R_n), t) and sigma(R_n) != C(sigma(Y_n), t) for all n, sigma, t

## Files

| File | Lines | Description |
|------|-------|-------------|
| `U4Lean.lean` | 440 | Complete proof: definitions, lemmas, and all cases |
| `Main.lean` | 9 | Executable that prints chain and verification matrix |

The proof uses **zero `sorry`** and has **no Mathlib dependency**.

## Building

Requires Lean 4.28.0-rc1 (specified in `lean-toolchain`).

```
lake build
```

## References

- B. Fitelson, "Resolving the Status of Ulrich's u4: A Condensed Detachment Analysis" (2026)
- B. Fitelson and N. Peltier, "Applying Saturation-Based Theorem Proving to Open Problems in Positive Implicational Logic", Journal of Automated Reasoning (to appear)
- C. Meredith, "A single axiom of positive logic", The Journal of Computing Systems, 1(3), 1953, pp. 169-170
