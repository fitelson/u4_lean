# u4_lean

Formal verification in Lean 4 that Ulrich's candidate u4 is not a single axiom for positive implication.

## Main Result

Theorem 4.1 (`thm5_not_unifiable`): For all *i* >= 1 and *j* >= 0, CD(T_i, T_j) is undefined.

Corollary (`Cpp_not_instance`, `Cpp_not_derivable`): *p* -> *p* is not a substitution instance of any member of the condensed-detachment closure of u4.

This settles the last of Ulrich's four 15-symbol candidates, establishing that Meredith's 17-symbol axiom is the shortest single axiom for positive implication.

## The Axiom

u4 = ((X -> Y) -> Z) -> ((Y -> (Z -> U)) -> (Y -> U))

In Polish notation: `CCCabcCCbCcdCbd`

## Proof Structure

Up to variable renaming, the CD closure of u4 is a single infinite sequence T_0, T_1, T_2, ... defined by the recurrence:
- T_0 = u4, T_{n+1} = CD(u4, T_n)
- Key subterms: Y_0 = c, R_0 = C(C(b,C(c,d)),C(b,d)), Y_{n+1} = C(R_n, z), R_{n+1} = C(Y_n, z)

Every T_n has weight >= 15, and substitution does not decrease weight, while *p* -> *p* has weight 3. The proof that no other CD application is defined uses four exhaustive cases, grouped in the Lean source as follows:

- Case A (i >= 2, j = 0): direct weight contradiction
- Case B (i = 1, any j): weight contradiction in two subcases
- Case C (i >= 2, j >= 1): reduces to the mutually inductive shape lemmas showing sigma(Y_n) != C(sigma(R_n), t) and sigma(R_n) != C(sigma(Y_n), t) for all n, sigma, t

## Files

| File | Lines | Description |
|------|-------|-------------|
| `U4Lean.lean` | 476 | Complete proof: definitions, lemmas, and all cases |
| `Main.lean` | 8 | Executable that prints the sequence and verification matrix |
| `verify_u4.py` | 249 | Independent Python check of finite CD pairs |
| `u4.in` | 3 | TPTP input for the u4 problem |

The proof uses no `sorry` and has no Mathlib dependency.

## Building

Requires Lean 4.28.0-rc1 (specified in `lean-toolchain`).

```
lake build
```

## References

- B. Fitelson, "Completing the Search for the Shortest Single Axiom for Positive Implication" (2026)
- B. Fitelson and N. Peltier, "Applying Saturation-Based Theorem Proving to Open Problems in Positive Implicational Logic", Journal of Automated Reasoning 70(1), article 5 (2026), DOI 10.1007/s10817-026-09752-1
- C. Meredith, "A single axiom of positive logic", The Journal of Computing Systems, 1(3), 1953, pp. 169-170
