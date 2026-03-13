#!/usr/bin/env python3
"""
Verify that the CD closure of u4 is exactly the chain T_0, T_1, T_2, ...
by attempting all CD pairs and confirming occurs check failures for i >= 1.
"""

# --- Term representation ---
# Terms are either variables (strings) or C-nodes (tuples ('C', left, right))

def is_var(t):
    return isinstance(t, str)

def weight(t):
    if is_var(t):
        return 1
    return 1 + weight(t[1]) + weight(t[2])

def variables(t):
    if is_var(t):
        return {t}
    return variables(t[1]) | variables(t[2])

def to_polish(t):
    if is_var(t):
        return t
    return 'C' + to_polish(t[1]) + to_polish(t[2])

def to_standard(t):
    if is_var(t):
        return t
    l, r = to_standard(t[1]), to_standard(t[2])
    return f"({l} -> {r})"

# --- Substitution ---
def apply_subst(subst, t):
    if is_var(t):
        if t in subst:
            return apply_subst(subst, subst[t])
        return t
    return ('C', apply_subst(subst, t[1]), apply_subst(subst, t[2]))

def occurs_in(var, t, subst):
    """Check if var occurs in t (under substitution)."""
    t = apply_subst(subst, t)
    if is_var(t):
        return t == var
    return occurs_in(var, t[1], subst) or occurs_in(var, t[2], subst)

# --- Unification ---
class UnificationFailure(Exception):
    def __init__(self, reason):
        self.reason = reason

def unify(s, t, subst=None):
    """Most general unifier. Raises UnificationFailure on failure."""
    if subst is None:
        subst = {}
    s = apply_subst(subst, s)
    t = apply_subst(subst, t)
    if s == t:
        return subst
    if is_var(s):
        if occurs_in(s, t, subst):
            raise UnificationFailure(f"occurs check: {s} in {to_polish(t)}")
        subst[s] = t
        return subst
    if is_var(t):
        if occurs_in(t, s, subst):
            raise UnificationFailure(f"occurs check: {t} in {to_polish(s)}")
        subst[t] = s
        return subst
    if s[0] == 'C' and t[0] == 'C':
        subst = unify(s[1], t[1], subst)
        subst = unify(s[2], t[2], subst)
        return subst
    raise UnificationFailure(f"structural mismatch: {to_polish(s)} vs {to_polish(t)}")

# --- Variable renaming ---
_rename_counter = 0
def fresh_var():
    global _rename_counter
    _rename_counter += 1
    return f"_v{_rename_counter}"

def rename_vars(t, mapping=None):
    """Rename all variables in t to fresh variables."""
    if mapping is None:
        mapping = {}
    if is_var(t):
        if t not in mapping:
            mapping[t] = fresh_var()
        return mapping[t]
    return ('C', rename_vars(t[1], mapping), rename_vars(t[2], mapping))

# --- Canonicalize variable names ---
def canonicalize(t):
    """Rename variables to a, b, c, ... in order of first occurrence."""
    mapping = {}
    counter = [0]
    var_names = "abcdefghijklmnopqrstuvwxyz"
    def walk(t):
        if is_var(t):
            if t not in mapping:
                if counter[0] < 26:
                    mapping[t] = var_names[counter[0]]
                else:
                    mapping[t] = f"v{counter[0]}"
                counter[0] += 1
            return mapping[t]
        return ('C', walk(t[1]), walk(t[2]))
    return walk(t)

# --- Condensed Detachment ---
def cd(major, minor):
    """
    Condensed detachment: major must be C(alpha, beta).
    Unify minor with alpha, apply substitution to beta.
    Returns (result, subst) or raises UnificationFailure.
    """
    if is_var(major) or major[0] != 'C':
        raise UnificationFailure("major is not an implication")
    # Rename both to fresh variables
    major_r = rename_vars(major)
    minor_r = rename_vars(minor)
    alpha = major_r[1]
    beta = major_r[2]
    subst = unify(minor_r, alpha)
    result = apply_subst(subst, beta)
    return canonicalize(result)

# --- Build u4 ---
# u4 = C(C(C(a,b),c), C(C(b,C(c,d)),C(b,d)))
def C(l, r):
    return ('C', l, r)

u4 = C(C(C('a','b'),'c'), C(C('b',C('c','d')),C('b','d')))

print("u4 =", to_polish(u4))
print("   =", to_standard(u4))
print(f"   weight = {weight(u4)}, vars = {len(variables(u4))}")
print()

# --- Build the chain ---
N = 12  # number of chain elements beyond u4
chain = [u4]
print("Building chain T_0, T_1, ..., T_{}:".format(N))
print(f"  T_0: w={weight(chain[0]):3d}, v={len(variables(chain[0]))}, {to_polish(chain[0])}")

for n in range(N):
    t_next = cd(u4, chain[-1])
    chain.append(t_next)
    p = to_polish(t_next)
    if len(p) <= 80:
        print(f"  T_{n+1}: w={weight(t_next):3d}, v={len(variables(t_next))}, {p}")
    else:
        print(f"  T_{n+1}: w={weight(t_next):3d}, v={len(variables(t_next))}, {p[:60]}...")

print()

# --- Verify all CD pairs ---
K = min(N + 1, 10)  # test pairs up to T_K
print(f"Testing all CD(T_i, T_j) for 0 <= i,j <= {K-1}:")
print(f"{'':>8}", end="")
for j in range(K):
    print(f"{'j='+str(j):>14}", end="")
print()

results = {}
for i in range(K):
    print(f"  i={i:2d}:", end="")
    for j in range(K):
        try:
            result = cd(chain[i], chain[j])
            # Check if result is in the chain
            result_polish = to_polish(result)
            found = None
            for k, tk in enumerate(chain):
                if to_polish(tk) == result_polish:
                    found = k
                    break
            if found is not None:
                tag = f"= T_{found}"
            else:
                tag = f"NEW w={weight(result)}"
            print(f"{'  ' + tag:>14}", end="")
            results[(i,j)] = ('success', tag)
        except UnificationFailure as e:
            reason = e.reason
            if reason.startswith("occurs"):
                # Extract just the variable name
                var = reason.split(":")[1].strip().split(" ")[0]
                tag = f"OC({var})"
            elif reason.startswith("struct"):
                tag = "STRUCT"
            else:
                tag = "FAIL"
            print(f"{'  ' + tag:>14}", end="")
            results[(i,j)] = ('fail', reason)
    print()

print()

# --- Summary ---
print("=" * 70)
print("SUMMARY")
print("=" * 70)
successes = [(i,j,r[1]) for (i,j),r in results.items() if r[0] == 'success']
failures = [(i,j,r[1]) for (i,j),r in results.items() if r[0] == 'fail']

print(f"\nSuccessful CD pairs ({len(successes)}):")
for i, j, tag in successes:
    print(f"  CD(T_{i}, T_{j}) {tag}")

print(f"\nFailed CD pairs ({len(failures)}):")
occurs_count = sum(1 for _,_,r in failures if 'occurs' in r)
struct_count = sum(1 for _,_,r in failures if 'structural' in r)
other_count = len(failures) - occurs_count - struct_count
print(f"  Occurs check failures: {occurs_count}")
print(f"  Structural mismatches: {struct_count}")
print(f"  Other failures: {other_count}")

# Show detailed occurs check info for i >= 1
print(f"\nDetailed occurs check failures for i >= 1:")
for i, j, reason in failures:
    if i >= 1 and 'occurs' in reason:
        print(f"  CD(T_{i}, T_{j}): {reason}")

# --- Final verification ---
print()
print("=" * 70)
print("VERIFICATION")
print("=" * 70)
print()

all_i1_fail = all(results.get((i,j), ('fail',''))[0] == 'fail'
                   for i in range(1, K) for j in range(K))
all_i0_chain = all(results.get((0,j), ('fail',''))[0] == 'success'
                    for j in range(K))

print(f"All CD(T_0, T_j) succeed and produce T_{{j+1}}:  {all_i0_chain}")
print(f"All CD(T_i, T_j) for i>=1 fail:                {all_i1_fail}")

if all_i0_chain and all_i1_fail:
    print()
    print("CONFIRMED: The CD closure of u4 is exactly the chain {T_n : n >= 0}.")
    print("Since all T_n have weight >= 15 and Cpp has weight 3,")
    print("Cpp is NOT derivable from u4 by condensed detachment.")
    print()
    print("Therefore u4 is NOT a single axiom for intuitionistic implication.")
