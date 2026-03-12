/-
  Formal verification of Theorem 5 from "Resolving the Status of Ulrich's u4"
  Part 1: Definitions and computational verification.
-/

-- Terms: variables (Nat) or implications
inductive Term where
  | var : Nat → Term
  | imp : Term → Term → Term
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Term

def weight : Term → Nat
  | var _ => 1
  | imp l r => 1 + weight l + weight r

def occurs (v : Nat) : Term → Bool
  | var n => n == v
  | imp l r => occurs v l || occurs v r

-- Count distinct variables
def varList : Term → List Nat
  | var n => [n]
  | imp l r => (varList l ++ varList r).eraseDups

def numVars (t : Term) : Nat := t.varList.length

-- Rename: shift all variable indices by offset
def shift (offset : Nat) : Term → Term
  | var n => var (n + offset)
  | imp l r => imp (shift offset l) (shift offset r)

-- Max variable index + 1 (for generating fresh offsets)
def maxVar : Term → Nat
  | var n => n + 1
  | imp l r => max (maxVar l) (maxVar r)

end Term

open Term

/-! ## The Y/R recurrence and chain T -/

mutual
def Y : Nat → Term
  | 0 => var 2
  | n + 1 => imp (R n) (var (n + 4))
def R : Nat → Term
  | 0 => imp (imp (var 1) (imp (var 2) (var 3))) (imp (var 1) (var 3))
  | n + 1 => imp (Y n) (var (n + 4))
end

def T : Nat → Term
  | 0 => imp (imp (imp (var 0) (var 1)) (var 2))
             (imp (imp (var 1) (imp (var 2) (var 3))) (imp (var 1) (var 3)))
  | n + 1 => imp (imp (Y n) (imp (R n) (var (n + 4))))
                 (imp (Y n) (var (n + 4)))

/-! ## Substitution (association list) -/

abbrev Subst := List (Nat × Term)

namespace Subst

def lookup (σ : Subst) (v : Nat) : Option Term :=
  match σ with
  | [] => none
  | (n, t) :: rest => if n == v then some t else lookup rest v

end Subst

/-! ## Apply substitution (chase bindings) -/

def Term.applySFuel (σ : Subst) (fuel : Nat) : Term → Term
  | var n => match fuel, σ.lookup n with
    | fuel' + 1, some t => t.applySFuel σ fuel'
    | _, _ => var n
  | imp l r => imp (l.applySFuel σ fuel) (r.applySFuel σ fuel)

-- Occurs check under substitution
def Term.occursInS (σ : Subst) (v : Nat) (fuel : Nat) : Term → Bool
  | var n => if n == v then true
    else match fuel, σ.lookup n with
      | fuel' + 1, some t => t.occursInS σ v fuel'
      | _, _ => false
  | imp l r => l.occursInS σ v fuel || r.occursInS σ v fuel

/-! ## Unification with occurs check (worklist, fuel-based) -/

/-- Unify a list of equation pairs under substitution σ.
    Returns the mgu or none (occurs check / structural failure). -/
def unifyWorklist (eqs : List (Term × Term)) (σ : Subst) (fuel : Nat) :
    Option Subst :=
  match fuel with
  | 0 => none  -- out of fuel
  | fuel' + 1 =>
    match eqs with
    | [] => some σ
    | (s, t) :: rest =>
      -- Apply current substitution
      let s' := s.applySFuel σ (fuel' + 1)
      let t' := t.applySFuel σ (fuel' + 1)
      if s' == t' then unifyWorklist rest σ fuel'
      else match s', t' with
        | var v, t'' =>
          if t''.occursInS σ v (fuel' + 1) then none  -- occurs check
          else unifyWorklist rest ((v, t'') :: σ) fuel'
        | s'', var v =>
          if s''.occursInS σ v (fuel' + 1) then none  -- occurs check
          else unifyWorklist rest ((v, s'') :: σ) fuel'
        | imp l1 r1, imp l2 r2 =>
          unifyWorklist ((l1, l2) :: (r1, r2) :: rest) σ fuel'

def unify (s t : Term) (fuel : Nat := 1000) : Option Subst :=
  unifyWorklist [(s, t)] [] fuel

/-! ## Condensed detachment -/

/-- CD(major, minor): major must be imp(α, β).
    Rename to disjoint vars, unify minor with α, return σ(β). -/
def cd (major minor : Term) (fuel : Nat := 1000) : Option Term :=
  match major with
  | var _ => none
  | imp α β =>
    let offset := max major.maxVar minor.maxVar
    -- Rename major variables by shifting
    let α' := α.shift offset
    let β' := β.shift offset
    match unify minor α' fuel with
    | none => none
    | some σ => some (β'.applySFuel σ (fuel + 1))

/-! ## Canonical renaming (for comparison) -/

private def enumerate (l : List Nat) : List (Nat × Nat) :=
  let rec go (l : List Nat) (i : Nat) : List (Nat × Nat) :=
    match l with
    | [] => []
    | x :: xs => (x, i) :: go xs (i + 1)
  go l 0

def Term.canonicalize (t : Term) : Term :=
  let vars := t.varList
  let mapping := enumerate vars
  let rec rename (mapping : List (Nat × Nat)) : Term → Term
    | var n => var (match mapping.find? (fun p => p.1 == n) with
        | some (_, i) => i | none => n)
    | imp l r => imp (rename mapping l) (rename mapping r)
  rename mapping t

/-! ## Computational verification -/

/-- Check CD(T i, T j): return a string describing the result -/
def checkCD (i j : Nat) : String :=
  match cd (T i) (T j) with
  | none => "FAIL"
  | some result =>
    let rc := result.canonicalize
    -- Check if it matches some T k
    let rec findMatch (k : Nat) (limit : Nat) : String :=
      match limit with
      | 0 => s!"NEW(w={rc.weight})"
      | limit' + 1 =>
        if (T k).canonicalize == rc then s!"T_{k}"
        else findMatch (k + 1) limit'
    findMatch 0 30

/-- Print the full CD matrix for 0 ≤ i,j ≤ bound -/
def printMatrix (bound : Nat) : IO Unit := do
  for i in List.range (bound + 1) do
    let mut row := s!"i={i}: "
    for j in List.range (bound + 1) do
      row := row ++ s!"{checkCD i j}  "
    IO.println row

/-- Verify Theorem 5 computationally for 0 ≤ i,j ≤ bound -/
def verifyThm5 (bound : Nat) : Bool :=
  let pairs := (List.range (bound + 1)).flatMap fun i =>
    (List.range (bound + 1)).map fun j => (i, j)
  pairs.all fun (i, j) =>
    if i == 0 then true  -- row 0 produces the chain (not part of Thm 5)
    else (cd (T i) (T j)).isNone

#eval printMatrix 6
#eval verifyThm5 10   -- should be true
#eval verifyThm5 15   -- should be true

-- Weight sanity checks
#eval (T 0).weight  -- 15
#eval (T 1).weight  -- 17
#eval (T 2).weight  -- 31
#eval (T 3).weight  -- 29
