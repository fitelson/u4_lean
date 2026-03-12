import U4Lean

def main : IO Unit := do
  IO.println "u4 formal verification"
  IO.println s!"T 0 weight: {(T 0).weight}"
  IO.println s!"T 1 weight: {(T 1).weight}"
  printMatrix 6
  IO.println s!"All CD(T_i, T_j) fail for 1 ≤ i,j ≤ 20: {verifyThm5 20}"
