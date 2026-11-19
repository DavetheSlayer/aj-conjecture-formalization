import AJTwist.Knot.TwKKnot

/-!
# Braid words of the four families, for the checks outside Lean

Run from the folder `lean`, after `lake build`:

    lake env lean tools/TwWords.lean > ../scripts/four_families/lean_words.txt

Prints, for `(r, s) ∈ {(2,3), (2,5), (3,4), (3,5)}`, `-3 ≤ ℓ ≤ 3` and both clasp signs, the
number of strands and the braid word `twWhiteheadWord r s ℓ σ` (lines `W`) and its inverse
`invWord` (lines `I`), and for each pair the torus braid (`T`) and the word of Theorem T (`P`).
A letter `[i, 1]` is the positive generator `σ_i`, `[i, -1]` its inverse. The scripts
`scripts/four_families/tw_audit_*.py` read this output.
-/
open AJConjecture
def cases : List (Nat × Nat) := [(2,3),(2,5),(3,4),(3,5)]
def ells : List Int := [-3,-2,-1,0,1,2,3]
def showWord (w : BraidWord) : String :=
  "[" ++ ",".intercalate (w.map fun g => s!"[{g.1},{if g.2 then 1 else -1}]") ++ "]"
#eval do
  for (r,s) in cases do
    for l in ells do
      for (cl : Bool) in [true,false] do
        IO.println s!"W {r} {s} {l} {if cl then 1 else 0} {twStrands r s l} {showWord (twWhiteheadWord r s l cl)}"
        IO.println s!"I {r} {s} {l} {if cl then 1 else 0} {twStrands r s l} {showWord (invWord (twWhiteheadWord r s l cl))}"
    IO.println s!"T {r} {s} {r} {showWord (torusPairWord r s)}"
    IO.println s!"P {r} {s} {pairStrands r s} {showWord (pairWhiteheadWord r s)}"
