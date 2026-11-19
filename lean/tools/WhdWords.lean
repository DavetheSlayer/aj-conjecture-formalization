import AJHandoff.TorusKnot.PairKKnot
import AJHandoff.TorusKnot.PairKTargetWord
import AJHandoff.TorusKnot.PairKWhDMain
import AJFamily.Skein.TorusWord
import AJFamily.Skein.TorusTargetWord

/-!
# Input for `scripts/whitehead_double/check_whd_manuscript.py`

Run from the Lean project directory: `lake env lean tools/WhdWords.lean > words.txt`.

* The `#eval` lines print the braid words of the library, so that the script tests the words the
  theorems are about and not a transcription of them.
* The two `example`s check that the diagram `whDouble (trefoil)` reached by the current braid
  for `(r, s) = (2, 3)` is, letter for letter, the 28-letter target word
  `witnessTargetWord` of the earlier single-witness library (the version accepted by the
  comparator), which the braid printed in the source manuscript was proved to reach.
-/

open AJConjecture

#eval s!"PW 2 3 {pairWhiteheadWord 2 3}"
#eval s!"PW 2 5 {pairWhiteheadWord 2 5}"
#eval s!"PW 2 7 {pairWhiteheadWord 2 7}"
#eval s!"PW 3 4 {pairWhiteheadWord 3 4}"
#eval s!"PW 3 5 {pairWhiteheadWord 3 5}"
#eval s!"PW 4 5 {pairWhiteheadWord 4 5}"
#eval s!"WT 1 {whiteheadTorusWord 1}"
#eval s!"WT 2 {whiteheadTorusWord 2}"
#eval s!"TP 2 3 {torusPairWord 2 3}"
#eval s!"TP 3 4 {torusPairWord 3 4}"

/-- `witnessTargetWord` of the earlier library (`AJConjecture/SkeinIsoWitnessWords.lean`). -/
def oldWitnessTargetWord : MorseWord :=
  [(.cup, 1), (.cup, 2), (.cup, 3), (.cross true, 1), (.cross true, 2), (.cross true, 0),
   (.cross true, 1), (.cross true, 1), (.cross true, 2), (.cross true, 0), (.cross true, 1),
   (.cross true, 1), (.cross true, 2), (.cross true, 0), (.cross true, 1), (.cap, 3), (.cap, 2),
   (.cross false, 0), (.cross false, 0), (.cross false, 0), (.cross false, 0),
   (.cross false, 0), (.cross false, 0), (.cup, 2), (.cross true, 1), (.cross true, 1),
   (.cap, 0), (.cap, 1)]

example : pairTargetWord 2 3 = oldWitnessTargetWord := by decide
example : torusTargetWord 1 = oldWitnessTargetWord := by decide
