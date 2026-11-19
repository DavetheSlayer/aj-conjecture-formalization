import AJHandoff
import Solution
import AJHandoff.Geometry.GeoZhVerbatim
import AJHandoff.TorusKnot.PairKWhDMain
import AJHandoff.TorusKnot.PairKWhDBandTorus
import AJHandoff.TorusKnot.PairKJonesTwoNe
import AJHandoff.TorusKnot.PairKMirrorRobust
import AJHandoff.TorusKnot.PairKMarkCalib

/-!
# Hypothesis audit for the v1 release

Run from the folder `lean`, after `lake build`:

    lake env lean tools/AuditReach.lean

For each group of root theorems it follows every constant occurring in the types and in the
proof terms (theorem bodies included) and reports which of the watched premises are reached. The
core, bridge and MARK groups must reach only `MarkovEquiv` (the relation named in the distinctness conclusion); the
four-family group (the theorem of the handoff of 18 November 2026, which makes no distinctness
claim) must reach none of them; the control groups show that the tool detects a premise when it is
used. Recorded output: `docs/V1_SCOPE.md`, Section 2, and `docs/FOUR_FAMILIES.md` for the four-family group.
-/
open Lean Meta Elab Command

/-- All constants reachable from `roots` through types and values. -/
partial def reach (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let deps := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[])
      for d in deps do
        if !seen.contains d then stack := d :: stack
  return seen

elab "#audit_reach" : command => do
  let env ← getEnv
  let groups : List (String × List Name) := [
    ("CORE", [`AJConjecture.theoremT, `AJConjecture.theoremF,
      `AJConjecture.minimalRecurrence_whiteheadTorusKnot,
      `AJConjecture.isRecurrencePolynomial_whiteheadTorusKnot_one,
      `AJConjecture.aPolynomial_pair_associated_famBound,
      `AJConjecture.not_ajSquareFreeConjecture,
      `AJConjecture.release_theoremT, `AJConjecture.release_classicalEquality,
      `AJConjecture.release_minimalRecurrence, `AJConjecture.release_pairWord_two]),
    ("BRIDGE", [`AJConjecture.pairWhiteheadKnot_whDouble, `AJConjecture.whiteheadTorusKnot_whDouble,
      `AJConjecture.morseReach_whDouble, `AJConjecture.bandLinkings_whBand_braidLongDiagram,
      `AJConjecture.coloredJones_two_pairWhiteheadKnot_ne]),
    ("MARK", [`AJConjecture.not_ajSquareFree_mirror_pair,
      `AJConjecture.isCoprime_extraFactorMirror_pair, `AJConjecture.commute_meridian_longitude,
      `AJConjecture.map_longitude_eq_one_of_commGroup, `AJConjecture.coloredJones_two_trefoil,
      `AJConjecture.eigenvalueSet_trefoil_subset, `AJConjecture.mem_eigenvalueSet_trefoil,
      `AJConjecture.longitude_mul_meridian_pow_torusPairKnot]),
    ("FOUR_FAMILIES", [`AJConjecture.theoremFourFamilies,
      `AJConjecture.release_theoremFourFamilies, `AJConjecture.release_fourFamilies_coloredJones,
      `AJConjecture.isBandClasp_twWhiteheadKnot, `AJConjecture.twH_exists_annihilator]),
    ("CONTROL_ZHENG", [`AJConjecture.geo_phys_of_zhengVerbatim]),
    ("CONTROL_JSJ", [`AJConjecture.pairWhiteheadKnot_not_markovEquiv_of_jsj]),
    ("CONTROL_G", [`AJConjecture.geo_theoremG])]
  let watch : List Name := [`AJConjecture.ZhengEstimates, `AJConjecture.ZhengVerbatim,
    `AJConjecture.ZhengEq512, `AJConjecture.WhiteheadJSJProp, `AJConjecture.WhiteheadGluing,
    `AJConjecture.WhiteheadComplete, `AJConjecture.whiteheadPeripheral, `AJConjecture.blochWigner,
    `AJConjecture.geoHypMeasure, `AJConjecture.GeoTillmannGroup, `AJConjecture.geoShapeRep,
    `AJConjecture.geo_theoremG, `AJConjecture.MarkovEquiv, `sorryAx]
  for (g, roots) in groups do
    let s := reach env roots
    let hits := watch.filter s.contains
    logInfo m!"{g}: {s.size} constants; watched premises reached: {hits}"
#audit_reach
