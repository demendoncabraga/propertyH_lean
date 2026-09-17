import PropertyH
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let roots := #[``PropertyH.sphere_maps_eventually_degreeZero_coarse,
    ``PropertyH.not_hasPropertyH_of_containsCoarseExpanders,
    ``PropertyH.not_hasRationalPropertyH_of_containsCoarseExpanders,
    ``PropertyH.not_hasPropertyH_of_uniformlyContainsFiniteSup,
    ``PropertyH.uniformlyContainsFiniteSup_cZero,
    ``PropertyH.not_hasPropertyH_cZero,
    ``PropertyH.exists_group_not_coarsely_embeddable_in_propertyH,
    ``PropertyH.exists_coarse_normalization,
    ``PropertyH.ball_normalization_degreeZero,
    ``PropertyH.expander_poincare]
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if !"PropertyH".isPrefixOf mod.toString then continue
    let some ci := env.find? name | continue
    let deps := ci.type.getUsedConstants ++ (ci.value? true |>.map Expr.getUsedConstants |>.getD #[])
    todo := todo ++ deps
    rows := rows.push <| Json.mkObj [("name", toJson name.toString), ("module", toJson mod.toString),
      ("deps", toJson (deps.map Name.toString))]
  IO.println <| (Json.mkObj [("roots", toJson (roots.map Name.toString)),
    ("declarations", Json.arr rows)]).compress
