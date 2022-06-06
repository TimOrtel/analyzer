open Cil
open MyCFG
open CompareGlobals
include DetectRenamedFunctions
include CompareAST
include CompareCFG

let empty_change_info () : change_info = {added = []; removed = []; changed = []; unchanged = []}

let eq_glob (a: global) (b: global) (cfgs : (cfg * (cfg * cfg)) option) = match a, b with
  | GFun (f,_), GFun (g,_) ->
    let identical, unchangedHeader, diffOpt, _ = CompareGlobals.eqF f g cfgs StringMap.empty in

    identical, unchangedHeader, diffOpt
  | GVar (x, init_x, _), GVar (y, init_y, _) -> eq_varinfo x y (StringMap.empty, StringMap.empty) |> fst, false, None (* ignore the init_info - a changed init of a global will lead to a different start state *)
  | GVarDecl (x, _), GVarDecl (y, _) -> eq_varinfo x y (StringMap.empty, StringMap.empty) |> fst, false, None
  | _ -> ignore @@ Pretty.printf "Not comparable: %a and %a\n" Cil.d_global a Cil.d_global b; false, false, None

let compareCilFiles ?(eq=eq_glob) (oldAST: file) (newAST: file) =
  let cfgs = if GobConfig.get_string "incremental.compare" = "cfg"
    then Some (CfgTools.getCFG oldAST |> fst, CfgTools.getCFG newAST)
    else None in

  let addGlobal map global  =
    try
      let gid = identifier_of_global global in
      let gid_to_string gid = match gid.global_t with
        | Var -> "Var " ^ gid.name
        | Decl -> "Decl " ^ gid.name
        | Fun -> "Fun " ^ gid.name in
      if GlobalMap.mem gid map then failwith ("Duplicate global identifier: " ^ gid_to_string gid) else GlobalMap.add gid global map
    with
      Not_found -> map
  in

  let changes = empty_change_info () in
  global_typ_acc := [];
  let findChanges map global =
    try
      let isGFun = match global with
        | GFun _-> false (* set to true later to disable finding changes for funs*)
        | _ -> false
      in

      if not isGFun then
        let ident = identifier_of_global global in
        let old_global = GlobalMap.find ident map in
        (* Do a (recursive) equal comparison ignoring location information *)
        let identical, unchangedHeader, diff = eq old_global global cfgs in
        if identical
        then changes.unchanged <- {current = global; old = old_global} :: changes.unchanged
        else changes.changed <- {current = global; old = old_global; unchangedHeader; diff} :: changes.changed
    with Not_found -> () (* Global was no variable or function, it does not belong into the map *)
  in

  (* Store a map from functionNames in the old file to the function definition*)
  let oldMap = Cil.foldGlobals oldAST addGlobal GlobalMap.empty in

  let renameDetectionResults = DetectRenamedFunctionsRecursive.detectRenamedFunctions oldAST newAST in
  FundecMap.to_seq renameDetectionResults |>
  Seq.iter
    (fun (fundec, (functionGlobal, status)) ->
       Printf.printf "Function status of %s is=" fundec.svar.vname;
       match status with
       | Unchanged _ -> Printf.printf "Same Name\n";
       | Added -> Printf.printf "Added\n";
       | Removed -> Printf.printf "Removed\n";
       | Changed _ -> Printf.printf "Changed\n";
       | UnchangedButRenamed toFrom ->
         match toFrom with
         | GFun (f, _) -> Printf.printf "Renamed to %s\n" f.svar.vname;
         | _ -> Printf.printf "TODO";
    );

  (*  For each function in the new file, check whether a function with the same name
      already existed in the old version, and whether it is the same function. *)
  Cil.iterGlobals newAST
    (fun glob -> findChanges oldMap glob);

  let unchanged, changed, added, removed = FundecMap.fold (fun _ (global, status) (u, c, a, r) ->
      match status with
      | Unchanged now -> (u @ [{old=global; current=now}], c, a, r)
      | UnchangedButRenamed now -> (u @ [{old=global; current=now}], c, a, r)
      | Added -> (u, c, a @ [global], r)
      | Removed -> (u, c, a, r @ [global])
      | Changed (now, unchangedHeader) -> (u, c @ [{old=global; current=now; unchangedHeader=unchangedHeader; diff=None}], a, r)
    ) renameDetectionResults (changes.unchanged, changes.changed, changes.added, changes.removed)
  in

  changes.added <- added;
  changes.removed <- removed;
  changes.changed <- changed;
  changes.unchanged <- unchanged;

  changes

(** Given an (optional) equality function between [Cil.global]s, an old and a new [Cil.file], this function computes a [change_info],
    which describes which [global]s are changed, unchanged, removed and added.  *)
let compareCilFiles ?(eq=eq_glob) (oldAST: file) (newAST: file) =
  Stats.time "compareCilFiles" (compareCilFiles ~eq oldAST) newAST
