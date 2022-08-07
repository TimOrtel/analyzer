open DetectRenamedFunctions
open Cil
open CilMaps
include CompareAST
include CompareCFG

(*(oldVarinfo, newName, unchangedHeader)*)
type renameAssumption = globalElem * string * bool

let show (renameAssumption: renameAssumption): string =
  let (v, n, _) = renameAssumption in
  globalElemName v ^ " -> " ^ n

module OrderedRenameAssumption = struct
  type t = renameAssumption

  (*x.svar.uid cannot be used, as they may overlap between old and now AST*)
  let compare (from1, to1, _) (from2, to2, _) =
    let fromCompare = String.compare (globalElemName from1) (globalElemName from2) in
    if fromCompare = 0 then String.compare to1 to2
    else fromCompare
end

module RenameAssumptionSet = Set.Make(OrderedRenameAssumption)

module RenameAssumptionMap = Map.Make(OrderedRenameAssumption)

type fQueue = renameAssumption list * RenameAssumptionSet.t

let enqueue: renameAssumption -> fQueue -> fQueue = fun e (keys, map) ->
  if RenameAssumptionSet.mem e map then (keys, map)
  else (keys @ [e], RenameAssumptionSet.add e map)

(*eList must be free of duplicates*)
let enqueueAll: renameAssumption list -> fQueue -> fQueue = fun eList (keys, map) ->
  let toAdd = List.filter (fun e -> not (RenameAssumptionSet.mem e map)) eList in
  (keys @ toAdd, RenameAssumptionSet.add_seq (List.to_seq toAdd) map)

let dequeue: fQueue -> renameAssumption * fQueue = fun (keys, map) ->
  let removedElem = List.hd keys in
  removedElem, (List.tl keys, RenameAssumptionSet.remove removedElem map)

let dequeueElem: renameAssumption -> fQueue -> fQueue = fun assumptionToRemove (keys, map) ->
  List.filter (fun e -> e <> assumptionToRemove) keys, RenameAssumptionSet.remove assumptionToRemove map

let filterElems = fun f (keys, map) -> List.filter f keys, RenameAssumptionSet.filter f map

let empty : fQueue = [], RenameAssumptionSet.empty

let isEmpty: fQueue -> bool = fun (keys, _) -> List.length keys = 0

let length: fQueue -> int = fun (keys, _) -> List.length keys

type extendedCarryType = {
  basicCarryData: carryType;
  assumptionQueue: fQueue;
  dependentsMap: renameAssumption list RenameAssumptionMap.t;
  assumptions: RenameAssumptionSet.t;
}

let modifyBasicCarryData modification data =
  {
    basicCarryData=modification data.basicCarryData;
    assumptionQueue=data.assumptionQueue;
    dependentsMap=data.dependentsMap;
    assumptions=data.assumptions;
  }

(*Enqueues the assumptions that do not exists and adds them to the list of all assumptions*)
let enqueueAssumptions assumptions data = {
  basicCarryData=data.basicCarryData;
  assumptionQueue=enqueueAll assumptions data.assumptionQueue;
  dependentsMap=data.dependentsMap;
  assumptions=RenameAssumptionSet.add_seq (List.to_seq assumptions) data.assumptions;
}

let dequeueAssumption assumption data = {
  basicCarryData=data.basicCarryData;
  assumptionQueue=dequeueElem assumption data.assumptionQueue;
  dependentsMap=data.dependentsMap;
  assumptions=data.assumptions;
}

let dequeueAssumptions (assumptions: (globalElem * string) list) data = {
  basicCarryData=data.basicCarryData;
  assumptionQueue=filterElems (fun (v, n, _) -> not (List.mem (v, n) assumptions)) data.assumptionQueue;
  dependentsMap=data.dependentsMap;
  assumptions=RenameAssumptionSet.filter (fun (v, n, _) -> not (List.mem (v, n) assumptions)) data.assumptions;
}

let dequeueFirstAssumption data =
  let elem, newQueue = dequeue data.assumptionQueue in
  elem, {
    basicCarryData=data.basicCarryData;
    assumptionQueue=newQueue;
    dependentsMap=data.dependentsMap;
    assumptions=data.assumptions;
  }

let removeInvalidAssumption (invalidAssumption: renameAssumption) data =
  (*let (a, b, _) = invalidAssumption in*)
  (*Printf.printf "Removing invalid assumption: %s -> %s\n" (a.vname) b;*)
  {
    basicCarryData=data.basicCarryData;
    assumptionQueue=data.assumptionQueue;
    dependentsMap=data.dependentsMap;
    assumptions=RenameAssumptionSet.remove invalidAssumption data.assumptions;
  }

let registerDependencies (dependencies: renameAssumption list) (dependent: renameAssumption) data =
  let newDependentsMap = List.fold_left (fun dependentsMap dependency ->
      let presentDependents: renameAssumption list = Option.value ~default:[] (RenameAssumptionMap.find_opt dependency dependentsMap) in

      RenameAssumptionMap.add dependency (dependent::presentDependents) dependentsMap
    ) data.dependentsMap dependencies in

  {
    basicCarryData=data.basicCarryData;
    assumptionQueue=data.assumptionQueue;
    dependentsMap=newDependentsMap;
    assumptions=data.assumptions;
  }

let clearDependents dependency data = {
  basicCarryData=data.basicCarryData;
  assumptionQueue=data.assumptionQueue;
  dependentsMap=RenameAssumptionMap.remove dependency data.dependentsMap;
  assumptions=data.assumptions;
}

let emptyExtendedCarryType = {
  basicCarryData=emptyCarryType;
  assumptionQueue=empty;
  dependentsMap=RenameAssumptionMap.empty;
  assumptions=RenameAssumptionSet.empty;
}


(*Marks the function status for the wrong assumptions as Modified/Created/Deleted. Removes the wrong assumption for the assumption queue.
   Then recursivly calls this function on all dependents of the wrong assumption.*)
let rec propagateWrongRenameAssumption (oldFunctionMap: f StringMap.t) (nowFunctionMap: f StringMap.t) (oldGVarMap: v StringMap.t) (nowGVarMap: v StringMap.t) (wrongAssumption: renameAssumption) (data: extendedCarryType) =
  let (oldG, nowName, unchangedHeader) = wrongAssumption in

  let dependents = Option.value ~default:[] (RenameAssumptionMap.find_opt wrongAssumption data.dependentsMap) in

  (*let _ = Printf.printf "Wrong: %s -> %s; dependents: %s\n" oldVarinfo.vname nowName ([%show: (string * string) list] (List.map (fun (a, b, _) -> a.vname, b) dependents)) in*)

  let hasStatus = GlobalElemMap.mem oldG data.basicCarryData.statusForOldElem in
  if hasStatus then removeInvalidAssumption wrongAssumption data
  else (
    let nowG, isFun = match oldG with
      | Fundec _ -> (
          let (nowF, _) = StringMap.find nowName nowFunctionMap in
          Fundec(nowF), true
        )
      | GlobalVar _ -> (
          let (nowG, _, _) = StringMap.find nowName nowGVarMap in
          GlobalVar nowG, false
        ) in

    (*Mark the assumption as changed or added/removed*)
    let dataWithAssumption = if globalElemName oldG = nowName then
        modifyBasicCarryData (fun d ->
            registerStatusForOldF oldG (Modified(nowG, unchangedHeader)) d |>
            registerStatusForNowF nowG (Modified(oldG, unchangedHeader))
          ) data
      else
        match (StringMap.find_opt nowName nowFunctionMap) with
        | Some ((nowF, _)) -> modifyBasicCarryData (fun d ->
            registerStatusForOldF oldG Deleted d |>
            registerStatusForNowF nowG Created
          ) data
        | None -> modifyBasicCarryData (registerStatusForOldF oldG Deleted) data
    in

    let updatedData = dequeueAssumption wrongAssumption dataWithAssumption |>
                      removeInvalidAssumption wrongAssumption
    in

    (*Get all other assumptions that rely on this varinfo*)
    let otherAssumptions = RenameAssumptionSet.filter (fun (v, _, _) -> globalElemName v = globalElemName oldG) updatedData.assumptions |>
                           RenameAssumptionSet.to_seq in

    (*Only propagate changes when names differ, because that means addition/removal.*)
    (*If the names are the same, a wrong assumption only means a change, if both function still exist.*)
    if globalElemName oldG <> nowName || (not (StringMap.mem nowName nowFunctionMap) && isFun) || (not (StringMap.mem nowName nowFunctionMap) && not isFun) then
      Seq.fold_left (fun data dependent ->
          propagateWrongRenameAssumption oldFunctionMap nowFunctionMap oldGVarMap nowGVarMap dependent data
        ) updatedData (Seq.append (List.to_seq dependents) otherAssumptions)
    else
      (*let _ = Printf.printf "Skipping!\n" in*)
      updatedData
  )

let hasCyclicDependency (parent: fundec * string) (dependencyList: (fundec * string) list) (data: extendedCarryType) : bool * (fundec * string) list =
  let isAssumptionInList (assumption: fundec * string) (list: (fundec * string) list) : bool =
    let (av, an) = assumption in
    List.exists (fun (v, n) -> v.svar.vname = av.svar.vname && n = an) list
  in

  (*let (pf, pn) = parent in

  Printf.printf "cyclic: \n";
  Printf.printf "parent: %s -> %s\n" pf.svar.vname pn;
  Printf.printf "dependencies %s\n" (String.concat "," (List.map (fun (a, b) -> a.svar.vname ^ " -> " ^ b) dependencyList));*)

  if isAssumptionInList parent dependencyList then true, []
  else (
    let rec find_dependency_in_graph (dep: fundec * string) (visitedAssumptions: (fundec * string) list) : bool * (fundec * string) list =
      match RenameAssumptionMap.find_opt (Fundec (fst dep), snd dep, false) data.dependentsMap with
      | Some dependentsList -> (
          List.fold_left (fun (recDepFound, carriedVisitedAssumptions) assumption ->
              (*Quick skip*)
              if recDepFound || isAssumptionInList assumption carriedVisitedAssumptions then (recDepFound, carriedVisitedAssumptions)
              else
                let isThisARecDep: bool = isAssumptionInList assumption dependencyList in
                if isThisARecDep then
                  (*Rec dep found. Backtrack.*)
                  (true, carriedVisitedAssumptions)
                else (
                  find_dependency_in_graph assumption (assumption::carriedVisitedAssumptions)
                )
            ) (false, visitedAssumptions) dependencyList
        )
      | None -> false, visitedAssumptions
    in

    find_dependency_in_graph parent []
  )

let rec resolveDependencies (oldFunctionMap: f StringMap.t) (nowFunctionMap: f StringMap.t) oldGVarMap nowGVarMap (data: extendedCarryType) =
  if isEmpty data.assumptionQueue then data
  else
    (*
    let _ = Printf.printf "\nresolveDependencies: \n" in
    let _ = Printf.printf "Assumptions: %s\n" (String.concat ", " (Seq.map show (RenameAssumptionSet.to_seq data.assumptions) |> List.of_seq)) in
    *)

    let (oldG, nowName, unchangedHeader), dataDequeued = dequeueFirstAssumption data in

    (*
    let _ = Printf.printf "Resolving: %s <-> %s\n" oldVarinfo.vname nowName in
    *)

    let doMatch, hasIllegalDependency, cyclicDependencyDetected, infectedAssumptions, dependencyList = match oldG with
      | Fundec oldFundec -> (
          match (StringMap.find_opt nowName nowFunctionMap) with
          | Some ((nowFundec, _)) ->
            let doMatch, _, _, function_dependencies, global_var_dependencies, renamesOnSuccess = CompareGlobals.eqF oldFundec nowFundec None VarinfoMap.empty VarinfoMap.empty in

            let basicData = dataDequeued.basicCarryData in
            let dependencySeq = getDependencies function_dependencies |> VarinfoMap.to_seq in

            let hasIllegalDependency = Seq.exists (fun (oldD, nowDName) ->
                let hasIllegalStatus name nameFunctionMap statusMap illegalStatus =
                  match (StringMap.find_opt name nameFunctionMap) with
                  | Some ((f, _)) -> (match (GlobalElemMap.find_opt (Fundec(f)) statusMap) with
                      | Some (s) ->
                        (*Printf.printf "%s has status %s\n" oldD.vname (pretty s);*)
                        s = illegalStatus
                      | None -> false)
                  | None -> true (*Illegal because it doesnt even exist*)
                in


                (*Having an entry in the function map at this point can only mean that the functions are removed/added or modified*)
                let hasEntryForOld = hasIllegalStatus oldD.vname oldFunctionMap basicData.statusForOldElem Deleted in
                let hasEntryForNow = hasIllegalStatus nowDName nowFunctionMap basicData.statusForNowElem Created in

                let assumptionAlreadyExists = RenameAssumptionSet.exists (fun (g, n, _) ->
                    match g with
                      | Fundec f -> VarinfoMap.exists (fun v a -> f.svar.vname = v.vname && n <> a.new_method_name) function_dependencies
                      | GlobalVar v -> VarinfoMap.exists (fun v2 newName -> v.vname = v2.vname && n <> newName) global_var_dependencies
                  ) data.assumptions
                in

                if assumptionAlreadyExists then Printf.printf "ASSUMPTION ALREADY EXISTS\n";

                hasEntryForOld || hasEntryForNow || assumptionAlreadyExists
              ) dependencySeq in

            let cyclicDependencyDetected, infectedAssumptions, dependencyList = if doMatch && not hasIllegalDependency then
                let dependencyList =
                  Seq.map (fun (vi, newName) ->
                      let (f, _) = StringMap.find vi.vname oldFunctionMap in
                      f, newName
                    ) dependencySeq |>
                  List.of_seq
                in

                let renameAssumptionDependencyList: renameAssumption list =
                  List.map (fun (f, newName) -> (Fundec f, newName, true)) dependencyList
                  @ (VarinfoMap.to_seq global_var_dependencies |> Seq.map (fun (v, s) -> (GlobalVar v, s, true)) |> List.of_seq)
                in

                let a, infectedAssumptions = hasCyclicDependency (oldFundec, nowName) dependencyList data in

                if a then Printf.printf "Cylic DETECTED\n";

                let actInfectedAssumptions = List.map (fun (f, nowName) -> Fundec f, nowName) infectedAssumptions in
                a, actInfectedAssumptions, renameAssumptionDependencyList
              else
                false, [], []
            in
            doMatch, hasIllegalDependency, cyclicDependencyDetected, infectedAssumptions, dependencyList
          | None -> true, false, false, [], []
        )
      | GlobalVar oV -> (
          match (StringMap.find_opt nowName nowGVarMap) with
          | Some (nV, _, _) -> (
              let (equal, (_, function_dependencies, global_var_dependencies, renamesOnSuccess)) = eq_varinfo oV nV emptyRenameMapping in
              (*eq_varinfo always comes back with a self dependency. We need to filter that out.*)

              equal, false, false, [], []
            )
          | None -> true, false, false, [], []
        )
    in

    if not doMatch || hasIllegalDependency then
      (*Functions either did not even match, or they contain a dependency we already know is wrong.*)
      propagateWrongRenameAssumption oldFunctionMap nowFunctionMap oldGVarMap nowGVarMap (oldG, nowName, unchangedHeader) dataDequeued |>
      resolveDependencies oldFunctionMap nowFunctionMap oldGVarMap nowGVarMap
    else
    if cyclicDependencyDetected then
      dequeueAssumptions infectedAssumptions dataDequeued |>
      propagateWrongRenameAssumption oldFunctionMap nowFunctionMap oldGVarMap nowGVarMap (oldG, nowName, unchangedHeader) |>
      resolveDependencies oldFunctionMap nowFunctionMap oldGVarMap nowGVarMap
    else
      dataDequeued |>
      registerDependencies dependencyList (oldG, nowName, unchangedHeader) |>
      enqueueAssumptions dependencyList |>
      resolveDependencies oldFunctionMap nowFunctionMap oldGVarMap nowGVarMap

let fillStatusForValidAssumptions oldFunctionMap nowFunctionMap oldGVarMap nowGVarMap (data: extendedCarryType) =
  RenameAssumptionSet.fold (fun (old, nowName, unchangedHeader) data ->
      let nowG = match old with
        | Fundec _ ->
          let (nF, _) = StringMap.find nowName nowFunctionMap in
          Option.some (Fundec nF)
        | GlobalVar _ ->
          if StringMap.mem nowName nowFunctionMap then
            let (nF, _, _) = StringMap.find nowName nowGVarMap in
            Option.some (GlobalVar nF)
          else None
      in

      match nowG with
        | Some nowG -> (
          if globalElemName old = nowName then
            modifyBasicCarryData (registerBiStatus old nowG (SameName(nowG))) data
          else
            modifyBasicCarryData (registerMapping old nowG) data
        )
        | None -> data
    ) data.assumptions data

let detectRenamedFunctions (oldAST: file) (newAST: file) : output GlobalElemMap.t =
  let oldFunctionMap, oldGVarMap = getFunctionAndGVarMap oldAST in
  let nowFunctionMap, nowGVarMap = getFunctionAndGVarMap newAST in

  let initialData: carryType = findSameNameMatchingGVars oldGVarMap nowGVarMap emptyCarryType in
  let initialExtendedData = {
    basicCarryData=initialData;
    assumptionQueue=empty;
    dependentsMap=RenameAssumptionMap.empty;
    assumptions=RenameAssumptionSet.empty;
  } in

  let initialBasicCarryType = findSameNameMatchingFunctions oldFunctionMap nowFunctionMap initialExtendedData (
      fun oldF nowF doMatch unchangedHeader functionDependencies global_var_dependencies renamesOnSuccess data ->
        let oldG = Fundec(oldF) in
        let nowG = Fundec(nowF) in

        if doMatch then
          let funcRenameMappings =
            VarinfoMap.to_seq functionDependencies |> List.of_seq |> List.map (fun (a, b) ->
                let (f, _) = StringMap.find a.vname oldFunctionMap in
                (Fundec f, b, true)
              )
          in

          let globVarRenameMappings =
            VarinfoMap.to_seq global_var_dependencies |> List.of_seq |>
            List.filter (fun (a, b) -> StringMap.mem a.vname oldGVarMap) |>
            List.map (fun (a, b) ->
                let (v, _, _) = StringMap.find a.vname oldGVarMap in
                (GlobalVar v, b, true)
              )
          in

          let renameMappings = funcRenameMappings @ globVarRenameMappings in

          enqueueAssumptions ((oldG, nowF.svar.vname, unchangedHeader)::renameMappings) data |>
          registerDependencies renameMappings (oldG, nowF.svar.vname, unchangedHeader)
        else
          modifyBasicCarryData (registerStatusForOldF oldG (Modified(nowG, unchangedHeader))) data |>
          modifyBasicCarryData (registerStatusForNowF nowG (Modified(oldG, unchangedHeader)))
    ) in

  (*let _ = Printf.printf "Queue size: %d\n" (length initialBasicCarryType.assumptionQueue) in*)

  (
    resolveDependencies oldFunctionMap nowFunctionMap oldGVarMap nowGVarMap initialBasicCarryType |>
    fillStatusForValidAssumptions oldFunctionMap nowFunctionMap oldGVarMap nowGVarMap
  ).basicCarryData |>
  fillStatusForUnassignedElems oldFunctionMap nowFunctionMap oldGVarMap nowGVarMap |>
  mapAnalysisResultToOutput oldFunctionMap nowFunctionMap oldGVarMap nowGVarMap
