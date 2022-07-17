open DetectRenamedFunctions
open Cil
open CilMaps
include CompareAST
include CompareCFG

(*(oldVarinfo, newName, unchangedHeader, parent assumption list (used to find cyclic dependencies))*)
type renameAssumption = varinfo * string * bool * ((varinfo * string) list)

let show (renameAssumption: renameAssumption): string =
  let (v, n, _, _) = renameAssumption in
  v.vname ^ " -> " ^ n

module OrderedRenameAssumption = struct
  type t = renameAssumption

  (*x.svar.uid cannot be used, as they may overlap between old and now AST*)
  let compare (from1, to1, _, _) (from2, to2, _, _) =
    let fromCompare = String.compare from1.vname from2.vname in
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

let dequeueAssumptions (assumptions: (varinfo * string) list) data = {
  basicCarryData=data.basicCarryData;
  assumptionQueue=filterElems (fun (v, n, _, _) -> not (List.mem (v, n) assumptions)) data.assumptionQueue;
  dependentsMap=data.dependentsMap;
  assumptions=RenameAssumptionSet.filter (fun (v, n, _, _) -> not (List.mem (v, n) assumptions)) data.assumptions;
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
  let (a, b, _, _) = invalidAssumption in
  Printf.printf "Removing invalid assumption: %s -> %s\n" (a.vname) b;
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
let rec propagateWrongRenameAssumption (oldFunctionMap: f StringMap.t) (nowFunctionMap: f StringMap.t) (wrongAssumption: renameAssumption) (data: extendedCarryType) =
  let (oldVarinfo, nowName, unchangedHeader, _) = wrongAssumption in

  let dependents = Option.value ~default:[] (RenameAssumptionMap.find_opt wrongAssumption data.dependentsMap) in

  let _ = Printf.printf "Wrong: %s -> %s; dependents: %s\n" oldVarinfo.vname nowName ([%show: (string * string) list] (List.map (fun (a, b, _, _) -> a.vname, b) dependents)) in

  let (oldF, _) = StringMap.find oldVarinfo.vname oldFunctionMap in

  let oldG = Fundec(oldF) in

  let hasStatus = GlobalElemMap.mem oldG data.basicCarryData.statusForOldElem in
  if hasStatus then removeInvalidAssumption wrongAssumption data
  else (
    (*Mark the assumption as changed or added/removed*)
    let dataWithAssumption = if oldVarinfo.vname = nowName then
        let (nowF, _) = StringMap.find nowName nowFunctionMap in
        let nowG = Fundec(nowF) in
        modifyBasicCarryData (fun d ->
            registerStatusForOldF oldG (Modified(nowG, unchangedHeader)) d |>
            registerStatusForNowF nowG (Modified(oldG, unchangedHeader))
          ) data
      else
        match (StringMap.find_opt nowName nowFunctionMap) with
        | Some ((nowF, _)) -> modifyBasicCarryData (fun d ->
            let nowG = Fundec(nowF) in
            registerStatusForOldF oldG Deleted d |>
            registerStatusForNowF nowG Created
          ) data
        | None -> modifyBasicCarryData (registerStatusForOldF oldG Deleted) data
    in

    let updatedData = dequeueAssumption wrongAssumption dataWithAssumption |>
                      removeInvalidAssumption wrongAssumption
    in

    (*Get all other assumptions that rely on this varinfo*)
    let otherAssumptions = RenameAssumptionSet.filter (fun (v, _, _, _) -> v.vname = oldVarinfo.vname) updatedData.assumptions |>
                           RenameAssumptionSet.to_seq in

    (*Only propagate changes when names differ, because that means addition/removal.*)
    (*If the names are the same, a wrong assumption only means a change, if both function still exist.*)
    if oldVarinfo.vname <> nowName || not (StringMap.mem nowName nowFunctionMap) then
      Seq.fold_left (fun data dependent ->
          propagateWrongRenameAssumption oldFunctionMap nowFunctionMap dependent data
        ) updatedData (Seq.append (List.to_seq dependents) otherAssumptions)
    else
      let _ = Printf.printf "Skipping!\n" in
      updatedData
  )

let rec resolveDependencies (oldFunctionMap: f StringMap.t) (nowFunctionMap: f StringMap.t) (data: extendedCarryType) =
  if isEmpty data.assumptionQueue then data
  else
    let _ = Printf.printf "\nresolveDependencies: \n" in
    let _ = Printf.printf "Assumptions: %s\n" (String.concat ", " (Seq.map show (RenameAssumptionSet.to_seq data.assumptions) |> List.of_seq)) in

    let (oldVarinfo, nowName, unchangedHeader, parentAssumptions), dataDequeued = dequeueFirstAssumption data in

    let _ = Printf.printf "Resolving: %s <-> %s\n" oldVarinfo.vname nowName in


    (*There has to be an entry for oldName*)
    let (oldFundec, _) = StringMap.find oldVarinfo.vname oldFunctionMap in

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
                  Printf.printf "%s has status %s\n" oldD.vname (pretty s);
                  s = illegalStatus
                | None -> false)
            | None -> true (*Illegal because it doesnt even exist*)
          in


          (*Having an entry in the function map at this point can only mean that the functions are removed/added or modified*)
          let hasEntryForOld = hasIllegalStatus oldD.vname oldFunctionMap basicData.statusForOldElem Deleted in
          let hasEntryForNow = hasIllegalStatus nowDName nowFunctionMap basicData.statusForNowElem Created in

          hasEntryForOld || hasEntryForNow
        ) dependencySeq
      in

      if not doMatch || hasIllegalDependency then
        let _ = Printf.printf "not match or illegal dependency: %s -> %s; matches=%b, illegalDep=%b\n" oldVarinfo.vname nowName doMatch hasIllegalDependency in
        (*Functions either did not even match, or they contain a dependency we already know is wrong.*)
        propagateWrongRenameAssumption oldFunctionMap nowFunctionMap (oldVarinfo, nowName, unchangedHeader, parentAssumptions) dataDequeued |>
        resolveDependencies oldFunctionMap nowFunctionMap
      else
        let _ = Printf.printf "%s <-> %s match\n" oldVarinfo.vname nowName in

        let dependencyList = Seq.map (fun (vi, newName) -> vi, newName, true, (oldVarinfo, nowName)::parentAssumptions) dependencySeq |>
                             List.of_seq
        in

        let cyclicDependencyDetected = List.exists (fun (v, newName) ->
            List.exists (fun (v2, newName2, _, _) -> v.vname = v2.vname && newName = newName2) dependencyList)
            parentAssumptions
        in

        if cyclicDependencyDetected then
          let _ = Printf.printf "Cyclic dependency detected: %s \n" (
              [%show: (string * string) list] (List.map (fun (v, n) -> v.vname, n) ((oldVarinfo, nowName)::parentAssumptions))) in

          dequeueAssumptions parentAssumptions dataDequeued |>
          propagateWrongRenameAssumption oldFunctionMap nowFunctionMap (oldVarinfo, nowName, unchangedHeader, parentAssumptions) |>
          resolveDependencies oldFunctionMap nowFunctionMap
        else
          dataDequeued |>
          registerDependencies dependencyList (oldVarinfo, nowName, unchangedHeader, parentAssumptions) |>
          enqueueAssumptions dependencyList |>
          resolveDependencies oldFunctionMap nowFunctionMap
    | None ->
      (*No function matching the name was found. As such this rename assumption is wrong.*)
      propagateWrongRenameAssumption oldFunctionMap nowFunctionMap (oldVarinfo, nowName, unchangedHeader, parentAssumptions) dataDequeued |>
      resolveDependencies oldFunctionMap nowFunctionMap

let fillStatusForValidAssumptions oldFunctionMap nowFunctionMap (data: extendedCarryType) =
  RenameAssumptionSet.fold (fun (old, nowName, unchangedHeader, parentAssumptions) data ->
      let (oF, _) = StringMap.find old.vname oldFunctionMap in
      let (nF, _) = StringMap.find nowName nowFunctionMap in

      let oldG, nowG = Fundec(oF), Fundec(nF) in

      if old.vname = nowName then
        modifyBasicCarryData (registerBiStatus oldG nowG (SameName(nowG))) data
      else
        modifyBasicCarryData (registerMapping oldG nowG) data
    ) data.assumptions data

let detectRenamedFunctions (oldAST: file) (newAST: file) : output GlobalElemMap.t =
  let oldFunctionMap, oldGVarMap = getFunctionAndGVarMap oldAST in
  let nowFunctionMap, nowGVarMap = getFunctionAndGVarMap newAST in

  let initialBasicCarryType = findSameNameMatchingFunctions oldFunctionMap nowFunctionMap emptyExtendedCarryType (
      fun oldF nowF doMatch unchangedHeader functionDependencies global_var_dependencies renamesOnSuccess data ->
        let oldG = Fundec(oldF) in
        let nowG = Fundec(nowF) in

        if doMatch then
          let renameMappings = (
            VarinfoMap.to_seq functionDependencies |> List.of_seq |> List.map (fun (a, b) -> (a, b, true, [oldF.svar, nowF.svar.vname]))
          ) in

          enqueueAssumptions ((oldF.svar, nowF.svar.vname, unchangedHeader, [])::renameMappings) data |>
          registerDependencies renameMappings (oldF.svar, nowF.svar.vname, unchangedHeader, [])
        else
          modifyBasicCarryData (registerStatusForOldF oldG (Modified(nowG, unchangedHeader))) data |>
          modifyBasicCarryData (registerStatusForNowF nowG (Modified(oldG, unchangedHeader)))
    ) in

  let _ = Printf.printf "Queue size: %d\n" (length initialBasicCarryType.assumptionQueue) in

  (
    resolveDependencies oldFunctionMap nowFunctionMap initialBasicCarryType |>
    fillStatusForValidAssumptions oldFunctionMap nowFunctionMap
  ).basicCarryData |>
  fillStatusForUnassignedElems oldFunctionMap nowFunctionMap oldGVarMap nowGVarMap |>
  mapAnalysisResultToOutput oldFunctionMap nowFunctionMap oldGVarMap nowGVarMap
