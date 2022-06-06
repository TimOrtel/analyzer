open DetectRenamedFunctions
open Cil
include CompareAST
include CompareCFG

type renameAssumption = string * string * bool

module OrderedRenameAssumption = struct
  type t = renameAssumption

  (*x.svar.uid cannot be used, as they may overlap between old and now AST*)
  let compare (from1, to1, _) (from2, to2, _) =
    let fromCompare = String.compare from1 from2 in
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

let dequeueFirstAssumption data =
  let elem, newQueue = dequeue data.assumptionQueue in
  elem, {
  basicCarryData=data.basicCarryData;
  assumptionQueue=newQueue;
  dependentsMap=data.dependentsMap;
  assumptions=data.assumptions;
}

let removeInvalidAssumption invalidAssumption data = {
  basicCarryData=data.basicCarryData;
  assumptionQueue=data.assumptionQueue;
  dependentsMap=data.dependentsMap;
  assumptions=RenameAssumptionSet.remove invalidAssumption data.assumptions;
}

let registerDependencies (dependencies: renameAssumption list ) (dependent: renameAssumption) data =
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
  let (oldName, nowName, unchangedHeader) = wrongAssumption in

  let _ = Printf.printf "Wrong: %s <-> %s\n" oldName nowName in


  let dependents = Option.value ~default:[] (RenameAssumptionMap.find_opt wrongAssumption data.dependentsMap) in

  let (oldF, _) = StringMap.find oldName oldFunctionMap in

  (*Mark the assumption as changed or added/removed*)
  let dataWithAssumption = if oldName = nowName then
      let (nowF, _) = StringMap.find nowName nowFunctionMap in
      modifyBasicCarryData (registerChangedFunction oldF nowF unchangedHeader) data
    else
      match (StringMap.find_opt nowName nowFunctionMap) with
      | Some ((nowF, _)) -> modifyBasicCarryData (fun d ->
          registerStatusForOldF oldF Deleted d |>
          registerStatusForNowF nowF Created
        ) data
      | None -> modifyBasicCarryData (registerStatusForOldF oldF Deleted) data
  in

  let updatedData = dequeueAssumption wrongAssumption dataWithAssumption |>
                    removeInvalidAssumption wrongAssumption
  in

  (*Only propagate changes when names differ, because that means addition/removal.*)
  (*If the names are the same, a wrong assumption only means a change, if both function still exist.*)
  if oldName <> nowName || not (StringMap.mem nowName nowFunctionMap) then
    List.fold_left (fun data dependent ->
        propagateWrongRenameAssumption oldFunctionMap nowFunctionMap dependent data
      ) updatedData dependents
  else updatedData

let rec resolveDependencies (oldFunctionMap: f StringMap.t) (nowFunctionMap: f StringMap.t) (data: extendedCarryType) =
  if isEmpty data.assumptionQueue then data
  else
    let (oldName, nowName, unchangedHeader), dataDequeued = dequeueFirstAssumption data in

    let _ = Printf.printf "%s <-> %s\n" oldName nowName in

    (*There has to be an entry for oldName*)
    let (oldFundec, _) = StringMap.find oldName oldFunctionMap in
    match (StringMap.find_opt nowName nowFunctionMap) with
    | Some ((nowFundec, _)) ->
      let doMatch, unchangedHeader, _, dependencies = CompareGlobals.eqF oldFundec nowFundec None StringMap.empty in

      let basicData = dataDequeued.basicCarryData in
      let dependencySeq = getDependencies dependencies |> StringMap.to_seq in

      let hasIllegalDependency = Seq.exists (fun (oldDName, nowDName) ->
          let hasIllegalStatus name nameFunctionMap statusMap illegalStatus =
            match (StringMap.find_opt name nameFunctionMap) with
            | Some ((f, _)) -> (match (FundecMap.find_opt f statusMap) with
                | Some (s) -> s = illegalStatus
                | None -> false)
            | None -> true (*Illegal because it doesnt even exist*)
          in


          (*Having an entry in the function map at this point can only mean that the functions are removed/added or modified*)
          let hasEntryForOld = hasIllegalStatus oldDName oldFunctionMap basicData.statusForOldFunction Deleted in
          let hasEntryForNow = hasIllegalStatus nowDName nowFunctionMap basicData.statusForNowFunction Created in

          hasEntryForOld || hasEntryForNow
        ) dependencySeq
      in

      if not doMatch || hasIllegalDependency then
        let _ = Printf.printf "%s <-> %s dont match\n" oldName nowName in
        (*Functions either did not even match, or they contain a dependency we already know is wrong.*)
        propagateWrongRenameAssumption oldFunctionMap nowFunctionMap (oldName, nowName, unchangedHeader) dataDequeued |>
        resolveDependencies oldFunctionMap nowFunctionMap
      else
        let _ = Printf.printf "%s <-> %s match\n" oldName nowName in

        let dependencyList = StringMap.map (fun a -> a.original_method_name, a.new_method_name, true) dependencies |>
                             StringMap.to_seq |>
                             List.of_seq |>
                             List.map snd
        in

        dataDequeued |>
        registerDependencies dependencyList (oldName, nowName, unchangedHeader) |>
        enqueueAssumptions dependencyList |>
        resolveDependencies oldFunctionMap nowFunctionMap
    | None ->
      (*No function matching the name was found. As such this rename assumption is wrong.*)
      propagateWrongRenameAssumption oldFunctionMap nowFunctionMap (oldName, nowName, unchangedHeader) dataDequeued |>
      resolveDependencies oldFunctionMap nowFunctionMap

let fillStatusForValidAssumptions oldFunctionMap nowFunctionMap (data: extendedCarryType) =
  RenameAssumptionSet.fold (fun (oldName, nowName, unchangedHeader) data ->
      let (oF, _) = StringMap.find oldName oldFunctionMap in
      let (nF, _) = StringMap.find nowName nowFunctionMap in

      if oldName = nowName then
        modifyBasicCarryData (registerBiStatus oF nF (SameName(nF))) data
      else
        modifyBasicCarryData (registerMapping oF nF) data
    ) data.assumptions data

let detectRenamedFunctions (oldAST: file) (newAST: file) : output FundecMap.t =
  let oldFunctionMap = getFunctionMap oldAST in
  let nowFunctionMap = getFunctionMap newAST in

  let initialBasicCarryType = findSameNameMatchingFunctions oldFunctionMap nowFunctionMap emptyExtendedCarryType (
      fun oldF nowF doMatch unchangedHeader dependencies data ->
        if doMatch then
          let renameMappings = (
            StringMap.to_seq dependencies |> List.of_seq |> List.map (fun (a, b) -> (a, b, true))
            ) in

          enqueueAssumptions ((oldF.svar.vname, nowF.svar.vname, unchangedHeader)::renameMappings) data |>
          registerDependencies renameMappings (oldF.svar.vname, nowF.svar.vname, unchangedHeader)
        else
          modifyBasicCarryData (registerChangedFunction oldF nowF unchangedHeader) data
    ) in

  let _ = Printf.printf "Queue size: %d\n" (length initialBasicCarryType.assumptionQueue) in

  (resolveDependencies oldFunctionMap nowFunctionMap initialBasicCarryType |>
  fillStatusForValidAssumptions oldFunctionMap nowFunctionMap
  ).basicCarryData |>
  fillStatusForUnassignedFunctions oldFunctionMap nowFunctionMap |>
  mapAnalysisResultToOutput oldFunctionMap nowFunctionMap
